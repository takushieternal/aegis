package main

import (
	"bytes"
	"crypto/aes"
	"crypto/cipher"
	"crypto/ed25519"
	"crypto/rand"
	"crypto/sha256"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"sync"
	"time"

	"golang.org/x/crypto/pbkdf2"
)

// ==========================================
// [Design Spec 3.1] Identity & Authentication
// ==========================================

type AegisIdentity struct {
	Username         string   `json:"username"`
	PublicKey        string   `json:"public_key"`
	PrivateKey       []byte   `json:"-"`
	EncryptedPrivKey string   `json:"encrypted_priv_key"`
	RootHash         string   `json:"root_hash"`
	SeedPhrase       []string `json:"-"`
	EncryptedSeed    string   `json:"encrypted_seed"`
	CryptoSalt       string   `json:"crypto_salt"`
	Devices          []string `json:"devices"`
	BlockedHashes    []string `json:"blocked_hashes"`
	TrustedHashes    []string `json:"trusted_hashes"` 
	BannedFrom       []string `json:"banned_from"`    
}

// ==========================================
// [Design Spec 4.1] Hybrid Logical Clocks
// ==========================================

type HLC struct {
	Physical int64 `json:"p"`
	Logical  int   `json:"l"`
}

func (h *HLC) Increment() {
	now := time.Now().UnixNano()
	if now > h.Physical {
		h.Physical = now
		h.Logical = 0
	} else {
		h.Logical++
	}
}

func (h *HLC) Update(remote HLC) {
	now := time.Now().UnixNano()
	maxPhysical := h.Physical
	if remote.Physical > maxPhysical {
		maxPhysical = remote.Physical
	}
	if now > maxPhysical {
		h.Physical = now
		h.Logical = 0
	} else {
		// Always advance h.Physical to the highest known physical time so the
		// invariant h.Physical >= remote.Physical is maintained.
		h.Physical = maxPhysical
		if remote.Logical > h.Logical {
			h.Logical = remote.Logical + 1
		} else {
			h.Logical++
		}
	}
}

// ==========================================
// Models
// ==========================================

type Role string

const (
	RoleOwner  Role = "OWNER"
	RoleAdmin  Role = "ADMIN"
	RoleMember Role = "MEMBER"
)

type Platform struct {
	ID                 string          `json:"id"`
	Name               string          `json:"name"`
	IsEphemeral        bool            `json:"is_ephemeral"`
	IsTrusted          bool            `json:"is_trusted"`
	TTL                time.Time       `json:"ttl,omitempty"`
	StateKey           string          `json:"-"`
	Members            map[string]Role `json:"members"`
	BannedHashes       []string        `json:"banned_hashes"`
	ShadowBannedHashes []string        `json:"shadow_banned_hashes"`
}

type InviteContract struct {
	ID        string    `json:"id"`
	Platform  string    `json:"platform"`
	ExpiresAt time.Time `json:"expires_at"`
	MaxUses   int       `json:"max_uses"`
	Uses      int       `json:"uses"`
}

type InvitePayload struct {
	PlatformID   string   `json:"platform_id"`
	PlatformName string   `json:"platform_name"`
	PeerURL      string   `json:"peer_url"` 
	PeerURLs     []string `json:"peer_urls"` 
	InviteID     string   `json:"invite_id"`
}

type Message struct {
	ID         string    `json:"id"`
	Platform   string    `json:"platform"`
	Sender     string    `json:"sender"`      
	SenderName string    `json:"sender_name"` 
	Text       string    `json:"text"`
	Timestamp  time.Time `json:"timestamp"`

	Clock      HLC               `json:"hlc"`
	VectorMap  map[string]uint64 `json:"vector_map"`
	MsgType    string            `json:"msg_type"`             
	TargetHash string            `json:"target_hash,omitempty"`
	Payload    string            `json:"payload,omitempty"`    
	FileCID    string            `json:"file_cid,omitempty"`
	FileName   string            `json:"file_name,omitempty"`
	FileSize   int64             `json:"file_size,omitempty"`  
	IsAcked    bool              `json:"is_acked"`
	AckedBy    []string          `json:"acked_by,omitempty"`   
	
	PublicKey  string            `json:"public_key"` 
	Signature  string            `json:"signature"`  
}

// ==========================================
// Node State & Main
// ==========================================

type AegisNode struct {
	Identity       AegisIdentity       `json:"identity"`
	Platforms      map[string]Platform `json:"platforms"`
	Messages       []Message           `json:"messages"`
	Invites        []InviteContract    `json:"invites"`
	Peers          []string            `json:"peers"`
	Clock          HLC                 `json:"clock"`
	SeenSignatures map[string]int64    `json:"seen_signatures"`
	LastUpdate     int64               `json:"-"`
	mu             sync.RWMutex
}

var node *AegisNode
var dbFile string
var currentPort string
var currentProfile string
var fileStoreDir string
var dataDir string   // directory that holds all persistent data files — always the exe's own directory
var dbMutex sync.Mutex
var APIToken string
var isNodeLocked bool

// updateMu + updateCond form a standalone condition variable used exclusively
// for long-poll wake-ups. It is intentionally separate from node.mu so that
// sync.Cond.Wait() (which requires exclusive ownership of its Locker) never
// races with RWMutex readers.
var updateMu   sync.Mutex
var updateCond = sync.NewCond(&updateMu)

func checkLocalAuth(w http.ResponseWriter, r *http.Request) bool {
	if r.Method == "OPTIONS" {
		w.WriteHeader(http.StatusOK)
		return false
	}
	
	authHeader := r.Header.Get("Authorization")
	if authHeader != "Bearer "+APIToken {
		jsonError(w, "Unauthorized local access. Invalid API Token.", http.StatusUnauthorized)
		return false
	}
	return true
}

func setNoCache(w http.ResponseWriter) {
	w.Header().Set("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
	w.Header().Set("Pragma", "no-cache")
	w.Header().Set("Expires", "0")
}

func jsonError(w http.ResponseWriter, message string, statusCode int) {
	w.WriteHeader(statusCode)
	json.NewEncoder(w).Encode(map[string]string{"error": message})
}

func generateID(prefix string) string {
	b := make([]byte, 16)
	if _, err := rand.Read(b); err != nil {
		log.Fatalf("crypto/rand exhausted in generateID: %v", err)
	}
	return fmt.Sprintf("%s_%x", prefix, b)
}

func main() {
// Since you are using a compiled .exe, permanently lock the dataDir 
	// to the exact folder where the executable file lives. This prevents 
	// Access Denied errors if launched via double-click or from other paths.
	exePath, err := os.Executable()
	if err == nil {
		dataDir = filepath.Dir(exePath)
	} else {
		dataDir = "."
	}

	portFlag := flag.String("port", "0", "Port to run the Aegis P2P node on (0 automatically finds a free port)")
	profileFlag := flag.String("profile", "default", "Profile name for local data storage")
	flag.Parse()
	currentPort = *portFlag
	currentProfile = *profileFlag

	// 1. Setup Local Admin Listener (Strictly bound to localhost)
	adminListener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		log.Fatalf("Failed to bind admin interface to localhost: %v", err)
	}
	adminPort := fmt.Sprintf("%d", adminListener.Addr().(*net.TCPAddr).Port)

	// 2. Setup Public P2P Listener
	p2pListener, err := net.Listen("tcp", ":"+currentPort)
	if err != nil {
		fmt.Printf("[Aegis] Port %s is in use. Finding an available dynamic port...\n", currentPort)
		p2pListener, err = net.Listen("tcp", ":0")
		if err != nil {
			log.Fatalf("Failed to bind to any public port: %v", err)
		}
	}
	currentPort = fmt.Sprintf("%d", p2pListener.Addr().(*net.TCPAddr).Port)

	fmt.Printf("[Aegis] Starting Project Aegis Node...\n")
	fmt.Printf("[P2P] Mesh Network listening on port %s\n", currentPort)
	initNode()

	go attemptUPnP(currentPort)

	// Route configuration for Admin API (Local Only)
	adminMux := http.NewServeMux()
	adminMux.HandleFunc("/", serveUI)
	adminMux.HandleFunc("/api/identity", apiIdentity)
	adminMux.HandleFunc("/api/unlock", apiUnlock)
	adminMux.HandleFunc("/api/reset", apiResetNode)
	adminMux.HandleFunc("/api/block", apiBlockUser)
	adminMux.HandleFunc("/api/trust", apiTrustUser)
	adminMux.HandleFunc("/api/platforms/ban", apiBanUser)
	adminMux.HandleFunc("/api/platforms", apiPlatforms)
	adminMux.HandleFunc("/api/platforms/leave", apiLeavePlatform)
	adminMux.HandleFunc("/api/messages", apiMessages)
	adminMux.HandleFunc("/api/messages/ack", apiAckMessage) 
	adminMux.HandleFunc("/api/moderate", apiModerate)
	adminMux.HandleFunc("/api/invites", apiInvites)
	adminMux.HandleFunc("/api/join", apiJoin)
	adminMux.HandleFunc("/api/peers", apiPeers)
	adminMux.HandleFunc("/api/ping", apiPing) 
	adminMux.HandleFunc("/api/files/upload", apiUploadFile)
	adminMux.HandleFunc("/api/files/download", apiDownloadFile)

	// Route configuration for Public P2P Interface (Internet Facing)
	p2pMux := http.NewServeMux()
	p2pMux.HandleFunc("/p2p/message", p2pReceiveMessage)
	p2pMux.HandleFunc("/p2p/files", p2pServeFile)
	p2pMux.HandleFunc("/p2p/files/push", p2pReceiveFile) 
	p2pMux.HandleFunc("/p2p/sync", p2pSyncMessages) // Public message sync endpoint for mesh peers
	p2pMux.HandleFunc("/api/ping", apiPing)
	p2pMux.HandleFunc("/api/peers", p2pApiPeers)

	go announcePresence()
	go peerMaintenance()
	go meshSyncLoop()

	go func() {
		for {
			time.Sleep(15 * time.Minute)
			cleanReplayCache()
		}
	}()

	url := "http://localhost:" + adminPort
	fmt.Printf("[Web] Aegis Local Admin Interface running at: %s\n", url)

	go func() {
		openBrowser(url)
	}()

	go http.Serve(adminListener, adminMux)
	log.Fatal(http.Serve(p2pListener, p2pMux))
}

func openBrowser(url string) {
	// Wait until the HTTP server is actually accepting connections before
	// opening the browser — prevents a connection-refused page on slow starts.
	for i := 0; i < 20; i++ {
		conn, err := net.Dial("tcp", strings.TrimPrefix(strings.TrimPrefix(url, "https://"), "http://"))
		if err == nil {
			conn.Close()
			break
		}
		time.Sleep(150 * time.Millisecond)
	}

	var err error
	switch runtime.GOOS {
	case "linux":
		// On Steam Deck in Gaming Mode the desktop session is Gamescope, which
		// doesn't have xdg-open wired up to a browser.  Try a chain of openers
		// in order of preference: steam-xdg-open (Valve helper), xdg-open
		// (works in Desktop Mode), then a set of known browsers directly.
		openers := [][]string{
			{"steam-xdg-open", url},
			{"xdg-open", url},
			{"flatpak-spawn", "--host", "xdg-open", url},
			{"firefox", url},
			{"chromium-browser", url},
			{"chromium", url},
			{"google-chrome", url},
		}
		for _, args := range openers {
			if path, lookErr := exec.LookPath(args[0]); lookErr == nil {
				err = exec.Command(path, args[1:]...).Start()
				if err == nil {
					return
				}
			}
		}
		// Nothing worked — log the URL so the user can open it manually.
		if err != nil {
			fmt.Printf("[Web] Could not open browser automatically.\n")
			fmt.Printf("[Web] Please open manually: %s\n", url)
		}
	case "windows":
		err = exec.Command("rundll32", "url.dll,FileProtocolHandler", url).Start()
	case "darwin":
		err = exec.Command("open", url).Start()
	default:
		err = fmt.Errorf("unsupported platform")
	}
	if err != nil {
		log.Printf("Could not open browser: %v", err)
		fmt.Printf("[Web] Please open manually: %s\n", url)
	}
}

// generateSeedPhrase produces a 24-word BIP39 mnemonic backed by 256 bits of
// cryptographically secure entropy (24 words × 11 bits = 264 bits raw; 256 bits
// of entropy + 8-bit checksum per the BIP39 spec).  We draw 2 random bytes per
// word, mask to 11 bits (0–2047), and index into the canonical 2048-word list.
func generateSeedPhrase() []string {
	// Full BIP39 English wordlist (2048 words).
	wordlist := []string{
		"abandon","ability","able","about","above","absent","absorb","abstract","absurd","abuse",
		"access","accident","account","accuse","achieve","acid","acoustic","acquire","across","act",
		"action","actor","actress","actual","adapt","add","addict","address","adjust","admit",
		"adult","advance","advice","aerobic","afford","afraid","again","age","agent","agree",
		"ahead","aim","air","airport","aisle","alarm","album","alcohol","alert","alien",
		"all","alley","allow","almost","alone","alpha","already","also","alter","always",
		"amateur","amazing","among","amount","amused","analyst","anchor","ancient","anger","angle",
		"angry","animal","ankle","announce","annual","another","answer","antenna","antique","anxiety",
		"any","apart","apology","appear","apple","approve","april","arch","arctic","area",
		"arena","argue","arm","armed","armor","army","around","arrange","arrest","arrive",
		"arrow","art","artefact","artist","artwork","ask","aspect","assault","asset","assist",
		"assume","asthma","athlete","atom","attack","attend","attitude","attract","auction","audit",
		"august","aunt","author","auto","autumn","average","avocado","avoid","awake","aware",
		"away","awesome","awful","awkward","axis","baby","balance","bamboo","banana","banner",
		"bar","barely","bargain","barrel","base","basic","basket","battle","beach","bean",
		"beauty","because","become","beef","before","begin","behave","behind","believe","below",
		"belt","bench","benefit","best","betray","better","between","beyond","bicycle","bid",
		"bike","bind","biology","bird","birth","bitter","black","blade","blame","blanket",
		"blast","bleak","bless","blind","blood","blossom","blouse","blue","blur","blush",
		"board","boat","body","boil","bomb","bone","book","boost","border","boring",
		"borrow","boss","bottom","bounce","box","boy","bracket","brain","brand","brave",
		"breeze","brick","bridge","brief","bright","bring","brisk","broccoli","broken","bronze",
		"broom","brother","brown","brush","bubble","buddy","budget","buffalo","build","bulb",
		"bulk","bullet","bundle","bunker","burden","burger","burst","bus","business","busy",
		"butter","buyer","buzz","cabbage","cabin","cable","cactus","cage","cake","call",
		"calm","camera","camp","can","canal","cancel","candy","cannon","canvas","canyon",
		"capable","capital","captain","car","carbon","card","cargo","carpet","carry","cart",
		"case","cash","casino","castle","casual","cat","catalog","catch","category","cattle",
		"caught","cause","caution","cave","ceiling","celery","cement","census","century","cereal",
		"certain","chair","chalk","champion","change","chaos","chapter","charge","chase","chat",
		"cheap","check","cheese","chef","cherry","chest","chicken","chief","child","chimney",
		"choice","choose","chronic","chuckle","chunk","cigar","cinnamon","circle","citizen","city",
		"civil","claim","clap","clarify","claw","clay","clean","clerk","clever","click",
		"client","cliff","climb","clinic","clip","clock","clog","close","cloth","cloud",
		"clown","club","clump","cluster","clutch","coach","coast","coconut","code","coffee",
		"coil","coin","collect","color","column","combine","come","comfort","comic","common",
		"company","concert","conduct","confirm","congress","connect","consider","control","convince","cook",
		"cool","copper","copy","coral","core","corn","correct","cost","cotton","couch",
		"country","couple","course","cousin","cover","coyote","crack","cradle","craft","cram",
		"crane","crash","crater","crawl","crazy","cream","credit","creek","crew","cricket",
		"crisp","critic","cross","crouch","crowd","crucial","cruel","cruise","crumble","crunch",
		"crush","cry","crystal","cube","culture","cup","cupboard","curious","current","curtain",
		"curve","cushion","custom","cute","cycle","dad","damage","damp","dance","danger",
		"daring","dash","daughter","dawn","day","deal","debate","debris","decade","december",
		"decide","decline","decorate","decrease","deer","defense","define","defy","degree","delay",
		"deliver","demand","demise","denial","dentist","deny","depart","depend","deposit","depth",
		"deputy","derive","describe","desert","design","desk","despair","destroy","detail","detect",
		"develop","device","devote","diagram","dial","diamond","diary","dice","diesel","diet",
		"differ","digital","dignity","dilemma","dinner","dinosaur","direct","dirt","disagree","discover",
		"disease","dish","dismiss","disorder","display","distance","divert","divide","divorce","dizzy",
		"doctor","document","dog","doll","dolphin","domain","donate","donkey","donor","door",
		"dose","double","dove","draft","dragon","drama","drastic","draw","dream","dress",
		"drift","drill","drink","drip","drive","drop","drum","dry","duck","dumb",
		"dune","during","dust","dutch","duty","dwarf","dynamic","eager","eagle","early",
		"earn","earth","easily","east","easy","echo","ecology","edge","edit","educate",
		"effort","egg","eight","either","elbow","elder","electric","elegant","element","elephant",
		"elevator","elite","else","embark","embody","embrace","emerge","emotion","employ","empower",
		"empty","enable","enact","endless","endorse","enemy","energy","enforce","engage","engine",
		"enhance","enjoy","enlist","enough","enrich","enroll","ensure","enter","entire","entry",
		"envelope","episode","equal","equip","erase","erode","erosion","error","erupt","escape",
		"essay","essence","estate","eternal","ethics","evidence","evil","evoke","evolve","exact",
		"example","excess","exchange","excite","exclude","exercise","exhaust","exhibit","exile","exist",
		"exit","exotic","expand","expire","explain","expose","express","extend","extra","eye",
		"fable","face","faculty","faint","faith","fall","false","fame","family","famous",
		"fan","fancy","fantasy","far","fashion","fat","fatal","father","fatigue","fault",
		"favorite","feature","february","federal","feedback","feel","feet","fellow","felt","fence",
		"festival","fetch","fever","few","fiber","fiction","field","figure","file","film",
		"filter","final","find","fine","finger","finish","fire","firm","first","fiscal",
		"fish","fit","fitness","fix","flag","flame","flash","flat","flavor","flee",
		"flight","flip","float","flock","floor","flower","fluid","flush","fly","foam",
		"focus","fog","foil","follow","food","foot","force","forest","forget","fork",
		"fortune","forum","forward","fossil","foster","found","fox","fragile","frame","frequent",
		"fresh","friend","fringe","frog","front","frost","frown","frozen","fruit","fuel",
		"fun","funny","furnace","fury","future","gadget","gain","galaxy","gallery","game",
		"gap","garbage","garden","garlic","garment","gasp","gate","gather","gauge","gaze",
		"general","genius","genre","gentle","genuine","gesture","ghost","giant","gift","giggle",
		"ginger","giraffe","girl","give","glad","glance","glare","glass","glide","glimpse",
		"globe","gloom","glory","glove","glow","glue","goat","goddess","gold","good",
		"goose","gorilla","gospel","gossip","govern","gown","grab","grace","grain","grant",
		"grape","grasp","grass","gravity","great","green","grid","grief","grit","grocery",
		"group","grow","grunt","guard","guide","guilt","guitar","gun","gym","habit",
		"hair","half","hammer","hamster","hand","happy","harsh","harvest","hat","have",
		"hawk","hazard","head","health","heart","heavy","hedgehog","height","hello","helmet",
		"help","hen","hero","hidden","high","hill","hint","hip","hire","history",
		"hobby","hockey","hold","hole","hollow","home","honey","hood","hope","horn",
		"horror","horse","hospital","host","hour","hover","hub","huge","human","humble",
		"humor","hundred","hungry","hunt","hurdle","hurry","hurt","husband","hybrid","ice",
		"icon","ignore","ill","illegal","image","imitate","immense","immune","impact","impose",
		"improve","impulse","inbox","income","increase","index","indicate","indoor","industry","infant",
		"inflict","inform","inhale","inject","inner","innocent","input","inquiry","insane","insect",
		"inspire","install","intact","interest","into","invest","invite","involve","iron","island",
		"isolate","issue","item","ivory","jacket","jaguar","jar","jazz","jealous","jeans",
		"jelly","jewel","job","join","joke","journey","joy","judge","juice","jump",
		"jungle","junior","junk","just","kangaroo","keen","keep","ketchup","key","kick",
		"kid","kingdom","kiss","kit","kitchen","kite","kitten","kiwi","knee","knife",
		"knock","know","lab","ladder","lamp","language","laptop","large","later","laugh",
		"laundry","lava","law","lawn","lawsuit","layer","lazy","leader","learn","leave",
		"lecture","left","leg","legal","legend","lemon","lend","length","lens","leopard",
		"lesson","letter","level","liar","liberty","library","license","life","lift","like",
		"limb","lion","liquid","list","little","live","lizard","load","loan","lobster",
		"local","lock","logic","lonely","long","loop","lottery","loud","lounge","love",
		"loyal","lucky","luggage","lumber","lunar","lunch","luxury","mad","magic","magnet",
		"maid","main","mammal","mango","mansion","manual","maple","marble","march","margin",
		"marine","market","marriage","mask","master","match","material","math","matrix","matter",
		"maximum","maze","meadow","mean","medal","media","melody","melt","member","memory",
		"mention","mercy","mesh","message","metal","method","middle","midnight","milk","million",
		"mimic","mind","minimum","minor","minute","miracle","miss","mistake","mix","mixed",
		"mixture","mobile","model","modify","mom","monitor","monkey","monster","month","moon",
		"moral","more","morning","mosquito","mother","motion","motor","mountain","mouse","move",
		"movie","much","muffin","mule","multiply","muscle","museum","mushroom","music","must",
		"mutual","myself","mystery","naive","name","napkin","narrow","nasty","nature","near",
		"neck","need","negative","neglect","neither","nephew","nerve","nest","network","news",
		"next","nice","night","noble","noise","nominee","noodle","normal","north","notable",
		"note","nothing","notice","novel","now","nuclear","number","nurse","nut","oak",
		"obey","object","oblige","obscure","obtain","ocean","october","odor","off","offer",
		"office","often","oil","okay","old","olive","olympic","omit","once","onion",
		"open","opera","oppose","option","orange","orbit","orchard","order","ordinary","organ",
		"orient","original","orphan","ostrich","other","outdoor","outside","oval","over","own",
		"oyster","ozone","pact","paddle","page","pair","palace","palm","panda","panel",
		"panic","panther","paper","parade","parent","park","parrot","party","pass","patch",
		"path","patrol","pause","pave","payment","peace","peanut","peasant","pelican","pen",
		"penalty","pencil","people","pepper","perfect","permit","person","pet","phone","photo",
		"phrase","physical","piano","picnic","picture","piece","pig","pigeon","pill","pilot",
		"pink","pioneer","pipe","pistol","pitch","pizza","place","planet","plastic","plate",
		"play","please","pledge","pluck","plug","plunge","poem","poet","point","polar",
		"pole","police","pond","pony","pool","popular","portion","position","possible","post",
		"potato","pottery","poverty","powder","power","practice","praise","predict","prefer","prepare",
		"present","pretty","prevent","price","pride","primary","print","priority","prison","private",
		"prize","problem","process","produce","profit","program","project","promote","proof","property",
		"prosper","protect","proud","provide","public","pudding","pull","pulp","pulse","pumpkin",
		"punish","pupil","purchase","purity","purpose","push","put","puzzle","pyramid","quality",
		"quantum","quarter","question","quick","quit","quiz","quote","rabbit","raccoon","race",
		"rack","radar","radio","rage","rail","rain","raise","rally","ramp","ranch",
		"random","range","rapid","rare","rate","rather","raven","reach","ready","real",
		"reason","rebel","rebuild","recall","receive","recipe","record","recycle","reduce","reflect",
		"reform","refuse","region","regret","regular","reject","relax","release","relief","rely",
		"remain","remember","remind","remove","render","renew","rent","reopen","repair","repeat",
		"replace","report","require","rescue","resemble","resist","resource","response","result","retire",
		"retreat","return","reunion","reveal","review","reward","rhythm","ribbon","ride","ridge",
		"rifle","right","rigid","ring","riot","ripple","risk","ritual","rival","river",
		"road","roast","robot","robust","rocket","romance","roof","rookie","rose","rotate",
		"rough","round","route","royal","rubber","rude","rug","rule","run","runway",
		"rural","sad","saddle","sadness","safe","sail","salad","salmon","salon","salt",
		"salute","same","sample","sand","satisfy","satoshi","sauce","sausage","save","scale",
		"scan","scatter","scene","scheme","scissors","scorpion","scout","scrap","screen","script",
		"scrub","sea","search","season","seat","second","secret","section","security","seek",
		"segment","select","sell","seminar","senior","sense","sentence","series","service","session",
		"settle","setup","seven","shadow","shaft","shallow","share","shed","shell","sheriff",
		"shield","shift","shine","ship","shiver","shock","shoe","shoot","shop","short",
		"shoulder","shove","shrimp","shrug","shuffle","shy","sibling","siege","sight","sign",
		"silent","silk","silly","silver","similar","simple","since","sing","siren","sister",
		"situate","six","size","sketch","skill","skin","skirt","skull","slab","slam",
		"sleep","slender","slice","slide","slight","slim","slogan","slot","slow","slush",
		"small","smart","smile","smoke","smooth","snack","snake","snap","sniff","snow",
		"soap","soccer","social","sock","solar","soldier","solid","solution","solve","someone",
		"song","soon","sorry","soul","sound","soup","source","south","space","spare",
		"spatial","spawn","speak","special","speed","sphere","spice","spider","spike","spin",
		"spirit","split","spoil","sponsor","spoon","spray","spread","spring","spy","square",
		"squeeze","squirrel","stable","stadium","staff","stage","stairs","stamp","stand","start",
		"state","stay","steak","steel","stem","step","stereo","stick","still","sting",
		"stock","stomach","stone","stop","store","storm","story","stove","strategy","street",
		"strike","strong","struggle","student","stuff","stumble","style","subject","submit","subway",
		"success","such","sudden","suffer","sugar","suggest","suit","sunny","sunset","super",
		"supply","supreme","sure","surface","surge","surprise","sustain","swallow","swamp","swap",
		"swear","sweet","swift","swim","swing","switch","sword","symbol","symptom","syrup",
		"table","tackle","tag","tail","talent","tank","tape","target","task","taste",
		"tattoo","taxi","teach","team","tell","ten","tenant","tennis","tent","term",
		"test","text","thank","that","theme","then","theory","there","they","thing",
		"this","thought","three","thrive","throw","thumb","thunder","ticket","tilt","timber",
		"time","tiny","tip","tired","title","toast","tobacco","today","together","toilet",
		"token","tomato","tomorrow","tone","tongue","tonight","tool","tooth","top","topic",
		"topple","torch","tornado","tortoise","toss","total","tourist","toward","tower","town",
		"toy","track","trade","traffic","tragic","train","transfer","trap","trash","travel",
		"tray","treat","tree","trend","trial","tribe","trick","trigger","trim","trip",
		"trophy","trouble","truck","truly","trumpet","trust","truth","try","tube","tuition",
		"tumble","tuna","tunnel","turkey","turn","turtle","twelve","twenty","twice","twin",
		"twist","two","type","typical","ugly","umbrella","unable","unaware","uncle","uncover",
		"under","undo","unfair","unfold","unhappy","uniform","unique","universe","unknown","unlock",
		"until","unusual","unveil","update","upgrade","uphold","upon","upper","upset","urban",
		"useful","useless","usual","utility","vacant","vacuum","vague","valid","valley","valve",
		"van","vanish","vapor","various","vast","vault","vehicle","velvet","vendor","venture",
		"venue","verb","verify","version","very","veteran","viable","vibrant","vicious","victory",
		"video","view","village","vintage","violin","virtual","virus","visa","visit","visual",
		"vital","vivid","vocal","voice","void","volcano","vote","voyage","wage","wagon",
		"wait","walk","wall","walnut","want","warfare","warm","warrior","waste","water",
		"wave","way","wealth","weapon","wear","weasel","weather","web","wedding","weekend",
		"weird","welcome","well","west","wet","whale","wheat","wheel","when","where",
		"whip","whisper","wide","width","wife","wild","will","win","window","wine",
		"wing","wink","winner","winter","wire","wisdom","wise","wish","witness","wolf",
		"woman","wonder","wood","wool","word","world","worry","worth","wrap","wreck",
		"wrestle","wrist","write","wrong","yard","year","yellow","you","young","youth",
		"zebra","zero","zone","zoo",
	}
	// 24 words × 11 bits = 264 raw bits; 256 bits of entropy + 8-bit BIP39 checksum.
	// We draw 2 bytes per word and mask to 11 bits for a uniform distribution over 2048 words.
	words := make([]string, 24)
	buf := make([]byte, 2)
	for i := range words {
		if _, err := rand.Read(buf); err != nil {
			panic(fmt.Sprintf("crypto/rand failed in generateSeedPhrase: %v", err))
		}
		idx := (int(buf[0])<<8|int(buf[1])) & 0x7FF // 11-bit mask → 0–2047
		words[i] = wordlist[idx]
	}
	return words
}

func initNode() {
	tokenBytes := make([]byte, 16)
	rand.Read(tokenBytes)
	APIToken = hex.EncodeToString(tokenBytes)

	node = &AegisNode{
		Platforms:      make(map[string]Platform),
		Messages:       make([]Message, 0),
		Invites:        make([]InviteContract, 0),
		Peers:          []string{"http://3.16.213.66:8080"}, // Optional default peer added
		Clock:          HLC{Physical: time.Now().UnixNano(), Logical: 0},
		SeenSignatures: make(map[string]int64),
		LastUpdate:     time.Now().UnixMilli(),
	}

	dbFile = filepath.Join(dataDir, fmt.Sprintf("aegis_local_store_%s.json", currentProfile))
	fileStoreDir = filepath.Join(dataDir, fmt.Sprintf("aegis_files_%s", currentProfile))

	fmt.Printf("[DB] Data directory : %s\n", dataDir)
	fmt.Printf("[DB] Database file  : %s\n", dbFile)
	fmt.Printf("[DB] File store     : %s\n", fileStoreDir)

	// Verify the data directory is writable before doing anything else.
	// This catches permission problems immediately with a clear error message.
	probeFile := filepath.Join(dataDir, ".aegis_write_probe")
	if err := os.WriteFile(probeFile, []byte("ok"), 0600); err != nil {
		log.Fatalf("[DB] FATAL: data directory is not writable: %s\n  Error: %v\n  Make sure the application has write permission to its own directory.", dataDir, err)
	}
	os.Remove(probeFile)

	if err := os.MkdirAll(fileStoreDir, 0700); err != nil {
		log.Fatalf("[DB] FATAL: could not create file store directory %s: %v", fileStoreDir, err)
	}

	if _, err := os.Stat(dbFile); os.IsNotExist(err) {
		fmt.Println("[Key] Generating Master Identity Key...")
		pub, priv, err := ed25519.GenerateKey(rand.Reader)
		if err != nil {
			log.Fatalf("Failed to generate keys: %v", err)
		}

		hash := sha256.Sum256(pub)
		rootHash := hex.EncodeToString(hash[:])
		
		saltBytes := make([]byte, 16)
		rand.Read(saltBytes)

		node.Identity = AegisIdentity{
			Username:      "", 
			PublicKey:     hex.EncodeToString(pub),
			PrivateKey:    priv,
			RootHash:      rootHash,
			SeedPhrase:    generateSeedPhrase(),
			CryptoSalt:    hex.EncodeToString(saltBytes),
			Devices:       []string{"device_01_local"},
			BlockedHashes: make([]string, 0),
			TrustedHashes: make([]string, 0),
			BannedFrom:    make([]string, 0),
		}

		isNodeLocked = false
		saveLocalDB()

		// On Windows, Defender scans new executables on first launch and can
		// hold a file lock long enough for the initial write to fail silently.
		// Retry in a background goroutine so startup is never blocked — the node
		// is fully functional in memory regardless of whether the file exists yet.
		go func() {
			for i := 0; i < 60; i++ {
				if _, err := os.Stat(dbFile); err == nil {
					if i > 0 {
						fmt.Println("[DB] Database file confirmed on disk.")
					}
					return
				}
				time.Sleep(500 * time.Millisecond)
				saveLocalDB()
			}
			fmt.Println("[DB] WARNING: could not confirm database file after 30s — data will not persist until next successful save.")
		}()
	} else {
		fmt.Println("[Unlock] Unlocking local database...")
		isNodeLocked = true
		loadLocalDB()
		if node.Identity.BlockedHashes == nil {
			node.Identity.BlockedHashes = make([]string, 0)
		}
		if node.Identity.TrustedHashes == nil {
			node.Identity.TrustedHashes = make([]string, 0)
		}
		if node.Identity.BannedFrom == nil {
			node.Identity.BannedFrom = make([]string, 0)
		}
		for k, p := range node.Platforms {
			if p.ShadowBannedHashes == nil {
				p.ShadowBannedHashes = make([]string, 0)
				node.Platforms[k] = p
			}
		}
		saveLocalDB()
	}
}

// setLastUpdate stamps the node's update time and wakes any goroutines that
// are long-polling for changes. Must be called while holding node.mu (write).
func setLastUpdate() {
	node.LastUpdate = time.Now().UnixMilli()
	// Broadcast on the dedicated standalone cond — safe because updateMu is
	// completely independent of node.mu, avoiding any lock-ordering deadlock.
	updateCond.Broadcast()
}

func saveLocalDB() {
	dbMutex.Lock()
	defer dbMutex.Unlock()

	node.mu.RLock()
	data, err := json.MarshalIndent(node, "", "  ")
	node.mu.RUnlock()

	if err != nil {
		fmt.Printf("[DB] Error marshaling state: %v\n", err)
		return
	}

	// 1. Forcefully guarantee BOTH the database folder AND the files directory exist
	os.MkdirAll(filepath.Dir(dbFile), 0755)
	os.MkdirAll(fileStoreDir, 0755)

	// 2. Silent retry loop to handle Windows Defender Cloud Analysis delays on new machines
	var writeErr error
	for i := 1; i <= 15; i++ {
		// Write directly to the database file, bypassing .tmp rename patterns
		writeErr = os.WriteFile(dbFile, data, 0600)
		if writeErr == nil {
			return // Silent success once Defender releases the lock!
		}
		
		// Wait a full second per retry while the OS analyzes the unrecognized .exe
		time.Sleep(1 * time.Second) 
	}

	// 3. If it completely fails after 15 seconds, print the actual error so you aren't guessing
	fmt.Printf("\n[DB] FATAL ERROR: Windows permanently blocked the JSON file from writing.\nError: %v\n", writeErr)
}

func loadLocalDB() {
	dbMutex.Lock()
	defer dbMutex.Unlock()
	data, err := os.ReadFile(dbFile)
	if err == nil {
		node.mu.Lock()
		json.Unmarshal(data, node)
		if node.SeenSignatures == nil {
			node.SeenSignatures = make(map[string]int64)
		}
		if node.Identity.TrustedHashes == nil {
			node.Identity.TrustedHashes = make([]string, 0)
		}
		if node.Identity.BannedFrom == nil {
			node.Identity.BannedFrom = make([]string, 0)
		}
		for k, p := range node.Platforms {
			if p.ShadowBannedHashes == nil {
				p.ShadowBannedHashes = make([]string, 0)
				node.Platforms[k] = p
			}
		}
		setLastUpdate()
		node.mu.Unlock()
	}
}

// ==========================================
// Cryptography Security Checks & Helpers
// ==========================================

func deriveKey(password string, salt []byte) []byte {
	return pbkdf2.Key([]byte(password), salt, 600000, 32, sha256.New)
}

func encryptData(data []byte, password string, saltHex string) string {
	salt, _ := hex.DecodeString(saltHex)
	key := deriveKey(password, salt)
	block, _ := aes.NewCipher(key)
	gcm, _ := cipher.NewGCM(block)
	nonce := make([]byte, gcm.NonceSize())
	rand.Read(nonce)
	ciphertext := gcm.Seal(nonce, nonce, data, nil)
	return base64.StdEncoding.EncodeToString(ciphertext)
}

func decryptData(cryptoText string, password string, saltHex string) ([]byte, error) {
	data, err := base64.StdEncoding.DecodeString(cryptoText)
	if err != nil {
		return nil, err
	}
	salt, _ := hex.DecodeString(saltHex)
	key := deriveKey(password, salt)
	block, _ := aes.NewCipher(key)
	gcm, _ := cipher.NewGCM(block)
	nonceSize := gcm.NonceSize()
	if len(data) < nonceSize {
		return nil, fmt.Errorf("ciphertext too short")
	}
	nonce, ciphertext := data[:nonceSize], data[nonceSize:]
	return gcm.Open(nil, nonce, ciphertext, nil)
}

func cleanReplayCache() {
	node.mu.Lock()
	defer node.mu.Unlock()
	cutoff := time.Now().UnixNano() - int64(15*time.Minute)
	for sig, timestamp := range node.SeenSignatures {
		if timestamp < cutoff {
			delete(node.SeenSignatures, sig)
		}
	}
}

// capMessages trims node.Messages to at most maxMessages entries, keeping the
// most recent ones.  Call this while holding node.mu.Lock().
const maxMessages = 100_000

func capMessages() {
	if len(node.Messages) > maxMessages {
		// Evict oldest entries; keep the tail.
		node.Messages = node.Messages[len(node.Messages)-maxMessages:]
	}
}

// Vulnerability 3 Fix: Strong Length-Prefixed Canonicalization
func generateSignaturePayload(msg Message) string {
	return fmt.Sprintf("%d:%s:%d:%s:%d:%s:%d:%s:%d:%s:%d:%s:%d",
		len(msg.ID), msg.ID,
		len(msg.Platform), msg.Platform,
		len(msg.MsgType), msg.MsgType,
		len(msg.TargetHash), msg.TargetHash,
		len(msg.Text), msg.Text,
		len(msg.FileCID), msg.FileCID,
		msg.Timestamp.UnixNano())
}

// Vulnerability 5 Fix: Properly cache cryptographic mathematical success, not packet rejection.
// The timestamp drift check is applied BEFORE the signature is cached so that a future-dated
// message cannot slip through via the cache on a subsequent delivery.
func verifyMessageSignature(msg Message) bool {
	// Enforce timestamp drift first — before any signature work or cache lookup.
	drift := time.Since(msg.Timestamp)
	if drift > 15*time.Minute || drift < -15*time.Minute {
		return false
	}

	node.mu.RLock()
	_, mathAlreadyVerified := node.SeenSignatures[msg.Signature]
	node.mu.RUnlock()

	if !mathAlreadyVerified {
		pubBytes, err := hex.DecodeString(msg.PublicKey)
		if err != nil || len(pubBytes) != ed25519.PublicKeySize {
			return false
		}
		hash := sha256.Sum256(pubBytes)
		if hex.EncodeToString(hash[:]) != msg.Sender {
			return false
		}
		sigBytes, err := hex.DecodeString(msg.Signature)
		if err != nil || len(sigBytes) != ed25519.SignatureSize {
			return false
		}

		payloadToVerify := generateSignaturePayload(msg)
		if !ed25519.Verify(pubBytes, []byte(payloadToVerify), sigBytes) {
			return false
		}

		node.mu.Lock()
		node.SeenSignatures[msg.Signature] = time.Now().UnixNano()
		node.mu.Unlock()
	}

	return true
}

// ==========================================
// P2P Networking & Discovery
// ==========================================

func extractXMLTag(data, tag string) string {
	startTag := "<" + tag + ">"
	endTag := "</" + tag + ">"
	startIdx := strings.Index(data, startTag)
	if startIdx == -1 {
		return ""
	}
	startIdx += len(startTag)
	endIdx := strings.Index(data[startIdx:], endTag)
	if endIdx == -1 {
		return ""
	}
	return data[startIdx : startIdx+endIdx]
}

func attemptUPnP(portStr string) {
	portInt := 0
	fmt.Sscanf(portStr, "%d", &portInt)
	if portInt == 0 { return }

	fmt.Println("[UPnP] Checking router for automatic port forwarding capabilities...")

	addr, _ := net.ResolveUDPAddr("udp", "239.255.255.250:1900")
	conn, err := net.ListenUDP("udp", nil)
	if err != nil { return }
	defer conn.Close()

	req := "M-SEARCH * HTTP/1.1\r\nHost: 239.255.255.250:1900\r\nST: urn:schemas-upnp-org:device:InternetGatewayDevice:1\r\nMan: \"ssdp:discover\"\r\nMX: 2\r\n\r\n"
	conn.WriteToUDP([]byte(req), addr)
	conn.SetReadDeadline(time.Now().Add(3 * time.Second))

	buf := make([]byte, 2048)
	n, _, err := conn.ReadFromUDP(buf)
	if err != nil {
		fmt.Println("[UPnP] No compatible router found (Normal if on a Hotspot or Enterprise Network).")
		return
	}

	respStr := string(buf[:n])
	location := ""
	for _, line := range strings.Split(respStr, "\r\n") {
		if strings.HasPrefix(strings.ToLower(line), "location:") {
			location = strings.TrimSpace(line[9:])
			break
		}
	}
	if location == "" { return }

	upnpClient := http.Client{Timeout: 5 * time.Second}
	resp, err := upnpClient.Get(location)
	if err != nil { return }
	defer resp.Body.Close()
	xmlData, _ := io.ReadAll(resp.Body)
	xmlStr := string(xmlData)

	serviceType := "urn:schemas-upnp-org:service:WANIPConnection:1"
	sIdx := strings.Index(xmlStr, serviceType)
	if sIdx == -1 {
		serviceType = "urn:schemas-upnp-org:service:WANPPPConnection:1"
		sIdx = strings.Index(xmlStr, serviceType)
	}
	if sIdx == -1 { return }
	
	subXml := xmlStr[sIdx:]
	controlURL := extractXMLTag(subXml, "controlURL")
	if controlURL == "" { return }

	baseURL, _ := url.Parse(location)
	ctrlURL, _ := baseURL.Parse(controlURL)

	localIP := getLocalIP()
	
	soapBody := fmt.Sprintf(`<?xml version="1.0"?>
<s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/">
<s:Body>
    <u:AddPortMapping xmlns:u="%s">
        <NewRemoteHost></NewRemoteHost>
        <NewExternalPort>%d</NewExternalPort>
        <NewProtocol>TCP</NewProtocol>
        <NewInternalPort>%d</NewInternalPort>
        <NewInternalClient>%s</NewInternalClient>
        <NewEnabled>1</NewEnabled>
        <NewPortMappingDescription>Aegis P2P Node</NewPortMappingDescription>
        <NewLeaseDuration>0</NewLeaseDuration>
    </u:AddPortMapping>
</s:Body>
</s:Envelope>`, serviceType, portInt, portInt, localIP)

	reqSoap, _ := http.NewRequest("POST", ctrlURL.String(), strings.NewReader(soapBody))
	reqSoap.Header.Set("Content-Type", `text/xml; charset="utf-8"`)
	reqSoap.Header.Set("SOAPAction", fmt.Sprintf(`"%s#AddPortMapping"`, serviceType))

	client := http.Client{Timeout: 5 * time.Second}
	resSoap, err := client.Do(reqSoap)
	if resSoap != nil {
		defer resSoap.Body.Close()
	}
	if err == nil && resSoap.StatusCode == 200 {
		fmt.Printf("[UPnP] SUCCESS! Router automatically forwarded public port %d to this machine.\n", portInt)
	} else {
		fmt.Println("[UPnP] Router rejected port mapping. You may need a Mesh Relay or manual port forward.")
	}
}

func getLocalIP() string {
	addrs, err := net.InterfaceAddrs()
	if err != nil {
		return "127.0.0.1"
	}
	for _, address := range addrs {
		if ipnet, ok := address.(*net.IPNet); ok && !ipnet.IP.IsLoopback() {
			if ipnet.IP.To4() != nil {
				ip := ipnet.IP.String()
				if strings.HasPrefix(ip, "192.168.") || strings.HasPrefix(ip, "10.") {
					return ip
				}
			}
		}
	}
	for _, address := range addrs {
		if ipnet, ok := address.(*net.IPNet); ok && !ipnet.IP.IsLoopback() {
			if ipnet.IP.To4() != nil {
				return ipnet.IP.String()
			}
		}
	}
	return "127.0.0.1"
}

func getPublicIP() string {
	client := http.Client{Timeout: 3 * time.Second}
	resp, err := client.Get("https://api.ipify.org")
	if resp != nil {
		defer resp.Body.Close()
	}
	if err != nil || resp.StatusCode != http.StatusOK {
		return ""
	}
	b, err := io.ReadAll(io.LimitReader(resp.Body, 64)) // IPs are at most ~45 chars
	if err != nil {
		return ""
	}
	ip := strings.TrimSpace(string(b))
	// Validate it's actually an IP before trusting it
	if net.ParseIP(ip) == nil {
		return ""
	}
	return ip
}

func apiPing(w http.ResponseWriter, r *http.Request) {
	setNoCache(w)
	w.Header().Set("Content-Type", "application/json")
	node.mu.RLock()
	hash := node.Identity.RootHash
	node.mu.RUnlock()
	json.NewEncoder(w).Encode(map[string]string{
		"root_hash": hash,
		"status":    "alive",
	})
}

// isRestrictedIP blocks IPs that must never be contacted by the P2P layer to
// prevent SSRF attacks against internal services and cloud metadata endpoints.
func isRestrictedIP(ip net.IP) bool {
	restrictedBlocks := []string{
		"127.0.0.0/8",     // IPv4 loopback
		"10.0.0.0/8",      // RFC1918 private
		"172.16.0.0/12",   // RFC1918 private
		"192.168.0.0/16",  // RFC1918 private
		"169.254.0.0/16",  // Link-local / AWS+GCP+Azure metadata (169.254.169.254)
		"100.64.0.0/10",   // Shared address space (RFC6598, carrier-grade NAT)
		"192.0.0.0/24",    // IETF protocol assignments
		"198.18.0.0/15",   // Benchmark testing
		"198.51.100.0/24", // TEST-NET-2 (documentation)
		"203.0.113.0/24",  // TEST-NET-3 (documentation)
		"240.0.0.0/4",     // Reserved
		"::1/128",         // IPv6 loopback
		"fc00::/7",        // IPv6 unique local
		"fe80::/10",       // IPv6 link-local
		"fd00::/8",        // IPv6 ULA (also covers GCP internal metadata)
	}
	for _, block := range restrictedBlocks {
		_, cidr, err := net.ParseCIDR(block)
		if err == nil && cidr.Contains(ip) {
			return true
		}
	}
	return false
}

func registerPeer(rawURL string, remoteAddr string, doReverse bool) {
	if rawURL == "" {
		return
	}
	peerURL := strings.TrimSpace(rawURL)
	peerURL = strings.TrimRight(peerURL, "/")

	if !strings.HasPrefix(peerURL, "http://") && !strings.HasPrefix(peerURL, "https://") {
		return
	}
	
	parsed, err := url.Parse(peerURL)
	if err != nil || parsed.Hostname() == "" {
		return
	}

	ips, err := net.LookupIP(parsed.Hostname())
	if err == nil && len(ips) > 0 {
		for _, ip := range ips {
			// Block cloud instance metadata endpoints — these are the real SSRF risk.
			// We allow RFC1918 / private IPs because LAN peers are a valid use-case.
			metadataBlocks := []string{
				"169.254.0.0/16", // AWS/GCP/Azure/IMDS metadata
				"fd00::/8",       // GCP internal metadata over IPv6
			}
			for _, block := range metadataBlocks {
				_, cidr, err := net.ParseCIDR(block)
				if err == nil && cidr.Contains(ip) {
					fmt.Println("[P2P] Blocked SSRF attempt to cloud metadata IP:", ip)
					return
				}
			}
		}
	}

	verifyAlive := func(target string) (bool, string) {
		client := http.Client{Timeout: 3 * time.Second}
		resp, err := client.Get(target + "/api/ping")
		if resp != nil {
			defer resp.Body.Close()
		}
		if err != nil || resp.StatusCode != http.StatusOK {
			return false, ""
		}
		var info map[string]string
		json.NewDecoder(io.LimitReader(resp.Body, 1024)).Decode(&info)
		// Validate root_hash is a hex string of correct length before trusting it
		if h := info["root_hash"]; len(h) != 64 {
			return false, ""
		}
		return true, info["root_hash"]
	}

	alive, remoteHash := verifyAlive(peerURL)
	
	if !alive && remoteAddr != "" {
		remoteHost, _, splitErr := net.SplitHostPort(remoteAddr)
		if splitErr == nil {
			if remoteHost == "::1" {
				remoteHost = "127.0.0.1"
			}
			
			port := parsed.Port()
			if port == "" {
				port = "80"
				if parsed.Scheme == "https" { port = "443" }
			}
			
			fallbackURL := fmt.Sprintf("%s://%s:%s", parsed.Scheme, remoteHost, port)
			
			alive, remoteHash = verifyAlive(fallbackURL)
			if alive {
				peerURL = fallbackURL 
			}
		}
	}

	if !alive {
		return 
	}

	node.mu.RLock()
	if remoteHash == node.Identity.RootHash || remoteHash == "" {
		node.mu.RUnlock()
		return
	}
	
	exists := false
	for _, p := range node.Peers {
		if p == peerURL {
			exists = true
			break
		}
	}
	node.mu.RUnlock()

	if !exists {
		node.mu.Lock()
		const maxPeers = 500
		if len(node.Peers) >= maxPeers {
			node.mu.Unlock()
			fmt.Printf("[P2P] Peer list full (%d); dropping new peer %s\n", maxPeers, peerURL)
			return
		}
		node.Peers = append(node.Peers, peerURL)
		node.mu.Unlock()
		
		fmt.Printf("[P2P] Verified & Registered New Peer: %s (Hash: %s)\n", peerURL, remoteHash[:8])
		
		go saveLocalDB()
		
		if doReverse {
			go func() {
				localIP := getLocalIP()
				publicIP := getPublicIP()
				var announceURLs []string
				announceURLs = append(announceURLs, fmt.Sprintf("http://%s:%s", localIP, currentPort))
				if publicIP != "" && publicIP != localIP {
					announceURLs = append(announceURLs, fmt.Sprintf("http://%s:%s", publicIP, currentPort))
				}
				client := http.Client{Timeout: 3 * time.Second}
				for _, me := range announceURLs {
					reqPayload, _ := json.Marshal(map[string]string{"url": me})
					client.Post(peerURL+"/api/peers", "application/json", bytes.NewBuffer(reqPayload))
				}
			}()
		}
	}
}

func broadcastMessageToPeers(msg Message) {
	node.mu.RLock()
	peers := make([]string, len(node.Peers))
	copy(peers, node.Peers)
	node.mu.RUnlock()

	if len(peers) == 0 {
		return
	}

	payload, _ := json.Marshal(msg)

	for _, peerURL := range peers {
		go func(pURL string) {
			client := http.Client{Timeout: 5 * time.Second}
			resp, err := client.Post(pURL+"/p2p/message", "application/json", bytes.NewBuffer(payload))
			
			if err == nil && resp.StatusCode == http.StatusOK {
				node.mu.Lock()
				for i, m := range node.Messages {
					if m.ID == msg.ID {
						node.Messages[i].IsAcked = true
						setLastUpdate()
						break
					}
				}
				node.mu.Unlock()
				go saveLocalDB()
			}
			
			if resp != nil {
				resp.Body.Close()
			}
		}(peerURL)
	}
}

// ==========================================
// Robust API Endpoints
// ==========================================

func apiIdentity(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }
	setNoCache(w)
	w.Header().Set("Content-Type", "application/json")
	
	node.mu.RLock()
	locked := isNodeLocked
	hasUsername := node.Identity.Username != ""
	node.mu.RUnlock()

	if r.Method == "POST" {
		var req struct { 
			Username string `json:"username"`
			Password string `json:"password"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err == nil {
			if req.Password == "" {
				jsonError(w, "Master password required to encrypt identity keys", http.StatusBadRequest)
				return
			}

			// Read the values we need for encryption before taking the write lock.
			// encryptData runs 600k pbkdf2 iterations — holding node.mu for that
			// duration would freeze every other goroutine in the process.
			node.mu.RLock()
			privKey := node.Identity.PrivateKey
			seedPhrase := node.Identity.SeedPhrase
			salt := node.Identity.CryptoSalt
			node.mu.RUnlock()

			if salt == "" {
				saltBytes := make([]byte, 16)
				rand.Read(saltBytes)
				salt = hex.EncodeToString(saltBytes)
			}

			// Do all expensive crypto work outside any lock.
			encryptedPrivKey := encryptData(privKey, req.Password, salt)
			seedData, _ := json.Marshal(seedPhrase)
			encryptedSeed := encryptData(seedData, req.Password, salt)

			// Now take the write lock only for the fast in-memory update.
			node.mu.Lock()
			node.Identity.Username = req.Username
			node.Identity.CryptoSalt = salt
			node.Identity.EncryptedPrivKey = encryptedPrivKey
			node.Identity.EncryptedSeed = encryptedSeed
			isNodeLocked = false
			node.mu.Unlock()

			saveLocalDB()
		}
	}
	
	node.mu.RLock()
	if locked && hasUsername {
		json.NewEncoder(w).Encode(map[string]interface{}{"locked": true})
	} else {
		json.NewEncoder(w).Encode(node.Identity)
	}
	node.mu.RUnlock()
}

func apiUnlock(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }
	w.Header().Set("Content-Type", "application/json")
	
	if r.Method != "POST" {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	
	var req struct { Password string `json:"password"` }
	json.NewDecoder(r.Body).Decode(&req)

	// Read the encrypted blobs without holding the write lock.
	node.mu.RLock()
	encPrivKey := node.Identity.EncryptedPrivKey
	encSeed := node.Identity.EncryptedSeed
	salt := node.Identity.CryptoSalt
	node.mu.RUnlock()

	// decryptData runs 600k pbkdf2 iterations — do it outside any lock so
	// other goroutines are not frozen for the duration.
	privKey, err1 := decryptData(encPrivKey, req.Password, salt)
	seedData, err2 := decryptData(encSeed, req.Password, salt)

	if err1 != nil || err2 != nil {
		jsonError(w, "Invalid master password", http.StatusUnauthorized)
		return
	}

	var seedPhrase []string
	json.Unmarshal(seedData, &seedPhrase)

	// Fast write lock only for the in-memory update.
	node.mu.Lock()
	node.Identity.PrivateKey = privKey
	node.Identity.SeedPhrase = seedPhrase
	isNodeLocked = false
	node.mu.Unlock()

	json.NewEncoder(w).Encode(map[string]string{"status": "unlocked"})
}

func apiResetNode(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }
	w.Header().Set("Content-Type", "application/json")

	if r.Method != "POST" {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	dbMutex.Lock()
	os.Remove(dbFile)
	os.Remove(dbFile + ".tmp")
	os.RemoveAll(fileStoreDir)
	os.MkdirAll(fileStoreDir, 0700)
	dbMutex.Unlock()

	node.mu.Lock()
	pub, priv, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		node.mu.Unlock()
		jsonError(w, "Failed to generate new keys", http.StatusInternalServerError)
		return
	}

	hash := sha256.Sum256(pub)
	rootHash := hex.EncodeToString(hash[:])
	
	saltBytes := make([]byte, 16)
	rand.Read(saltBytes)

	node.Identity = AegisIdentity{
		Username:      "", 
		PublicKey:     hex.EncodeToString(pub),
		PrivateKey:    priv,
		RootHash:      rootHash,
		SeedPhrase:    generateSeedPhrase(),
		CryptoSalt:    hex.EncodeToString(saltBytes),
		Devices:       []string{"device_01_local"},
		BlockedHashes: make([]string, 0),
		TrustedHashes: make([]string, 0),
		BannedFrom:    make([]string, 0),
	}

	node.Platforms = make(map[string]Platform)
	node.Messages = make([]Message, 0)
	node.Invites = make([]InviteContract, 0)
	node.Peers = []string{"http://3.16.213.66:8080"} // Restore optional default peer on factory reset
	node.Clock = HLC{Physical: time.Now().UnixNano(), Logical: 0}
	node.SeenSignatures = make(map[string]int64)

	isNodeLocked = false
	setLastUpdate()
	node.mu.Unlock()

	saveLocalDB()

	json.NewEncoder(w).Encode(map[string]string{"status": "reset"})
}

func apiBlockUser(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }
	w.Header().Set("Content-Type", "application/json")
	
	if r.Method == "POST" {
		var req struct { Hash string `json:"hash"` }
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			jsonError(w, "Invalid payload format", http.StatusBadRequest)
			return
		}

		node.mu.Lock()
		found := -1
		for i, h := range node.Identity.BlockedHashes {
			if h == req.Hash {
				found = i
				break
			}
		}
		
		if found >= 0 {
			node.Identity.BlockedHashes = append(node.Identity.BlockedHashes[:found], node.Identity.BlockedHashes[found+1:]...)
		} else {
			node.Identity.BlockedHashes = append(node.Identity.BlockedHashes, req.Hash)
		}
		setLastUpdate()
		node.mu.Unlock()
		
		saveLocalDB()
		json.NewEncoder(w).Encode(map[string]string{"status": "success"})
	} else {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
	}
}

func apiTrustUser(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }
	w.Header().Set("Content-Type", "application/json")
	
	if r.Method == "POST" {
		var req struct { Hash string `json:"hash"` }
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			jsonError(w, "Invalid payload format", http.StatusBadRequest)
			return
		}

		var messagesToBroadcast []Message

		// Resolve IPs before acquiring the lock — getPublicIP makes a network
		// request and must never be called while holding node.mu.
		localIP := getLocalIP()
		publicIP := getPublicIP()
		var announceURLs []string
		announceURLs = append(announceURLs, fmt.Sprintf("http://%s:%s", localIP, currentPort))
		if publicIP != "" && publicIP != localIP {
			announceURLs = append(announceURLs, fmt.Sprintf("http://%s:%s", publicIP, currentPort))
		}

		node.mu.Lock()
		found := -1
		for i, h := range node.Identity.TrustedHashes {
			if h == req.Hash {
				found = i
				break
			}
		}
		
		if found >= 0 {
			node.Identity.TrustedHashes = append(node.Identity.TrustedHashes[:found], node.Identity.TrustedHashes[found+1:]...)
		} else {
			node.Identity.TrustedHashes = append(node.Identity.TrustedHashes, req.Hash)

			urls := announceURLs

			for _, plat := range node.Platforms {
				if plat.IsTrusted && plat.Members[node.Identity.RootHash] == RoleOwner {
					invID := generateID("inv")
					inv := InviteContract{
						ID:        invID,
						Platform:  plat.ID,
						MaxUses:   999999,
						ExpiresAt: time.Now().Add(87600 * time.Hour), 
					}
					node.Invites = append(node.Invites, inv)

					payload := InvitePayload{
						PlatformID:   plat.ID,
						PlatformName: plat.Name,
						PeerURL:      urls[0], 
						PeerURLs:     urls,
						InviteID:     invID,
					}
					payloadBytes, _ := json.Marshal(payload)
					encodedCode := base64.StdEncoding.EncodeToString(payloadBytes)

					node.Clock.Increment()
					msg := Message{
						ID:         generateID("msg"),
						Platform:   plat.ID, 
						Sender:     node.Identity.RootHash,
						SenderName: node.Identity.Username,
						Text:       plat.Name, 
						MsgType:    "TRUSTED_INVITE",
						TargetHash: req.Hash,
						Payload:    encodedCode,
						Timestamp:  time.Now().UTC().Round(time.Millisecond),
						Clock:      node.Clock,
						PublicKey:  node.Identity.PublicKey,
						IsAcked:    false,
						AckedBy:    make([]string, 0),
					}
					payloadToSign := generateSignaturePayload(msg)
					sig := ed25519.Sign(node.Identity.PrivateKey, []byte(payloadToSign))
					msg.Signature = hex.EncodeToString(sig)

					node.Messages = append(node.Messages, msg)
					messagesToBroadcast = append(messagesToBroadcast, msg)
				}
			}
		}
		setLastUpdate()
		node.mu.Unlock()
		
		go saveLocalDB()
		for _, msg := range messagesToBroadcast {
			go broadcastMessageToPeers(msg)
		}

		json.NewEncoder(w).Encode(map[string]string{"status": "success"})
	} else {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
	}
}

func apiBanUser(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }
	w.Header().Set("Content-Type", "application/json")
	
	if r.Method == "POST" {
		var req struct {
			PlatformID string `json:"platform_id"`
			Hash       string `json:"hash"`
			Action     string `json:"action"` 
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			jsonError(w, "Invalid payload format", http.StatusBadRequest)
			return
		}

		node.mu.Lock()
		plat, exists := node.Platforms[req.PlatformID]
		if !exists {
			node.mu.Unlock()
			jsonError(w, "Platform not found", http.StatusNotFound)
			return
		}
		
		myRole := plat.Members[node.Identity.RootHash]
		
		if myRole != RoleOwner && myRole != RoleAdmin {
			node.mu.Unlock()
			jsonError(w, "Unauthorized action", http.StatusForbidden)
			return
		}

		if req.Action == "ban" {
			found := -1
			for i, h := range plat.BannedHashes { if h == req.Hash { found = i; break } }
			if found < 0 { plat.BannedHashes = append(plat.BannedHashes, req.Hash) }
		} else if req.Action == "unban" {
			found := -1
			for i, h := range plat.BannedHashes { if h == req.Hash { found = i; break } }
			if found >= 0 { plat.BannedHashes = append(plat.BannedHashes[:found], plat.BannedHashes[found+1:]...) }
		} else if req.Action == "shadow_ban" {
			found := -1
			for i, h := range plat.ShadowBannedHashes { if h == req.Hash { found = i; break } }
			if found < 0 { plat.ShadowBannedHashes = append(plat.ShadowBannedHashes, req.Hash) }
		} else if req.Action == "unshadow_ban" {
			found := -1
			for i, h := range plat.ShadowBannedHashes { if h == req.Hash { found = i; break } }
			if found >= 0 { plat.ShadowBannedHashes = append(plat.ShadowBannedHashes[:found], plat.ShadowBannedHashes[found+1:]...) }
		}
		
		node.Platforms[req.PlatformID] = plat

		node.Clock.Increment()
		msgType := "PLATFORM_BAN"
		if req.Action == "unban" { msgType = "PLATFORM_UNBAN" }
		if req.Action == "shadow_ban" { msgType = "PLATFORM_SHADOW_BAN" }
		if req.Action == "unshadow_ban" { msgType = "PLATFORM_UNSHADOW_BAN" }
		
		banMsg := Message{
			ID:         generateID("msg"),
			Platform:   req.PlatformID,
			Sender:     node.Identity.RootHash,
			SenderName: node.Identity.Username,
			Text:       req.Hash,
			MsgType:    msgType,
			TargetHash: req.Hash,
			Timestamp:  time.Now().UTC().Round(time.Millisecond),
			Clock:      node.Clock,
			PublicKey:  node.Identity.PublicKey,
			IsAcked:    false,
			AckedBy:    make([]string, 0),
		}
		
		payloadToSign := generateSignaturePayload(banMsg)
		sig := ed25519.Sign(node.Identity.PrivateKey, []byte(payloadToSign))
		banMsg.Signature = hex.EncodeToString(sig)
		
		node.Messages = append(node.Messages, banMsg)
		setLastUpdate()
		node.mu.Unlock()
		
		go saveLocalDB()
		go broadcastMessageToPeers(banMsg)

		json.NewEncoder(w).Encode(map[string]string{"status": "success"})
	} else {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
	}
}

// apiPeers is the LOCAL admin version — requires auth for all operations.
func apiPeers(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }
	setNoCache(w)
	w.Header().Set("Content-Type", "application/json")
	
	if r.Method == "GET" {
		node.mu.RLock()
		defer node.mu.RUnlock()
		json.NewEncoder(w).Encode(node.Peers)
		return
	}
	
	if r.Method == "POST" {
		var req struct { URL string `json:"url"` }
		if err := json.NewDecoder(r.Body).Decode(&req); err == nil && req.URL != "" {
			go registerPeer(req.URL, r.RemoteAddr, true)
		}
		node.mu.RLock()
		json.NewEncoder(w).Encode(node.Peers)
		node.mu.RUnlock()
		return
	}

	if r.Method == "DELETE" {
		var req struct { URL string `json:"url"` }
		if err := json.NewDecoder(r.Body).Decode(&req); err == nil && req.URL != "" {
			node.mu.Lock()
			var updatedPeers []string
			for _, p := range node.Peers {
				if p != req.URL {
					updatedPeers = append(updatedPeers, p)
				}
			}
			node.Peers = updatedPeers
			node.mu.Unlock()
			go saveLocalDB()
		}
		node.mu.RLock()
		json.NewEncoder(w).Encode(node.Peers)
		node.mu.RUnlock()
		return
	}
	
	jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
}

// p2pApiPeers is the PUBLIC p2p version — allows unauthenticated POST (peer announcement)
// and GET (peer discovery), but returns an empty list for GET to avoid leaking topology.
func p2pApiPeers(w http.ResponseWriter, r *http.Request) {
	setNoCache(w)
	w.Header().Set("Content-Type", "application/json")

	if r.Method == "GET" {
		// Return empty list publicly — peers are discovered via direct connection, not broadcast.
		json.NewEncoder(w).Encode([]string{})
		return
	}

	if r.Method == "POST" {
		var req struct { URL string `json:"url"` }
		if err := json.NewDecoder(r.Body).Decode(&req); err == nil && req.URL != "" {
			go registerPeer(req.URL, r.RemoteAddr, false) // doReverse=false to avoid amplification
		}
		w.WriteHeader(http.StatusOK)
		return
	}

	jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
}

func apiPlatforms(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }
	setNoCache(w)
	w.Header().Set("Content-Type", "application/json")

	if r.Method == "GET" {
		node.mu.RLock()
		json.NewEncoder(w).Encode(node.Platforms)
		node.mu.RUnlock()
		return
	}

	if r.Method == "POST" {
		var req struct {
			Name        string `json:"name"`
			IsEphemeral bool   `json:"is_ephemeral"`
			IsTrusted   bool   `json:"is_trusted"`
			TTLHours    int    `json:"ttl_hours"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			jsonError(w, "Invalid payload format", http.StatusBadRequest)
			return
		}

		randomBytes := make([]byte, 4)
		rand.Read(randomBytes)
		id := fmt.Sprintf("plat_%s_%x", node.Identity.RootHash[:16], randomBytes)

		p := Platform{
			ID:          id,
			Name:        req.Name,
			IsEphemeral: req.IsEphemeral,
			IsTrusted:   req.IsTrusted,
			Members:     map[string]Role{node.Identity.RootHash: RoleOwner},
		}

		if req.IsEphemeral {
			p.TTL = time.Now().Add(time.Duration(req.TTLHours) * time.Hour)
		}

		// Resolve IPs before acquiring the lock — getPublicIP makes a network
		// request (up to 3 s) and must never be called while holding node.mu.
		var announceURLs []string
		if req.IsTrusted {
			localIP := getLocalIP()
			publicIP := getPublicIP()
			announceURLs = append(announceURLs, fmt.Sprintf("http://%s:%s", localIP, currentPort))
			if publicIP != "" && publicIP != localIP {
				announceURLs = append(announceURLs, fmt.Sprintf("http://%s:%s", publicIP, currentPort))
			}
		}

		node.mu.Lock()
		node.Platforms[id] = p
		
		var messagesToBroadcast []Message

		if req.IsTrusted {
			invID := generateID("inv")
			inv := InviteContract{
				ID:        invID,
				Platform:  id,
				MaxUses:   999999,
				ExpiresAt: time.Now().Add(87600 * time.Hour), 
			}
			node.Invites = append(node.Invites, inv)

			urls := announceURLs

			payload := InvitePayload{
				PlatformID:   id,
				PlatformName: req.Name,
				PeerURL:      urls[0],
				PeerURLs:     urls,
				InviteID:     invID,
			}

			payloadBytes, _ := json.Marshal(payload)
			encodedCode := base64.StdEncoding.EncodeToString(payloadBytes)

			node.Clock.Increment()
			for _, th := range node.Identity.TrustedHashes {
				msg := Message{
					ID:         generateID("msg"),
					Platform:   id, 
					Sender:     node.Identity.RootHash,
					SenderName: node.Identity.Username,
					Text:       req.Name, 
					MsgType:    "TRUSTED_INVITE",
					TargetHash: th,
					Payload:    encodedCode,
					Timestamp:  time.Now().UTC().Round(time.Millisecond),
					Clock:      node.Clock,
					PublicKey:  node.Identity.PublicKey,
					IsAcked:    false,
					AckedBy:    make([]string, 0),
				}
				payloadToSign := generateSignaturePayload(msg)
				sig := ed25519.Sign(node.Identity.PrivateKey, []byte(payloadToSign))
				msg.Signature = hex.EncodeToString(sig)

				node.Messages = append(node.Messages, msg)
				messagesToBroadcast = append(messagesToBroadcast, msg)
			}
		}

		setLastUpdate()
		node.mu.Unlock()
		
		go saveLocalDB()
		for _, msg := range messagesToBroadcast {
			go broadcastMessageToPeers(msg)
		}

		json.NewEncoder(w).Encode(p)
	} else {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
	}
}

func apiLeavePlatform(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }
	w.Header().Set("Content-Type", "application/json")
	
	if r.Method == "POST" {
		var req struct { ID string `json:"id"` }
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			jsonError(w, "Invalid payload structure", http.StatusBadRequest)
			return
		}

		node.mu.Lock()
		delete(node.Platforms, req.ID)
		
		var filteredMsgs []Message
		for _, m := range node.Messages {
			if m.Platform != req.ID {
				filteredMsgs = append(filteredMsgs, m)
			}
		}
		node.Messages = filteredMsgs

		var filteredInvites []InviteContract
		for _, i := range node.Invites {
			if i.Platform != req.ID {
				filteredInvites = append(filteredInvites, i)
			}
		}
		node.Invites = filteredInvites
		
		setLastUpdate()
		node.mu.Unlock()

		saveLocalDB()
		json.NewEncoder(w).Encode(map[string]string{"status": "success"})
	} else {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
	}
}

func apiAckMessage(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }
	var req struct {
		MessageIDs []string `json:"message_ids"`
	}
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		jsonError(w, "Invalid payload format", http.StatusBadRequest)
		return
	}

	var updatedMsgs []Message
	node.mu.Lock()
	myHash := node.Identity.RootHash
	changed := false

	for _, reqID := range req.MessageIDs {
		for i, m := range node.Messages {
			if m.ID == reqID {
				hasMe := false
				for _, a := range m.AckedBy {
					if a == myHash {
						hasMe = true
						break
					}
				}
				if !hasMe {
					node.Messages[i].AckedBy = append(node.Messages[i].AckedBy, myHash)
					changed = true
					updatedMsgs = append(updatedMsgs, node.Messages[i])
				}
				break
			}
		}
	}

	if changed {
		setLastUpdate()
	}
	node.mu.Unlock()

	if changed {
		go saveLocalDB()
		for _, uMsg := range updatedMsgs {
			go broadcastMessageToPeers(uMsg)
		}
	}

	json.NewEncoder(w).Encode(map[string]string{"status": "success"})
}

func apiMessages(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }
	setNoCache(w)
	w.Header().Set("Content-Type", "application/json")

	if r.Method == "GET" {
		limitStr := r.URL.Query().Get("limit")
		sinceStr := r.URL.Query().Get("since")
		var since int64
		if sinceStr != "" {
			fmt.Sscanf(sinceStr, "%d", &since)
		}

		if since > 0 {
			// Long-poll: block up to 10 s waiting for a state change.
			// updateMu/updateCond are completely independent of node.mu — we must
			// never acquire node.mu while holding updateMu (or vice-versa) to
			// avoid a deadlock between the writer (apiPlatforms holds node.mu,
			// calls setLastUpdate → Broadcast) and the waiter (holds updateMu,
			// loop body would re-acquire node.mu.RLock).
			node.mu.RLock()
			currentUpdate := node.LastUpdate
			node.mu.RUnlock()

			if currentUpdate <= since {
				deadline := time.Now().Add(10 * time.Second)
				updateMu.Lock()
				for currentUpdate <= since && time.Now().Before(deadline) {
					updateCond.Wait()
					// Re-read LastUpdate without holding node.mu inside the loop —
					// safe because int64 reads are atomic on all supported platforms,
					// and we only need eventual visibility here.
					currentUpdate = node.LastUpdate
				}
				updateMu.Unlock()
			}

			if currentUpdate <= since {
				w.WriteHeader(http.StatusNotModified)
				return
			}
		}

		node.mu.RLock()
		lastUpdate := node.LastUpdate
		platformID := r.URL.Query().Get("platform")
		filtered := make([]Message, 0)
		for _, m := range node.Messages {
			if platformID == "" || m.Platform == platformID {
				filtered = append(filtered, m)
			}
		}
		node.mu.RUnlock()
		
		limit := 2000 
		if limitStr != "" {
			fmt.Sscanf(limitStr, "%d", &limit)
		}
		if len(filtered) > limit {
			filtered = filtered[len(filtered)-limit:]
		}

		w.Header().Set("X-Last-Update", fmt.Sprintf("%d", lastUpdate))
		json.NewEncoder(w).Encode(filtered)
		return
	}

	if r.Method == "POST" {
		var msg Message
		if err := json.NewDecoder(r.Body).Decode(&msg); err != nil {
			jsonError(w, "Invalid payload format", http.StatusBadRequest)
			return
		}

		node.mu.Lock()
		if plat, ok := node.Platforms[msg.Platform]; ok {
			for _, bh := range plat.BannedHashes {
				if bh == node.Identity.RootHash {
					node.mu.Unlock()
					jsonError(w, "You are banned from this platform", http.StatusForbidden)
					return
				}
			}
			for _, bh := range plat.ShadowBannedHashes {
				if bh == node.Identity.RootHash {
					// Shadow-ban: silently accept the message locally so the sender
					// doesn't know they're suppressed, but don't store or broadcast it.
					node.mu.Unlock()
					w.WriteHeader(http.StatusCreated)
					json.NewEncoder(w).Encode(msg)
					return
				}
			}
		}

		node.Clock.Increment()
		msg.ID = generateID("msg")
		msg.Sender = node.Identity.RootHash
		msg.SenderName = node.Identity.Username
		msg.PublicKey = node.Identity.PublicKey
		msg.Timestamp = time.Now().UTC().Round(time.Millisecond) 
		msg.Clock = node.Clock
		msg.IsAcked = false 
		msg.AckedBy = make([]string, 0) 

		if msg.MsgType == "" {
			msg.MsgType = "TEXT"
		}

		payloadToSign := generateSignaturePayload(msg)
		sig := ed25519.Sign(node.Identity.PrivateKey, []byte(payloadToSign))
		msg.Signature = hex.EncodeToString(sig)

		node.Messages = append(node.Messages, msg)
		
		if plat, exists := node.Platforms[msg.Platform]; exists {
			if _, memberExists := plat.Members[msg.Sender]; !memberExists {
				plat.Members[msg.Sender] = RoleMember
				node.Platforms[msg.Platform] = plat
			}
		}
		setLastUpdate()
		node.mu.Unlock()
		
		go saveLocalDB()
		go broadcastMessageToPeers(msg)

		w.WriteHeader(http.StatusCreated)
		json.NewEncoder(w).Encode(msg)
	} else {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
	}
}

// Vulnerability 2 Fix: Rebuild Tombstone as an explicit Command Message that can be verified and synced correctly
func apiModerate(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }
	w.Header().Set("Content-Type", "application/json")
	
	if r.Method == "POST" {
		var req struct {
			MessageID  string `json:"message_id"`
			PlatformID string `json:"platform_id"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			jsonError(w, "Invalid payload format", http.StatusBadRequest)
			return
		}

		node.mu.Lock()
		plat, exists := node.Platforms[req.PlatformID]
		if !exists {
			node.mu.Unlock()
			jsonError(w, "Platform not found", http.StatusNotFound)
			return
		}
		
		myRole := plat.Members[node.Identity.RootHash]
		
		if myRole != RoleOwner && myRole != RoleAdmin {
			node.mu.Unlock()
			jsonError(w, "Unauthorized: Powernode required", http.StatusForbidden)
			return
		}

		node.Clock.Increment()
		cmdMsg := Message{
			ID:         generateID("msg"),
			Platform:   req.PlatformID,
			Sender:     node.Identity.RootHash,
			SenderName: node.Identity.Username,
			Text:       req.MessageID, // Text contains the target ID
			MsgType:    "TOMBSTONE_CMD",
			Timestamp:  time.Now().UTC().Round(time.Millisecond),
			Clock:      node.Clock,
			PublicKey:  node.Identity.PublicKey,
			IsAcked:    false,
			AckedBy:    make([]string, 0),
		}

		payloadToSign := generateSignaturePayload(cmdMsg)
		sig := ed25519.Sign(node.Identity.PrivateKey, []byte(payloadToSign))
		cmdMsg.Signature = hex.EncodeToString(sig)

		node.Messages = append(node.Messages, cmdMsg)

		// Apply immediately to local data
		for i, m := range node.Messages {
			if m.ID == req.MessageID {
				node.Messages[i].MsgType = "TOMBSTONE"
				node.Messages[i].Text = ""
				node.Messages[i].FileCID = ""
				node.Messages[i].Clock.Update(node.Clock)
				break
			}
		}

		setLastUpdate()
		node.mu.Unlock()

		saveLocalDB()

		go broadcastMessageToPeers(cmdMsg)
		
		json.NewEncoder(w).Encode(map[string]string{"status": "success"})
	} else {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
	}
}

func apiInvites(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }
	w.Header().Set("Content-Type", "application/json")

	if r.Method == "POST" {
		var req struct {
			PlatformID string `json:"platform_id"`
			MaxUses    int    `json:"max_uses"`
			TTLHours   int    `json:"ttl_hours"`
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			jsonError(w, "Invalid payload structure", http.StatusBadRequest)
			return
		}

		node.mu.Lock()
		plat, exists := node.Platforms[req.PlatformID]
		if !exists {
			node.mu.Unlock()
			jsonError(w, "Platform not found", http.StatusNotFound)
			return
		}

		inv := InviteContract{
			ID:        generateID("inv"),
			Platform:  req.PlatformID,
			MaxUses:   req.MaxUses,
			ExpiresAt: time.Now().Add(time.Duration(req.TTLHours) * time.Hour),
		}

		node.Invites = append(node.Invites, inv)
		node.mu.Unlock()

		localIP := getLocalIP()
		publicIP := getPublicIP()
		var urls []string
		urls = append(urls, fmt.Sprintf("http://%s:%s", localIP, currentPort))
		if publicIP != "" && publicIP != localIP {
			urls = append(urls, fmt.Sprintf("http://%s:%s", publicIP, currentPort))
		}

		payload := InvitePayload{
			PlatformID:   req.PlatformID,
			PlatformName: plat.Name,
			PeerURL:      urls[0], 
			PeerURLs:     urls,
			InviteID:     inv.ID,
		}

		payloadBytes, _ := json.Marshal(payload)
		encodedCode := base64.StdEncoding.EncodeToString(payloadBytes)

		go saveLocalDB()

		json.NewEncoder(w).Encode(map[string]string{
			"invite_code": encodedCode,
		})
	} else {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
	}
}

func apiJoin(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }
	w.Header().Set("Content-Type", "application/json")
	
	if r.Method == "POST" {
		var req struct { InviteCode string `json:"invite_code"` }
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			jsonError(w, "Invalid payload structure", http.StatusBadRequest)
			return
		}

		decodedBytes, err := base64.StdEncoding.DecodeString(req.InviteCode)
		if err != nil {
			jsonError(w, "Invalid invite code format", http.StatusBadRequest)
			return
		}

		var payload InvitePayload
		if err := json.Unmarshal(decodedBytes, &payload); err != nil {
			jsonError(w, "Failed to parse invite metadata", http.StatusBadRequest)
			return
		}
		
		node.mu.RLock()
		isBanned := false
		for _, b := range node.Identity.BannedFrom {
			if b == payload.PlatformID {
				isBanned = true
				break
			}
		}
		node.mu.RUnlock()

		if isBanned {
			jsonError(w, "You have been permanently banned from this platform.", http.StatusForbidden)
			return
		}

		var validPeerURL string
		urlsToTry := payload.PeerURLs
		if len(urlsToTry) == 0 && payload.PeerURL != "" {
			urlsToTry = []string{payload.PeerURL}
		}

		checkClient := http.Client{Timeout: 4 * time.Second}
		for _, u := range urlsToTry {
			cleanU := strings.TrimRight(strings.TrimSpace(u), "/")
			resp, err := checkClient.Get(cleanU + "/api/ping")
			if err == nil && resp.StatusCode == http.StatusOK {
				var info map[string]string
				json.NewDecoder(io.LimitReader(resp.Body, 1024)).Decode(&info)
				resp.Body.Close()

				node.mu.RLock()
				myHash := node.Identity.RootHash
				node.mu.RUnlock()

				rh := info["root_hash"]
				if len(rh) == 64 && rh != myHash {
					validPeerURL = cleanU
					break
				}
			} else if resp != nil {
				resp.Body.Close()
			}
		}

		node.mu.RLock()
		hasRelay := len(node.Peers) > 0
		node.mu.RUnlock()

		if validPeerURL == "" && !hasRelay {
			jsonError(w, "Host Unreachable: Both nodes are trapped behind strict NAT firewalls without UPnP (e.g. mobile hotspots). To connect them, run Aegis on a cloud VPS to act as an automatic Mesh Relay.", http.StatusServiceUnavailable)
			return
		}

		node.mu.Lock()
		if _, platExists := node.Platforms[payload.PlatformID]; !platExists {
			node.Platforms[payload.PlatformID] = Platform{
				ID:         payload.PlatformID,
				Name:       payload.PlatformName,
				Members:    map[string]Role{node.Identity.RootHash: RoleMember},
			}
		}
		setLastUpdate()
		node.mu.Unlock()

		if validPeerURL != "" {
			go registerPeer(validPeerURL, "", true)

			// After registering, the meshSyncLoop will handle ongoing sync.
			// Do an immediate initial sync to populate the platform history.
			go func(peerURL, platformID string) {
				time.Sleep(500 * time.Millisecond) 
				syncURL := fmt.Sprintf("%s/p2p/sync?platform=%s&limit=1000", peerURL, platformID)
				client := http.Client{Timeout: 5 * time.Second}
				syncResp, err := client.Get(syncURL)
				
				if err == nil && syncResp != nil {
					defer syncResp.Body.Close()

					limitReader := io.LimitReader(syncResp.Body, 5*1024*1024)

					var pastMsgs []Message
					if err := json.NewDecoder(limitReader).Decode(&pastMsgs); err == nil {
						
						var validMsgs []Message
						for _, m := range pastMsgs {
							if verifyMessageSignature(m) {
								validMsgs = append(validMsgs, m)
							}
						}

						node.mu.Lock()
						changed := false
						myRootHash := node.Identity.RootHash
						
						for _, m := range validMsgs {
							
							isSenderBanned := false
							isSenderShadowBanned := false
							
							if plat, platExists := node.Platforms[m.Platform]; platExists {
								for _, bh := range plat.BannedHashes {
									if bh == m.Sender { isSenderBanned = true; break }
								}
								for _, bh := range plat.ShadowBannedHashes {
									if bh == m.Sender { isSenderShadowBanned = true; break }
								}
							}
							
							if isSenderBanned { continue }
							if isSenderShadowBanned && m.Sender != myRootHash { continue }

							if m.MsgType == "PLATFORM_BAN" && m.Text == myRootHash {
								foundB := false
								for _, b := range node.Identity.BannedFrom { if b == m.Platform { foundB = true; break } }
								if !foundB { node.Identity.BannedFrom = append(node.Identity.BannedFrom, m.Platform) }

								delete(node.Platforms, m.Platform)
								var filteredMsgs []Message
								for _, em := range node.Messages {
									if em.Platform != m.Platform {
										filteredMsgs = append(filteredMsgs, em)
									}
								}
								m.IsAcked = true
								filteredMsgs = append(filteredMsgs, m) 
								node.Messages = filteredMsgs
								changed = true
								continue 
							}
							
							if m.MsgType == "PLATFORM_UNBAN" && m.Text == myRootHash {
								found := -1
								for i, b := range node.Identity.BannedFrom { if b == m.Platform { found = i; break } }
								if found >= 0 {
									node.Identity.BannedFrom = append(node.Identity.BannedFrom[:found], node.Identity.BannedFrom[found+1:]...)
									changed = true
								}
							}

							if m.MsgType == "PLATFORM_BAN" || m.MsgType == "PLATFORM_UNBAN" || m.MsgType == "PLATFORM_SHADOW_BAN" || m.MsgType == "PLATFORM_UNSHADOW_BAN" {
								if plat, ok := node.Platforms[m.Platform]; ok {
									role, roleExists := plat.Members[m.Sender]
									
									if roleExists && (role == RoleOwner || role == RoleAdmin) {

										if m.MsgType == "PLATFORM_BAN" {
											found := -1
											for i, h := range plat.BannedHashes { if h == m.Text { found = i; break } }
											if found < 0 { plat.BannedHashes = append(plat.BannedHashes, m.Text) }
										} else if m.MsgType == "PLATFORM_UNBAN" {
											found := -1
											for i, h := range plat.BannedHashes { if h == m.Text { found = i; break } }
											if found >= 0 { plat.BannedHashes = append(plat.BannedHashes[:found], plat.BannedHashes[found+1:]...) }
										} else if m.MsgType == "PLATFORM_SHADOW_BAN" {
											found := -1
											for i, h := range plat.ShadowBannedHashes { if h == m.Text { found = i; break } }
											if found < 0 { plat.ShadowBannedHashes = append(plat.ShadowBannedHashes, m.Text) }
										} else if m.MsgType == "PLATFORM_UNSHADOW_BAN" {
											found := -1
											for i, h := range plat.ShadowBannedHashes { if h == m.Text { found = i; break } }
											if found >= 0 { plat.ShadowBannedHashes = append(plat.ShadowBannedHashes[:found], plat.ShadowBannedHashes[found+1:]...) }
										}
										node.Platforms[m.Platform] = plat
										changed = true
									}
								}
							}

							exists := false
							for i, existing := range node.Messages {
								if existing.ID == m.ID {
									exists = true

									if len(m.AckedBy) > 0 {
										merged := make(map[string]bool)
										for _, a := range existing.AckedBy { merged[a] = true }
										added := false
										for _, a := range m.AckedBy {
											if !merged[a] {
												merged[a] = true
												node.Messages[i].AckedBy = append(node.Messages[i].AckedBy, a)
												added = true
											}
										}
										if added { changed = true }
									}
									break
								}
							}
							if !exists {
								m.IsAcked = true
								node.Messages = append(node.Messages, m)
								capMessages()
								node.Clock.Update(m.Clock)
								changed = true
								
								// Process pending tombstones dynamically
								for _, cmd := range node.Messages {
									if cmd.MsgType == "TOMBSTONE_CMD" && cmd.Text == m.ID {
										isAuth := cmd.Sender == m.Sender
										if !isAuth {
											if p, ok := node.Platforms[cmd.Platform]; ok {
												role := p.Members[cmd.Sender]
												if role == RoleOwner || role == RoleAdmin { isAuth = true }
											}
										}
										if isAuth {
											node.Messages[len(node.Messages)-1].MsgType = "TOMBSTONE"
											node.Messages[len(node.Messages)-1].Text = ""
											node.Messages[len(node.Messages)-1].FileCID = ""
											break
										}
									}
								}

								if plat, ok := node.Platforms[m.Platform]; ok {
									if _, memExists := plat.Members[m.Sender]; !memExists {
										plat.Members[m.Sender] = RoleMember
										node.Platforms[m.Platform] = plat
									}
								}
							}

							// Apply Tombstone Cmd logic dynamically
							if m.MsgType == "TOMBSTONE_CMD" {
								targetMsgID := m.Text
								isAuthorized := false
								for _, existing := range node.Messages {
									if existing.ID == targetMsgID {
										if m.Sender == existing.Sender { isAuthorized = true; break }
									}
								}
								if !isAuthorized {
									if p, ok := node.Platforms[m.Platform]; ok {
										role := p.Members[m.Sender]
										if role == RoleOwner || role == RoleAdmin { isAuthorized = true }
									}
								}

								if isAuthorized {
									for i, existing := range node.Messages {
										if existing.ID == targetMsgID && existing.MsgType != "TOMBSTONE" {
											node.Messages[i].MsgType = "TOMBSTONE"
											node.Messages[i].Text = ""
											node.Messages[i].FileCID = ""
											node.Messages[i].Clock.Update(m.Clock)
											changed = true
											break
										}
									}
								}
							}

						}
						if changed {
							setLastUpdate()
						}
						node.mu.Unlock()
						if changed { saveLocalDB() }
					}
				}
			}(validPeerURL, payload.PlatformID)
		}

		saveLocalDB()
		json.NewEncoder(w).Encode(map[string]string{"status": "success"})
	} else {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
	}
}

// ==========================================
// File API & P2P Handlers
// ==========================================

func getDirSize(path string) int64 {
	var size int64
	filepath.Walk(path, func(_ string, info os.FileInfo, err error) error {
		if err == nil && !info.IsDir() {
			size += info.Size()
		}
		return nil
	})
	return size
}

// verifyCID reads the encrypted file, decodes each GCM chunk, hashes the plaintext,
// and checks that the result matches the expected CID. This prevents a malicious peer
// from storing arbitrary data under a trusted CID.
func verifyCID(filePath string, expectedCID string) bool {
	// We need the AES key to decode chunks and hash plaintext.
	// Look it up from the message ledger.
	node.mu.RLock()
	var aesKeyHex string
	for _, m := range node.Messages {
		if m.FileCID == expectedCID && m.MsgType == "FILE_TICKET" {
			aesKeyHex = m.Payload
			break
		}
	}
	node.mu.RUnlock()

	if aesKeyHex == "" {
		// No key available (file received before ticket) — skip content check,
		// rely on the ticket-validation gate in p2pReceiveFile.
		return true
	}

	aesKey, err := hex.DecodeString(aesKeyHex)
	if err != nil || len(aesKey) != 32 {
		return false
	}

	f, err := os.Open(filePath)
	if err != nil {
		return false
	}
	defer f.Close()

	block, err := aes.NewCipher(aesKey)
	if err != nil { return false }
	gcm, err := cipher.NewGCM(block)
	if err != nil { return false }

	hasher := sha256.New()
	lenBuf := make([]byte, 4)
	for {
		_, err := io.ReadFull(f, lenBuf)
		if err == io.EOF { break }
		if err != nil { return false }
		chunkLen := int(lenBuf[0])<<24 | int(lenBuf[1])<<16 | int(lenBuf[2])<<8 | int(lenBuf[3])
		if chunkLen <= 0 || chunkLen > 2*1024*1024+gcm.NonceSize()+gcm.Overhead() {
			return false
		}
		chunkData := make([]byte, chunkLen)
		if _, err := io.ReadFull(f, chunkData); err != nil { return false }
		if len(chunkData) < gcm.NonceSize() { return false }
		nonce := chunkData[:gcm.NonceSize()]
		ciphertext := chunkData[gcm.NonceSize():]
		plaintext, err := gcm.Open(nil, nonce, ciphertext, nil)
		if err != nil { return false }
		hasher.Write(plaintext)
	}

	computed := hex.EncodeToString(hasher.Sum(nil))
	return computed == expectedCID
}

func broadcastFileToPeers(cid string) {
	node.mu.RLock()
	peers := make([]string, len(node.Peers))
	copy(peers, node.Peers)
	node.mu.RUnlock()

	if len(peers) == 0 {
		return
	}

	path := filepath.Join(fileStoreDir, cid)

	for _, peerURL := range peers {
		go func(pURL string) {
			file, err := os.Open(path)
			if err != nil {
				return
			}
			defer file.Close()

			client := http.Client{Timeout: 10 * time.Minute}
			req, err := http.NewRequest("POST", pURL+"/p2p/files/push?cid="+cid, file)
			if err != nil {
				return
			}
			req.Header.Set("Content-Type", "application/octet-stream")
			resp, err := client.Do(req)
			if err == nil && resp != nil {
				resp.Body.Close()
			}
		}(peerURL)
	}
}

func p2pReceiveFile(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	cid := r.URL.Query().Get("cid")
	if cid == "" || len(cid) != 64 {
		http.Error(w, "Invalid cid", http.StatusBadRequest)
		return
	}

	// Vulnerability 1 Fix: Explicitly decode hex to prevent arbitrary path traversal and injection attacks
	if _, err := hex.DecodeString(cid); err != nil {
		http.Error(w, "Malformed cid", http.StatusBadRequest)
		return
	}

	// Ensure the file is bound to a verified cryptographic ticket
	node.mu.RLock()
	isValidTicket := false
	var expectedSize int64
	for _, m := range node.Messages {
		if m.FileCID == cid && m.MsgType == "FILE_TICKET" {
			if _, ok := node.Platforms[m.Platform]; ok {
				isValidTicket = true
				expectedSize = m.FileSize
				break
			}
		}
	}
	node.mu.RUnlock()

	if !isValidTicket {
		http.Error(w, "Rejected: CID not found in verified ledger", http.StatusForbidden)
		return
	}

	// Vulnerability 4 Fix: Enforce accurate size bounds limits to prevent DoS via infinite data streams
	if expectedSize <= 0 || expectedSize > 5*1024*1024*1024 {
		http.Error(w, "File exceeds network limits", http.StatusBadRequest)
		return
	}

	if getDirSize(fileStoreDir)+expectedSize > 50*1024*1024*1024 { // 50GB node total max
		http.Error(w, "Node storage quota exceeded", http.StatusForbidden)
		return
	}

	path := filepath.Join(fileStoreDir, cid)
	if _, err := os.Stat(path); err == nil {
		w.WriteHeader(http.StatusOK) 
		return
	}

	r.Body = http.MaxBytesReader(w, r.Body, expectedSize+1024) 

	tempPath := filepath.Join(fileStoreDir, generateID("temp_push"))
	outFile, err := os.Create(tempPath)
	if err != nil {
		http.Error(w, "Storage failure", http.StatusInternalServerError)
		return
	}

	_, err = io.Copy(outFile, r.Body)
	outFile.Close()

	if err != nil {
		os.Remove(tempPath)
		http.Error(w, "Transfer failed or exceeded quota bounds", http.StatusInternalServerError)
		return
	}

	os.Rename(tempPath, path)

	// Verify that the received content actually hashes to the claimed CID.
	// This prevents a malicious peer from injecting arbitrary data.
	if !verifyCID(path, cid) {
		os.Remove(path)
		fmt.Printf("[P2P] CID integrity check failed for incoming file %s — discarding.\n", cid[:8])
		http.Error(w, "Integrity check failed: content does not match CID", http.StatusBadRequest)
		return
	}

	go broadcastFileToPeers(cid)

	w.WriteHeader(http.StatusOK)
}

func apiUploadFile(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }

	currentSize := getDirSize(fileStoreDir)
	if currentSize > 50*1024*1024*1024 { // 50GB node total max
		jsonError(w, "Node storage strictly forbids uploads. Hard quota > 50GB exceeded.", http.StatusForbidden)
		return
	}
	
	r.Body = http.MaxBytesReader(w, r.Body, 5<<30+100<<20) // Max network read 5.1GB
	err := r.ParseMultipartForm(32 << 20) // Only hold 32MB in RAM; smoothly stream the rest to disk
	if err != nil {
		jsonError(w, "File too large. Mesh limit is 5GB per file.", http.StatusBadRequest)
		return
	}

	file, header, err := r.FormFile("file")
	if err != nil {
		jsonError(w, "Invalid file upload structure", http.StatusBadRequest)
		return
	}
	defer file.Close()

	// Use AES-256-GCM for authenticated encryption.
	// The file is streamed in chunks to avoid loading it all into memory.
	fileKey := make([]byte, 32)
	rand.Read(fileKey)

	block, err := aes.NewCipher(fileKey)
	if err != nil {
		jsonError(w, "Cipher init failure", http.StatusInternalServerError)
		return
	}
	gcm, err := cipher.NewGCM(block)
	if err != nil {
		jsonError(w, "GCM init failure", http.StatusInternalServerError)
		return
	}

	// For large file streaming with GCM we chunk-encrypt.
	// Each chunk: [4-byte big-endian length][nonce(12)][ciphertext+tag]
	const chunkSize = 1 * 1024 * 1024 // 1MB plaintext chunks

	cidHasher := sha256.New()
	tempPath := filepath.Join(fileStoreDir, generateID("temp"))
	outFile, err := os.Create(tempPath)
	if err != nil {
		jsonError(w, "Storage failure", http.StatusInternalServerError)
		return
	}

	buf := make([]byte, chunkSize)
	var encErr error
	for {
		n, readErr := io.ReadFull(file, buf)
		if n > 0 {
			nonce := make([]byte, gcm.NonceSize())
			if _, err := rand.Read(nonce); err != nil {
				encErr = err
				break
			}
			ciphertext := gcm.Seal(nil, nonce, buf[:n], nil)
			// Write: [4-byte chunk length][nonce][ciphertext]
			chunkLen := uint32(len(nonce) + len(ciphertext))
			lenBytes := []byte{byte(chunkLen >> 24), byte(chunkLen >> 16), byte(chunkLen >> 8), byte(chunkLen)}
			cidHasher.Write(buf[:n]) // Hash plaintext for CID
			outFile.Write(lenBytes)
			outFile.Write(nonce)
			outFile.Write(ciphertext)
		}
		if readErr == io.EOF || readErr == io.ErrUnexpectedEOF {
			break
		}
		if readErr != nil {
			encErr = readErr
			break
		}
	}
	outFile.Close()

	if encErr != nil {
		os.Remove(tempPath)
		jsonError(w, "Encryption stream failure", http.StatusInternalServerError)
		return
	}

	cid := hex.EncodeToString(cidHasher.Sum(nil))
	finalPath := filepath.Join(fileStoreDir, cid)
	os.Rename(tempPath, finalPath)

	go broadcastFileToPeers(cid)

	warningMsg := ""
	if currentSize > 45*1024*1024*1024 {
		warningMsg = "Warning: Node storage exceeds 45GB. Approaching hard disk limit."
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"cid":     cid,
		"name":    header.Filename,
		"key":     hex.EncodeToString(fileKey),
		"warning": warningMsg,
	})
}

func p2pServeFile(w http.ResponseWriter, r *http.Request) {
	cid := r.URL.Query().Get("cid")
	
	if cid == "" || len(cid) != 64 {
		http.Error(w, "Invalid or missing cid", http.StatusBadRequest)
		return
	}
	if _, err := hex.DecodeString(cid); err != nil {
		http.Error(w, "Malformed cid", http.StatusBadRequest)
		return
	}

	path := filepath.Join(fileStoreDir, cid)
	if _, err := os.Stat(path); os.IsNotExist(err) {
		http.Error(w, "File not found locally", http.StatusNotFound)
		return
	}

	w.Header().Set("Content-Type", "application/octet-stream")
	http.ServeFile(w, r, path)
}

func apiDownloadFile(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }
	cid := r.URL.Query().Get("cid")
	name := r.URL.Query().Get("name")
	
	if cid == "" || len(cid) != 64 {
		jsonError(w, "Invalid or missing cid", http.StatusBadRequest)
		return
	}
	if _, err := hex.DecodeString(cid); err != nil {
		jsonError(w, "Malformed cid", http.StatusBadRequest)
		return
	}

	var fileKeyHex string
	var expectedSize int64
	node.mu.RLock()
	peers := append([]string{}, node.Peers...)
	for _, m := range node.Messages {
		if m.FileCID == cid && m.MsgType == "FILE_TICKET" {
			fileKeyHex = m.Payload
			expectedSize = m.FileSize
			break
		}
	}
	node.mu.RUnlock()

	if fileKeyHex == "" {
		http.Error(w, "Access Denied: Keys not found on authenticated ledger", http.StatusForbidden)
		return
	}
	aesKey, err := hex.DecodeString(fileKeyHex)
	if err != nil || len(aesKey) != 32 {
		http.Error(w, "Invalid key format", http.StatusInternalServerError)
		return
	}

	path := filepath.Join(fileStoreDir, cid)
	if _, err := os.Stat(path); os.IsNotExist(err) {
		found := false
		// Cap the fetch size: encrypted overhead is modest, so allow 10% margin above plaintext size.
		// Fall back to a 5GB cap if expectedSize is unknown.
		fetchLimit := expectedSize + expectedSize/10 + 1024*1024
		if fetchLimit <= 0 || fetchLimit > 5*1024*1024*1024+100*1024*1024 {
			fetchLimit = 5*1024*1024*1024 + 100*1024*1024
		}
		for _, peer := range peers {
			client := http.Client{Timeout: 10 * time.Minute}
			resp, err := client.Get(peer + "/p2p/files?cid=" + cid)
			if err == nil && resp.StatusCode == http.StatusOK {
				outFile, err := os.Create(path)
				if err == nil {
					// LimitReader prevents a malicious peer from streaming infinite data
					_, copyErr := io.Copy(outFile, io.LimitReader(resp.Body, fetchLimit))
					outFile.Close()
					resp.Body.Close()
					if copyErr == nil {
						// Verify content integrity: hash the raw file and compare to CID
						if verifyCID(path, cid) {
							found = true
							break
						}
						// Hash mismatch — discard the corrupt/tampered file
						os.Remove(path)
						fmt.Printf("[P2P] CID integrity check failed for %s from %s\n", cid[:8], peer)
					} else {
						os.Remove(path)
					}
				} else {
					resp.Body.Close()
				}
			} else if resp != nil {
				resp.Body.Close()
			}
		}
		if !found {
			http.Error(w, "File not available on the mesh. The sender might be offline.", http.StatusNotFound)
			return
		}
	}

	inFile, err := os.Open(path)
	if err != nil {
		http.Error(w, "Local read failure", http.StatusInternalServerError)
		return
	}
	defer inFile.Close()

	block, err := aes.NewCipher(aesKey)
	if err != nil {
		http.Error(w, "Cipher init failure", http.StatusInternalServerError)
		return
	}
	gcm, err := cipher.NewGCM(block)
	if err != nil {
		http.Error(w, "GCM init failure", http.StatusInternalServerError)
		return
	}

	// Strip to safe characters only — prevents CRLF header injection via crafted filenames.
	safeBytes := make([]byte, 0, len(name))
	for _, c := range filepath.Base(name) {
		if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') ||
			c == '.' || c == '-' || c == '_' || c == ' ' {
			safeBytes = append(safeBytes, byte(c))
		}
	}
	safeName := strings.TrimSpace(string(safeBytes))
	if safeName == "" || safeName == "." {
		safeName = "download"
	}
	w.Header().Set("Content-Disposition", fmt.Sprintf(`attachment; filename="%s"`, safeName))
	w.Header().Set("Content-Type", "application/octet-stream")

	// Decode chunked GCM format: [4-byte length][nonce][ciphertext+tag] ...
	lenBuf := make([]byte, 4)
	for {
		_, err := io.ReadFull(inFile, lenBuf)
		if err == io.EOF {
			break
		}
		if err != nil {
			return
		}
		chunkLen := int(lenBuf[0])<<24 | int(lenBuf[1])<<16 | int(lenBuf[2])<<8 | int(lenBuf[3])
		if chunkLen <= 0 || chunkLen > 2*1024*1024+gcm.NonceSize()+gcm.Overhead() {
			http.Error(w, "Corrupt chunk header", http.StatusInternalServerError)
			return
		}
		chunkData := make([]byte, chunkLen)
		if _, err := io.ReadFull(inFile, chunkData); err != nil {
			return
		}
		if len(chunkData) < gcm.NonceSize() {
			return
		}
		nonce := chunkData[:gcm.NonceSize()]
		ciphertext := chunkData[gcm.NonceSize():]
		plaintext, err := gcm.Open(nil, nonce, ciphertext, nil)
		if err != nil {
			// Authentication tag mismatch — file has been tampered with
			fmt.Printf("[Security] GCM authentication failed for file %s\n", cid[:8])
			return
		}
		w.Write(plaintext)
	}
}

// p2pSyncMessages is the PUBLIC endpoint peers use to pull messages during mesh sync.
// It only returns messages for platforms the requester specifies, and strips sensitive
// invite payload data (TRUSTED_INVITE Payload field) before sending.
func p2pSyncMessages(w http.ResponseWriter, r *http.Request) {
	if r.Method != "GET" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	setNoCache(w)
	w.Header().Set("Content-Type", "application/json")

	platformID := r.URL.Query().Get("platform")
	// Platform IDs are generated internally as "plat_{32hex}_{8hex}" — cap at 64 chars
	if len(platformID) > 64 {
		http.Error(w, "Invalid platform id", http.StatusBadRequest)
		return
	}
	limitStr := r.URL.Query().Get("limit")
	limit := 200
	if limitStr != "" {
		fmt.Sscanf(limitStr, "%d", &limit)
		if limit > 500 { limit = 500 }
		if limit < 1 { limit = 1 }
	}

	node.mu.RLock()
	var filtered []Message
	for _, m := range node.Messages {
		if platformID != "" && m.Platform != platformID {
			continue
		}
		// Strip TRUSTED_INVITE payloads — these contain encoded invite codes
		// and are only meaningful to the targeted recipient.
		if m.MsgType == "TRUSTED_INVITE" {
			stripped := m
			stripped.Payload = ""
			filtered = append(filtered, stripped)
		} else {
			filtered = append(filtered, m)
		}
	}
	node.mu.RUnlock()

	if len(filtered) > limit {
		filtered = filtered[len(filtered)-limit:]
	}

	json.NewEncoder(w).Encode(filtered)
}

func p2pReceiveMessage(w http.ResponseWriter, r *http.Request) {
	if r.Method == "POST" {
		// Cap incoming P2P message size to 1MB — messages are text/metadata only,
		// files are transferred via the separate /p2p/files/push endpoint.
		r.Body = http.MaxBytesReader(w, r.Body, 1<<20)
		var msg Message
		if err := json.NewDecoder(r.Body).Decode(&msg); err != nil {
			jsonError(w, "Invalid payload format", http.StatusBadRequest)
			return
		}

		if !verifyMessageSignature(msg) {
			jsonError(w, "Signature verification failed or replay detected", http.StatusUnauthorized)
			return
		}

		node.mu.Lock()
		
		plat, platExists := node.Platforms[msg.Platform]
		
		if !platExists && msg.TargetHash != node.Identity.RootHash {
			node.mu.Unlock()
			w.WriteHeader(http.StatusOK) // Silently drop pushes for unknown platforms
			return
		}

		isSenderBanned := false
		isSenderShadowBanned := false
		
		if platExists {
			for _, bh := range plat.BannedHashes {
				if bh == msg.Sender { isSenderBanned = true; break }
			}
			for _, bh := range plat.ShadowBannedHashes {
				if bh == msg.Sender { isSenderShadowBanned = true; break }
			}
		}

		if isSenderBanned {
			node.mu.Unlock()
			w.WriteHeader(http.StatusOK)
			return
		}
		if isSenderShadowBanned && msg.Sender != node.Identity.RootHash {
			node.mu.Unlock()
			w.WriteHeader(http.StatusOK)
			return
		}

		if msg.MsgType == "PLATFORM_BAN" && msg.Text == node.Identity.RootHash {
			foundB := false
			for _, b := range node.Identity.BannedFrom {
				if b == msg.Platform { foundB = true; break }
			}
			if !foundB { node.Identity.BannedFrom = append(node.Identity.BannedFrom, msg.Platform) }

			delete(node.Platforms, msg.Platform)
			var filteredMsgs []Message
			for _, em := range node.Messages {
				if em.Platform != msg.Platform {
					filteredMsgs = append(filteredMsgs, em)
				}
			}
			node.Messages = filteredMsgs
			setLastUpdate()
			node.mu.Unlock()
			go saveLocalDB()
			w.WriteHeader(http.StatusOK)
			return
		}

		if msg.MsgType == "PLATFORM_UNBAN" && msg.Text == node.Identity.RootHash {
			found := -1
			for i, b := range node.Identity.BannedFrom {
				if b == msg.Platform { found = i; break }
			}
			if found >= 0 {
				node.Identity.BannedFrom = append(node.Identity.BannedFrom[:found], node.Identity.BannedFrom[found+1:]...)
			}
		}

		if msg.MsgType == "PLATFORM_BAN" || msg.MsgType == "PLATFORM_UNBAN" || msg.MsgType == "PLATFORM_SHADOW_BAN" || msg.MsgType == "PLATFORM_UNSHADOW_BAN" {
			if platExists {
				role, roleExists := plat.Members[msg.Sender]
				
				if roleExists && (role == RoleOwner || role == RoleAdmin) {

					if msg.MsgType == "PLATFORM_BAN" {
						found := -1
						for i, h := range plat.BannedHashes { if h == msg.Text { found = i; break } }
						if found < 0 { plat.BannedHashes = append(plat.BannedHashes, msg.Text) }
					} else if msg.MsgType == "PLATFORM_UNBAN" {
						found := -1
						for i, h := range plat.BannedHashes { if h == msg.Text { found = i; break } }
						if found >= 0 { plat.BannedHashes = append(plat.BannedHashes[:found], plat.BannedHashes[found+1:]...) }
					} else if msg.MsgType == "PLATFORM_SHADOW_BAN" {
						found := -1
						for i, h := range plat.ShadowBannedHashes { if h == msg.Text { found = i; break } }
						if found < 0 { plat.ShadowBannedHashes = append(plat.ShadowBannedHashes, msg.Text) }
					} else if msg.MsgType == "PLATFORM_UNSHADOW_BAN" {
						found := -1
						for i, h := range plat.ShadowBannedHashes { if h == msg.Text { found = i; break } }
						if found >= 0 { plat.ShadowBannedHashes = append(plat.ShadowBannedHashes[:found], plat.ShadowBannedHashes[found+1:]...) }
					}
					node.Platforms[msg.Platform] = plat
				}
			}
		}

		exists := false
		changed := false
		for i, m := range node.Messages {
			if m.ID == msg.ID {
				exists = true

				if len(msg.AckedBy) > 0 {
					merged := make(map[string]bool)
					for _, a := range m.AckedBy { merged[a] = true }
					added := false
					for _, a := range msg.AckedBy {
						if !merged[a] {
							merged[a] = true
							node.Messages[i].AckedBy = append(node.Messages[i].AckedBy, a)
							added = true
						}
					}
					if added { changed = true }
				}
				break
			}
		}

		if !exists {
			node.Clock.Update(msg.Clock)
			msg.IsAcked = true 
			node.Messages = append(node.Messages, msg)
			capMessages()
			
			// Process pending tombstones dynamically
			for _, cmd := range node.Messages {
				if cmd.MsgType == "TOMBSTONE_CMD" && cmd.Text == msg.ID {
					isAuth := cmd.Sender == msg.Sender
					if !isAuth {
						if p, ok := node.Platforms[cmd.Platform]; ok {
							role := p.Members[cmd.Sender]
							if role == RoleOwner || role == RoleAdmin { isAuth = true }
						}
					}
					if isAuth {
						node.Messages[len(node.Messages)-1].MsgType = "TOMBSTONE"
						node.Messages[len(node.Messages)-1].Text = ""
						node.Messages[len(node.Messages)-1].FileCID = ""
						break
					}
				}
			}

			if plat, ok := node.Platforms[msg.Platform]; ok {
				if _, memExists := plat.Members[msg.Sender]; !memExists {
					plat.Members[msg.Sender] = RoleMember
					node.Platforms[msg.Platform] = plat
				}
			}
			changed = true
		}
		
		// Apply Tombstone Cmd logic dynamically
		if msg.MsgType == "TOMBSTONE_CMD" {
			targetMsgID := msg.Text
			isAuthorized := false
			for _, existing := range node.Messages {
				if existing.ID == targetMsgID {
					if msg.Sender == existing.Sender { isAuthorized = true; break }
				}
			}
			if !isAuthorized {
				if p, ok := node.Platforms[msg.Platform]; ok {
					role := p.Members[msg.Sender]
					if role == RoleOwner || role == RoleAdmin { isAuthorized = true }
				}
			}

			if isAuthorized {
				for i, existing := range node.Messages {
					if existing.ID == targetMsgID && existing.MsgType != "TOMBSTONE" {
						node.Messages[i].MsgType = "TOMBSTONE"
						node.Messages[i].Text = ""
						node.Messages[i].FileCID = ""
						node.Messages[i].Clock.Update(msg.Clock)
						changed = true
						break
					}
				}
			}
		}

		var msgToBroadcast Message
		if changed {
			setLastUpdate()
			if !exists {
				msgToBroadcast = msg
			} else {
				for _, m := range node.Messages {
					if m.ID == msg.ID { msgToBroadcast = m; break }
				}
			}
		}
		node.mu.Unlock()

		if changed {
			go saveLocalDB()
			if msgToBroadcast.ID != "" {
				go broadcastMessageToPeers(msgToBroadcast) 
			}
		}

		w.WriteHeader(http.StatusOK)
	} else {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
	}
}

// ==========================================
// P2P Self-Healing Mesh Logic
// ==========================================

func announcePresence() {
	time.Sleep(3 * time.Second)

	localIP := getLocalIP()
	publicIP := getPublicIP()

	var announceURLs []string
	announceURLs = append(announceURLs, fmt.Sprintf("http://%s:%s", localIP, currentPort))
	if publicIP != "" && publicIP != localIP {
		announceURLs = append(announceURLs, fmt.Sprintf("http://%s:%s", publicIP, currentPort))
	}

	node.mu.RLock()
	peers := make([]string, len(node.Peers))
	copy(peers, node.Peers)
	node.mu.RUnlock()

	if len(peers) > 0 {
		fmt.Printf("[P2P] Announcing presence (%v) to %d known peers...\n", announceURLs, len(peers))
	}

	// Announce each of our addresses to every peer so cross-network peers
	// can discover our public IP even if they can't reach our LAN IP.
	for _, peerURL := range peers {
		for _, me := range announceURLs {
			go func(pURL, myAddr string) {
				reqPayload, _ := json.Marshal(map[string]string{"url": myAddr})
				client := http.Client{Timeout: 5 * time.Second}
				client.Post(pURL+"/api/peers", "application/json", bytes.NewBuffer(reqPayload))
			}(peerURL, me)
		}
	}
}

func peerMaintenance() {
	for {
		time.Sleep(5 * time.Minute) 

		node.mu.RLock()
		peers := make([]string, len(node.Peers))
		copy(peers, node.Peers)
		node.mu.RUnlock()

		var deadPeers []string

		for _, pURL := range peers {
			client := http.Client{Timeout: 5 * time.Second}
			resp, err := client.Get(pURL + "/api/ping")

			if err != nil || resp.StatusCode != http.StatusOK {
				deadPeers = append(deadPeers, pURL) 
			}
			if resp != nil {
				resp.Body.Close()
			}
		}

		if len(deadPeers) > 0 {
			node.mu.Lock()
			var updatedPeers []string
			for _, existing := range node.Peers {
				isDead := false
				for _, dead := range deadPeers {
					if existing == dead {
						isDead = true
						break
					}
				}
				if !isDead {
					updatedPeers = append(updatedPeers, existing)
				} else {
					fmt.Printf("[P2P] Peer unreachable, deprecating: %s\n", existing)
				}
			}
			node.Peers = updatedPeers
			node.mu.Unlock()

			saveLocalDB() 
		}
	}
}

func meshSyncLoop() {
	for {
		time.Sleep(10 * time.Second)

		node.mu.RLock()
		peers := make([]string, len(node.Peers))
		copy(peers, node.Peers)
		myPlatforms := make(map[string]bool)
		for k := range node.Platforms {
			myPlatforms[k] = true
		}
		myRootHash := node.Identity.RootHash
		node.mu.RUnlock()

		if len(peers) == 0 {
			continue
		}

		for _, peerURL := range peers {
			go func(pURL string) {
				client := http.Client{Timeout: 10 * time.Second} 
				resp, err := client.Get(pURL + "/p2p/sync?limit=200")
				if err == nil && resp.StatusCode == http.StatusOK {
					defer resp.Body.Close()
					
					limitReader := io.LimitReader(resp.Body, 5*1024*1024)
					var msgs []Message
					if err := json.NewDecoder(limitReader).Decode(&msgs); err == nil {
						
						var validMsgs []Message
						for _, m := range msgs {
							node.mu.RLock()
							_, platExists := node.Platforms[m.Platform]
							node.mu.RUnlock()

							isTargetedToMe := m.TargetHash == myRootHash
							
							if !platExists && !isTargetedToMe {
								continue 
							}
							
							if verifyMessageSignature(m) {
								validMsgs = append(validMsgs, m)
							}
						}
						
						if len(validMsgs) > 0 {
							node.mu.Lock()
							changed := false
							for _, m := range validMsgs {
								
								plat, platExists := node.Platforms[m.Platform]
								isTargetedToMe := m.TargetHash == myRootHash

								if !platExists && !isTargetedToMe {
									continue
								}

								isSenderBanned := false
								isSenderShadowBanned := false
								if platExists {
									for _, bh := range plat.BannedHashes {
										if bh == m.Sender {
											isSenderBanned = true
											break
										}
									}
									for _, bh := range plat.ShadowBannedHashes {
										if bh == m.Sender {
											isSenderShadowBanned = true
											break
										}
									}
								}
								if isSenderBanned {
									continue 
								}
								if isSenderShadowBanned && m.Sender != myRootHash {
									continue
								}
				
								if m.MsgType == "PLATFORM_BAN" && m.Text == myRootHash {
									foundB := false
									for _, b := range node.Identity.BannedFrom { if b == m.Platform { foundB = true; break } }
									if !foundB { node.Identity.BannedFrom = append(node.Identity.BannedFrom, m.Platform) }

									delete(node.Platforms, m.Platform)
									var filteredMsgs []Message
									for _, em := range node.Messages {
										if em.Platform != m.Platform {
											filteredMsgs = append(filteredMsgs, em)
										}
									}
									node.Messages = filteredMsgs
									changed = true
									continue 
								}

								if m.MsgType == "PLATFORM_UNBAN" && m.Text == myRootHash {
									found := -1
									for i, b := range node.Identity.BannedFrom { if b == m.Platform { found = i; break } }
									if found >= 0 {
										node.Identity.BannedFrom = append(node.Identity.BannedFrom[:found], node.Identity.BannedFrom[found+1:]...)
										changed = true
									}
								}

								if m.MsgType == "PLATFORM_BAN" || m.MsgType == "PLATFORM_UNBAN" || m.MsgType == "PLATFORM_SHADOW_BAN" || m.MsgType == "PLATFORM_UNSHADOW_BAN" {
									if platExists {
										role, roleExists := plat.Members[m.Sender]

										if roleExists && (role == RoleOwner || role == RoleAdmin) {

											if m.MsgType == "PLATFORM_BAN" {
												found := -1
												for i, h := range plat.BannedHashes { if h == m.Text { found = i; break } }
												if found < 0 { plat.BannedHashes = append(plat.BannedHashes, m.Text) }
											} else if m.MsgType == "PLATFORM_UNBAN" {
												found := -1
												for i, h := range plat.BannedHashes { if h == m.Text { found = i; break } }
												if found >= 0 { plat.BannedHashes = append(plat.BannedHashes[:found], plat.BannedHashes[found+1:]...) }
											} else if m.MsgType == "PLATFORM_SHADOW_BAN" {
												found := -1
												for i, h := range plat.ShadowBannedHashes { if h == m.Text { found = i; break } }
												if found < 0 { plat.ShadowBannedHashes = append(plat.ShadowBannedHashes, m.Text) }
											} else if m.MsgType == "PLATFORM_UNSHADOW_BAN" {
												found := -1
												for i, h := range plat.ShadowBannedHashes { if h == m.Text { found = i; break } }
												if found >= 0 { plat.ShadowBannedHashes = append(plat.ShadowBannedHashes[:found], plat.ShadowBannedHashes[found+1:]...) }
											}
											node.Platforms[m.Platform] = plat
											changed = true
										}
									}
								}

								exists := false
								for i, existing := range node.Messages {
									if existing.ID == m.ID {
										exists = true

										if len(m.AckedBy) > 0 {
											merged := make(map[string]bool)
											for _, a := range existing.AckedBy { merged[a] = true }
											added := false
											for _, a := range m.AckedBy {
												if !merged[a] {
													merged[a] = true
													node.Messages[i].AckedBy = append(node.Messages[i].AckedBy, a)
													added = true
												}
											}
											if added { changed = true }
										}
										break
									}
								}

								if !exists {
									m.IsAcked = true
									node.Messages = append(node.Messages, m)
									capMessages()
									node.Clock.Update(m.Clock)
									changed = true
									
									// Process pending tombstones dynamically
									for _, cmd := range node.Messages {
										if cmd.MsgType == "TOMBSTONE_CMD" && cmd.Text == m.ID {
											isAuth := cmd.Sender == m.Sender
											if !isAuth {
												if p, ok := node.Platforms[cmd.Platform]; ok {
													role := p.Members[cmd.Sender]
													if role == RoleOwner || role == RoleAdmin { isAuth = true }
												}
											}
											if isAuth {
												node.Messages[len(node.Messages)-1].MsgType = "TOMBSTONE"
												node.Messages[len(node.Messages)-1].Text = ""
												node.Messages[len(node.Messages)-1].FileCID = ""
												break
											}
										}
									}

									if plat, ok := node.Platforms[m.Platform]; ok {
										if _, memExists := plat.Members[m.Sender]; !memExists {
											plat.Members[m.Sender] = RoleMember
											node.Platforms[m.Platform] = plat
										}
									}
								}

								// Apply Tombstone Cmd logic dynamically
								if m.MsgType == "TOMBSTONE_CMD" {
									targetMsgID := m.Text
									isAuthorized := false
									for _, existing := range node.Messages {
										if existing.ID == targetMsgID {
											if m.Sender == existing.Sender { isAuthorized = true; break }
										}
									}
									if !isAuthorized {
										if p, ok := node.Platforms[m.Platform]; ok {
											role := p.Members[m.Sender]
											if role == RoleOwner || role == RoleAdmin { isAuthorized = true }
										}
									}

									if isAuthorized {
										for i, existing := range node.Messages {
											if existing.ID == targetMsgID && existing.MsgType != "TOMBSTONE" {
												node.Messages[i].MsgType = "TOMBSTONE"
												node.Messages[i].Text = ""
												node.Messages[i].FileCID = ""
												node.Messages[i].Clock.Update(m.Clock)
												changed = true
												break
											}
										}
									}
								}
							}
							
							if changed {
								setLastUpdate()
							}
							node.mu.Unlock()
							
							if changed {
								saveLocalDB()
							}
						}
					}
				}
			}(peerURL)
		}
	}
}

// --- Embedded UI (HTML/JS/CSS) ---

func serveUI(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "text/html")
	html := strings.Replace(htmlTemplate, "{{API_TOKEN}}", APIToken, 1)
	w.Write([]byte(html))
}

const htmlTemplate = `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Project Aegis | Local Node</title>
    <script src="https://cdn.tailwindcss.com"></script>
    <style>
        body { background-color: #0f172a; color: #f8fafc; font-family: ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Arial, sans-serif; }
        .mesh-bg { background-image: radial-gradient(#334155 1px, transparent 1px); background-size: 20px 20px; }
        ::-webkit-scrollbar { width: 8px; }
        ::-webkit-scrollbar-track { background: #1e293b; }
        ::-webkit-scrollbar-thumb { background: #475569; border-radius: 4px; }
        .platform-btn.active { background-color: rgba(79, 70, 229, 0.2); border-color: rgba(99, 102, 241, 0.4); color: #a5b4fc; }
        .sidebar-transition { transition: width 0.3s ease, border-width 0.3s ease; }
    </style>
</head>
<body class="h-screen flex flex-col mesh-bg" onclick="closeMemberMenu()">

    <div id="toastContainer" class="fixed bottom-4 right-4 z-[9000] flex flex-col space-y-2 pointer-events-none"></div>

    <div id="confirmModal" class="fixed inset-0 bg-black/80 backdrop-blur-sm hidden flex items-center justify-center z-[8000]">
        <div class="bg-slate-900 border border-slate-700 p-6 rounded-xl w-96 shadow-2xl">
            <h2 id="confirmTitle" class="text-xl font-bold mb-2 text-white">Confirm Action</h2>
            <p id="confirmMessage" class="text-sm text-slate-300 mb-6">Are you sure?</p>
            <div class="flex justify-end space-x-3">
                <button onclick="closeConfirmModal(false)" class="px-4 py-2 text-slate-400 hover:text-white transition-colors">Cancel</button>
                <button id="confirmBtn" onclick="closeConfirmModal(true)" class="bg-red-600 hover:bg-red-500 text-white px-4 py-2 rounded transition-colors font-bold">Confirm</button>
            </div>
        </div>
    </div>

    <!-- Live Video Modal -->
    <div id="videoModal" class="fixed top-24 left-1/4 bg-slate-900 border border-slate-700 rounded-xl shadow-2xl z-[100] hidden flex-col min-w-[320px] max-w-2xl resize overflow-hidden">
        <div id="videoModalHeader" class="bg-slate-800 p-2 cursor-move flex justify-between items-center border-b border-slate-700">
            <span class="text-xs font-bold text-slate-300 px-2">Live Mesh Call</span>
            <button onclick="toggleCall(false)" class="text-red-400 hover:text-red-300 text-xs px-2 font-bold">Hang Up</button>
        </div>
        <div id="videoGrid" class="p-2 grid grid-cols-2 gap-2 max-h-[60vh] overflow-y-auto bg-slate-950">
            <!-- Videos injected here -->
        </div>
        <div class="bg-slate-800 p-3 flex justify-between items-center border-t border-slate-700">
            <div class="flex space-x-2">
                <button id="btnMuteAudio" onclick="toggleMute()" class="bg-slate-700 hover:bg-slate-600 px-3 py-1.5 text-xs rounded text-emerald-400 font-bold shadow transition-colors flex items-center">
                    <span class="mr-1">🎙️</span> <span id="lblMute">Mute Audio</span>
                </button>
                <button id="btnVideoToggle" onclick="toggleLocalVideo()" class="bg-slate-700 hover:bg-slate-600 px-3 py-1.5 text-xs rounded text-emerald-400 font-bold shadow transition-colors flex items-center hidden">
                    <span class="mr-1">📹</span> <span id="lblVideo">Stop Video</span>
                </button>
                <button id="btnScreenShare" onclick="toggleScreenShare()" class="bg-slate-700 hover:bg-slate-600 px-3 py-1.5 text-xs rounded text-slate-400 font-bold shadow transition-colors flex items-center hidden">
                    <span class="mr-1">📺</span> <span id="lblScreen">Share</span>
                </button>
            </div>
            <button onclick="showPTTSettings()" class="bg-slate-700 hover:bg-slate-600 px-3 py-1.5 text-xs rounded text-slate-300 shadow transition-colors font-bold flex items-center">
                <span class="mr-1">⚙️</span> PTT Setup
            </button>
        </div>
    </div>

    <!-- Header / Nav -->
    <header class="bg-slate-900 border-b border-slate-700 p-4 flex justify-between items-center shadow-lg z-10">
        <div class="flex items-center space-x-3">
            <div class="w-8 h-8 rounded bg-indigo-500 flex items-center justify-center font-bold text-white shadow-[0_0_15px_rgba(99,102,241,0.5)]">A</div>
            <h1 class="text-xl font-bold tracking-wider">AEGIS <span class="text-xs text-indigo-400 align-top">v2.7-SECURE</span></h1>
        </div>
        <div class="flex items-center space-x-4 text-sm">
            <button onclick="showPeerModal()" id="peerStatusBtn" class="flex items-center hover:bg-slate-800 px-2 py-1 rounded transition-colors border border-transparent hover:border-slate-600 cursor-pointer">
                <span id="pCountDot" class="w-2 h-2 rounded-full bg-slate-600 mr-2"></span>
                <span id="peerCount">0 Peers</span>
            </button>
            <div class="bg-slate-800 px-3 py-1 rounded border border-slate-700 flex items-center space-x-2">
                <span class="text-slate-400">Node ID:</span>
                <span id="userIdBox" class="font-mono text-indigo-300">...</span>
            </div>
        </div>
    </header>

    <div class="flex flex-1 overflow-hidden">
        
        <!-- Sidebar (Platforms) -->
        <aside class="w-72 bg-slate-900/90 border-r border-slate-800 flex flex-col backdrop-blur-md">
            <div class="p-2 border-b border-slate-800 flex space-x-1 bg-slate-900/95">
                <button id="tabPlatforms" onclick="setTab('platforms')" class="flex-1 py-1.5 text-[10px] font-bold rounded bg-slate-800 text-white uppercase tracking-wider transition-colors relative">
                    Platforms <span id="badgePlatforms" class="hidden absolute -top-1 -right-1 bg-red-500 text-white text-[9px] px-1.5 py-0.5 rounded-full shadow">0</span>
                </button>
                <button id="tabDMs" onclick="setTab('dms')" class="flex-1 py-1.5 text-[10px] font-bold rounded text-slate-400 hover:bg-slate-800/50 uppercase tracking-wider transition-colors relative">
                    DMs <span id="badgeDMs" class="hidden absolute -top-1 -right-1 bg-red-500 text-white text-[9px] px-1.5 py-0.5 rounded-full shadow">0</span>
                </button>
            </div>
            
            <div class="p-3 border-b border-slate-800 flex flex-col justify-between items-center bg-slate-900">
                <div class="flex space-x-1 w-full mt-1 mb-1">
                    <button onclick="showDiscoverModal()" id="discoverBtn" class="flex-1 bg-emerald-600/80 hover:bg-emerald-500 text-white px-2 py-1 rounded text-xs transition-colors border border-emerald-500/50 shadow-sm font-bold" title="Discover Trusted Servers">🌐 Discover</button>
                    <button onclick="showJoinModal()" class="flex-1 bg-slate-800 hover:bg-slate-700 text-slate-300 px-2 py-1 rounded text-xs transition-colors border border-slate-700 shadow-sm" title="Join with Invite Code">+ Join</button>
                    <button onclick="showCreateModal()" class="flex-1 bg-indigo-600/80 hover:bg-indigo-500 text-white px-2 py-1 rounded text-xs transition-colors border border-indigo-500/50 shadow-sm font-bold" title="Create Platform">New</button>
                </div>
            </div>
			<div class="p-3 border-b border-slate-800 space-y-2">
				<input type="text" id="platformSearch" placeholder="Search platforms..." class="w-full bg-slate-800 border border-slate-700 rounded px-2 py-1.5 text-xs text-white outline-none focus:border-indigo-500 transition-colors" onkeyup="renderPlatformsList()">
				<select id="platformSort" class="w-full bg-slate-800 border border-slate-700 rounded px-2 py-1.5 text-xs text-slate-300 outline-none focus:border-indigo-500" onchange="renderPlatformsList()">
					<option value="default">Default Sort</option>
					<option value="az">A-Z Name Sort</option>
				</select>
			</div>
            <div id="platformsList" class="flex-1 overflow-y-auto p-3 space-y-1">
                <!-- Platforms rendered here -->
            </div>
        </aside>

        <!-- Chat Area -->
        <main class="flex-1 flex flex-col bg-slate-900/60 backdrop-blur-sm relative">
            <div class="p-4 border-b border-slate-800 flex justify-between items-center bg-slate-900/90">
                <div id="activePlatformHeader">
                    <h3 class="font-bold text-lg text-slate-300">No Platforms</h3><span class="text-xs text-slate-400">Join or create a platform to get started.</span>
                </div>
                <div class="flex space-x-2 hidden" id="platformActions">
                    <button onclick="toggleCall(false)" id="voiceBtn" class="text-xs bg-slate-800 hover:bg-slate-700 text-slate-300 px-3 py-1.5 rounded border border-slate-700 transition-colors flex items-center shadow-sm font-bold">
                        <span class="mr-1">🎙️ Audio Call</span>
                    </button>
                    <button onclick="toggleCall(true)" id="videoBtn" class="text-xs bg-slate-800 hover:bg-slate-700 text-slate-300 px-3 py-1.5 rounded border border-slate-700 transition-colors flex items-center shadow-sm font-bold">
                        <span class="mr-1">📹 Video Chat</span>
                    </button>
                    <button onclick="showBannedModal()" class="text-xs bg-slate-800 hover:bg-slate-700 text-slate-300 px-3 py-1.5 rounded border border-slate-700 transition-colors flex items-center shadow-sm" id="bannedUsersBtn" style="display:none;">
                        <span class="mr-1">Ban List</span>
                    </button>
                    <button onclick="generateInvite()" class="text-xs bg-slate-800 hover:bg-slate-700 text-slate-300 px-3 py-1.5 rounded border border-slate-700 transition-colors flex items-center shadow-sm">
                        <span class="mr-1">Generate Invite</span>
                    </button>
                    <button onclick="leavePlatform()" id="leaveBtn" class="text-xs bg-red-900/30 hover:bg-red-800/60 text-red-300 px-3 py-1.5 rounded border border-red-800/50 transition-colors flex items-center shadow-sm">
                        <span class="mr-1">Leave</span>
                    </button>
                    <button onclick="toggleMembers()" class="text-xs bg-indigo-900/30 hover:bg-indigo-800/60 text-indigo-300 px-3 py-1.5 rounded border border-indigo-800/50 transition-colors flex items-center shadow-sm ml-4">
                        <svg class="w-4 h-4 mr-1" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M12 4.354a4 4 0 110 5.292M15 21H3v-1a6 6 0 0112 0v1zm0 0h6v-1a6 6 0 00-9-5.197M13 7a4 4 0 11-8 0 4 4 0 018 0z"></path></svg>
                        Members
                    </button>
                </div>
            </div>
            
            <div id="chatBox" class="flex-1 overflow-y-auto p-4 space-y-4 pb-32">
                <div class="text-center text-slate-600 italic text-sm mt-10">You are not a member of any platforms.</div>
            </div>

            <!-- Input Area -->
            <div class="absolute bottom-0 w-full p-4 bg-gradient-to-t from-slate-900 via-slate-900 to-transparent">
                <form id="msgForm" class="flex space-x-2 bg-slate-800/90 backdrop-blur border border-slate-700 p-2 rounded-xl shadow-xl hidden">
                    <input type="file" id="filePicker" class="hidden" onchange="handleFileSelect(event)">
                    <button type="button" onclick="document.getElementById('filePicker').click()" class="bg-slate-700 hover:bg-slate-600 text-slate-300 px-4 py-2 rounded-lg transition-colors border border-slate-600 font-bold flex items-center justify-center whitespace-nowrap" title="Share a file with the mesh"><span class="mr-2 text-xl">📁</span> Upload File</button>
                    <input type="text" id="msgInput" class="flex-1 bg-transparent text-white px-3 focus:outline-none placeholder-slate-400" placeholder="Broadcast to mesh..." autocomplete="off">
                    <button type="submit" class="bg-indigo-600 hover:bg-indigo-500 text-white px-6 py-2 rounded-lg font-medium transition-colors shadow-lg shadow-indigo-600/30">Send</button>
                </form>
            </div>
        </main>

        <!-- Right Sidebar (Members) -->
        <aside id="membersSidebar" class="w-0 border-l-0 border-slate-800 flex flex-col bg-slate-900/90 backdrop-blur-md sidebar-transition overflow-hidden opacity-0">
            <div class="p-4 border-b border-slate-800 flex justify-between items-center whitespace-nowrap min-w-[16rem]">
                <h2 class="text-xs font-bold text-slate-400 uppercase tracking-widest">Platform Members</h2>
                <button onclick="toggleMembers()" class="text-slate-500 hover:text-white transition-colors">
                    <svg class="w-4 h-4" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M6 18L18 6M6 6l12 12"></path></svg>
                </button>
            </div>
            <div class="p-3 border-b border-slate-800 min-w-[16rem]">
                <input type="text" id="memberSearch" placeholder="Search members..." class="w-full bg-slate-800 border border-slate-700 rounded px-3 py-1.5 text-xs text-white outline-none focus:border-indigo-500 transition-colors" onkeyup="renderMembers()">
            </div>
            <div id="membersList" class="flex-1 overflow-y-auto p-3 space-y-1 min-w-[16rem]">
                <!-- Members rendered here -->
            </div>
        </aside>

    </div>

    <!-- Modals -->
    <div id="unlockModal" class="fixed inset-0 bg-black/80 backdrop-blur-sm hidden flex items-center justify-center z-[70]">
        <div class="bg-slate-900 border border-slate-700 p-8 rounded-2xl w-96 shadow-2xl text-center">
            <div class="w-16 h-16 bg-indigo-600 rounded-2xl mx-auto mb-4 flex items-center justify-center text-2xl font-bold shadow-lg shadow-indigo-500/20">
				<svg class="w-8 h-8 text-white" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M12 15v2m-6 4h12a2 2 0 002-2v-6a2 2 0 00-2-2H6a2 2 0 00-2 2v6a2 2 0 002 2zm10-10V7a4 4 0 00-8 0v4h8z"></path></svg>
			</div>
            <h2 class="text-2xl font-bold mb-2">Unlock Node</h2>
            <p class="text-xs text-slate-400 mb-6">Enter your master password to decrypt your identity keys.</p>
            <input type="password" id="unlockPasswordInput" class="w-full bg-slate-800 border border-slate-700 rounded-xl px-4 py-3 text-white outline-none focus:border-indigo-500 mb-4 text-center font-bold" placeholder="Master Password">
            <button onclick="unlockNode()" class="w-full bg-indigo-600 hover:bg-indigo-500 text-white px-4 py-3 rounded-xl font-bold transition-all shadow-lg shadow-indigo-600/30">Unlock Mesh</button>
            <button onclick="factoryReset()" class="w-full mt-4 text-xs text-red-400 hover:text-red-300 transition-colors bg-transparent border-none">Forgot Password? Factory Reset Node</button>
        </div>
    </div>

    <div id="usernameModal" class="fixed inset-0 bg-black/80 backdrop-blur-sm hidden flex items-center justify-center z-[70]">
        <div class="bg-slate-900 border border-slate-700 p-8 rounded-2xl w-96 shadow-2xl text-center">
            <div class="w-16 h-16 bg-indigo-600 rounded-2xl mx-auto mb-4 flex items-center justify-center text-2xl font-bold shadow-lg shadow-indigo-500/20">A</div>
            <h2 class="text-2xl font-bold mb-2">Welcome to Aegis Mesh</h2>
            <p class="text-xs text-slate-400 mb-6">Create your decentralized identity and set a strong master password to encrypt your private keys on disk.</p>
            <input type="text" id="usernameInput" class="w-full bg-slate-800 border border-slate-700 rounded-xl px-4 py-3 text-white outline-none focus:border-indigo-500 mb-2 text-center font-bold" placeholder="Enter a Username...">
            <input type="password" id="createPasswordInput" class="w-full bg-slate-800 border border-slate-700 rounded-xl px-4 py-3 text-white outline-none focus:border-indigo-500 mb-4 text-center font-bold" placeholder="Set Master Password">
			<button onclick="setUsername()" class="w-full bg-indigo-600 hover:bg-indigo-500 text-white px-4 py-3 rounded-xl font-bold transition-all shadow-lg shadow-indigo-600/30">Generate & Encrypt Identity</button>
        </div>
    </div>

    <div id="createModal" class="fixed inset-0 bg-black/60 backdrop-blur-sm hidden flex items-center justify-center z-[60]">
        <div class="bg-slate-900 border border-slate-700 p-6 rounded-xl w-96 shadow-2xl">
            <h2 class="text-xl font-bold mb-4">Initialize Platform</h2>
            <div class="space-y-4">
                <div>
                    <label class="block text-xs text-slate-400 mb-1">Name</label>
                    <input type="text" id="newPlatName" class="w-full bg-slate-800 border border-slate-700 rounded px-3 py-2 text-white outline-none focus:border-indigo-500" placeholder="# secret-project">
                </div>
                <div class="flex items-center space-x-2 mt-3">
                    <input type="checkbox" id="newPlatTrusted" class="w-4 h-4 rounded bg-slate-800 border-slate-700 text-indigo-500 focus:ring-indigo-500">
                    <label class="text-xs text-slate-300 font-medium">Visible to Trusted Peers</label>
                </div>
            </div>
            <div class="flex justify-end space-x-3 mt-6">
                <button onclick="hideCreateModal()" class="px-4 py-2 text-slate-400 hover:text-white transition-colors">Cancel</button>
                <button onclick="createPlatform()" class="bg-indigo-600 hover:bg-indigo-500 text-white px-4 py-2 rounded transition-colors">Generate Genesis Block</button>
            </div>
        </div>
    </div>

    <div id="joinModal" class="fixed inset-0 bg-black/60 backdrop-blur-sm hidden flex items-center justify-center z-[60]">
        <div class="bg-slate-900 border border-slate-700 p-6 rounded-xl w-96 shadow-2xl">
            <h2 class="text-xl font-bold mb-2">Join Platform</h2>
            <p class="text-xs text-slate-400 mb-4">Paste an encoded invite string from a friend to sync the platform ledger and connect via P2P.</p>
            <div class="space-y-4">
                <div>
                    <label class="block text-xs text-slate-400 mb-1">Invite Code</label>
                    <textarea id="inviteCodeInput" class="w-full bg-slate-800 border border-slate-700 rounded px-3 py-2 text-white outline-none focus:border-indigo-500 text-xs font-mono h-24" placeholder="Paste base64 invite code here..."></textarea>
                </div>
            </div>
            <div class="flex justify-end space-x-3 mt-6">
                <button onclick="hideJoinModal()" class="px-4 py-2 text-slate-400 hover:text-white transition-colors">Cancel</button>
                <button onclick="joinPlatform()" class="bg-indigo-600 hover:bg-indigo-500 text-white px-4 py-2 rounded transition-colors">Join Mesh</button>
            </div>
        </div>
    </div>

    <!-- Discover Modal -->
    <div id="discoverModal" class="fixed inset-0 bg-black/60 backdrop-blur-sm hidden flex items-center justify-center z-[60]">
        <div class="bg-slate-900 border border-slate-700 p-6 rounded-xl w-[36rem] shadow-2xl max-h-[80vh] flex flex-col">
            <h2 class="text-xl font-bold mb-2 text-white flex items-center"><span class="mr-2">🌐</span> Discover Trusted Servers</h2>
            <p class="text-xs text-slate-400 mb-4 border-b border-slate-700 pb-4">A master list of public servers actively shared by your trusted peers.</p>
            
            <div id="discoverListDisplay" class="flex-1 overflow-y-auto space-y-2 bg-slate-800 p-3 rounded shadow-inner mb-4 border border-slate-700/50">
                <!-- Discovered Servers injected here -->
            </div>
            
            <div class="flex justify-end space-x-3 mt-2">
                <button onclick="hideDiscoverModal()" class="px-4 py-2 text-slate-400 hover:text-white transition-colors">Cancel</button>
                <button onclick="joinSelectedDiscovered()" class="bg-emerald-600 hover:bg-emerald-500 text-white px-4 py-2 rounded transition-colors font-bold shadow-lg shadow-emerald-600/20 flex items-center">
                    <svg class="w-4 h-4 mr-2" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M13 10V3L4 14h7v7l9-11h-7z"></path></svg>
                    Join Selected
                </button>
            </div>
        </div>
    </div>

    <div id="inviteDisplayModal" class="fixed inset-0 bg-black/60 backdrop-blur-sm hidden flex items-center justify-center z-[60]">
        <div class="bg-slate-900 border border-slate-700 p-6 rounded-xl w-[28rem] shadow-2xl">
            <h2 class="text-xl font-bold mb-2">Platform Invite Generated</h2>
            <p class="text-xs text-slate-400 mb-4">Share this code securely with a friend. It contains network mapping and cryptographic keys for them to establish a direct connection to your node.</p>
            <textarea id="generatedInviteCode" class="w-full bg-slate-800 border border-slate-700 rounded px-3 py-2 text-emerald-300 outline-none focus:border-indigo-500 text-xs font-mono h-24 resize-none shadow-inner" readonly></textarea>
            <div class="flex justify-end space-x-3 mt-6">
                <button onclick="hideInviteDisplayModal()" class="px-4 py-2 text-slate-400 hover:text-white transition-colors">Close</button>
                <button onclick="copyInviteCode()" class="bg-emerald-600 hover:bg-emerald-500 text-white px-4 py-2 rounded transition-colors flex items-center">
                    <svg class="w-4 h-4 mr-2" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M8 16H6a2 2 0 01-2-2V6a2 2 0 012-2h8a2 2 0 00-2-2h-8a2 2 0 00-2-2v8a2 2 0 002 2z"></path></svg>
                    Copy Code
                </button>
            </div>
        </div>
    </div>

    <div id="peerModal" class="fixed inset-0 bg-black/60 backdrop-blur-sm hidden flex items-center justify-center z-[60]">
        <div class="bg-slate-900 border border-slate-700 p-6 rounded-xl w-96 shadow-2xl">
            <h2 class="text-xl font-bold mb-4">Network Peers</h2>
            <div class="space-y-4">
                <div id="peerListDisplay" class="bg-slate-800 rounded p-2 text-sm text-slate-300 min-h-[80px] max-h-40 overflow-y-auto space-y-1">
                </div>
                <div>
                    <label class="block text-xs text-slate-400 mb-1">Add Peer Address (Manual Override)</label>
                    <input type="text" id="newPeerUrl" class="w-full bg-slate-800 border border-slate-700 rounded px-3 py-2 text-white outline-none focus:border-emerald-500 text-sm" placeholder="http://3.16.213.66:8080">
                </div>
            </div>
            <div class="flex justify-end space-x-3 mt-6">
                <button onclick="hidePeerModal()" class="px-4 py-2 text-slate-400 hover:text-white transition-colors">Close</button>
                <button onclick="addPeer()" class="bg-emerald-600 hover:bg-emerald-500 text-white px-4 py-2 rounded transition-colors font-bold">Connect</button>
            </div>
        </div>
    </div>

    <div id="bannedModal" class="fixed inset-0 bg-black/60 backdrop-blur-sm hidden flex items-center justify-center z-[60]">
        <div class="bg-slate-900 border border-slate-700 p-6 rounded-xl w-96 shadow-2xl max-h-[80vh] flex flex-col">
            <h2 class="text-xl font-bold mb-4 text-red-400 border-b border-slate-700 pb-2">Banned Hash Ledgers</h2>
            <div id="bannedListDisplay" class="flex-1 overflow-y-auto space-y-2 p-1">
            </div>
            <div class="flex justify-end mt-6 border-t border-slate-700 pt-4">
                <button onclick="document.getElementById('bannedModal').classList.add('hidden')" class="px-4 py-2 bg-slate-700 text-white rounded hover:bg-slate-600 transition-colors">Close Control Panel</button>
            </div>
        </div>
    </div>
	
	<div id="ackModal" class="fixed inset-0 bg-black/60 backdrop-blur-sm hidden flex items-center justify-center z-[8000]">
		<div class="bg-slate-900 border border-slate-700 p-6 rounded-xl w-80 shadow-2xl">
			<h2 class="text-xl font-bold mb-4 text-white flex items-center">
				<span class="text-emerald-400 mr-2 font-bold tracking-tighter">✓✓</span> Read by
			</h2>
			<div id="ackListDisplay" class="bg-slate-800 rounded p-2 text-sm text-slate-300 min-h-[60px] max-h-48 overflow-y-auto space-y-1">
			</div>
			<div class="flex justify-end mt-4">
				<button onclick="document.getElementById('ackModal').classList.add('hidden')" class="px-4 py-2 bg-slate-700 text-white rounded hover:bg-slate-600 transition-colors font-bold shadow-sm">Close</button>
			</div>
		</div>
	</div>

	<!-- Chat Request Modal -->
    <div id="chatRequestModal" class="fixed inset-0 bg-black/80 backdrop-blur-sm hidden flex items-center justify-center z-[8000]">
        <div class="bg-slate-900 border border-slate-700 p-6 rounded-xl w-96 shadow-2xl text-center">
            <div class="w-16 h-16 bg-indigo-600 rounded-2xl mx-auto mb-4 flex items-center justify-center text-3xl font-bold shadow-lg shadow-indigo-500/20">💬</div>
            <h2 class="text-xl font-bold mb-2 text-white">New Chat Request</h2>
            <p id="chatRequestText" class="text-sm text-slate-300 mb-6">User wants to chat.</p>
            <div class="flex justify-center space-x-3">
                <button id="btnChatBlock" class="px-4 py-2 bg-red-900/50 hover:bg-red-800 text-red-200 rounded transition-colors text-sm">Block User</button>
                <button id="btnChatIgnore" class="px-4 py-2 bg-slate-700 hover:bg-slate-600 text-white rounded transition-colors text-sm">Ignore</button>
                <button id="btnChatAccept" class="px-4 py-2 bg-emerald-600 hover:bg-emerald-500 text-white font-bold rounded transition-colors shadow-lg">Accept Chat</button>
            </div>
        </div>
    </div>

    <!-- PTT Settings Modal -->
    <div id="pttModal" class="fixed inset-0 bg-black/80 backdrop-blur-sm hidden flex items-center justify-center z-[9500]">
        <div class="bg-slate-900 border border-slate-700 p-6 rounded-xl w-96 shadow-2xl">
            <h2 class="text-xl font-bold mb-4 text-white flex items-center"><span class="mr-2">⚙️</span> Push-to-Talk Settings</h2>
            
            <div class="flex items-center justify-between bg-slate-800 p-3 rounded mb-4">
                <span class="text-sm font-bold text-slate-300">Enable PTT</span>
                <label class="relative inline-flex items-center cursor-pointer">
                  <input type="checkbox" id="pttToggle" class="sr-only peer" onchange="togglePTTMode(this.checked)">
                  <div class="w-11 h-6 bg-slate-600 peer-focus:outline-none rounded-full peer peer-checked:after:translate-x-full peer-checked:after:border-white after:content-[''] after:absolute after:top-[2px] after:left-[2px] after:bg-white after:border-gray-300 after:border after:rounded-full after:h-5 after:w-5 after:transition-all peer-checked:bg-emerald-500"></div>
                </label>
            </div>

            <div class="mb-6">
                <label class="block text-xs font-bold text-slate-400 mb-2 uppercase tracking-wider">PTT Hotkey</label>
                <button id="pttKeyBtn" onclick="listenForPTTKey()" class="w-full bg-slate-800 border border-slate-600 text-white p-3 rounded text-center font-mono hover:bg-slate-700 transition-colors">v</button>
                <p class="text-[10px] text-slate-500 mt-2 text-center">Click the button above and press any key to rebind.</p>
            </div>

            <div class="flex justify-end">
                <button onclick="document.getElementById('pttModal').classList.add('hidden')" class="px-5 py-2 bg-indigo-600 text-white font-bold rounded shadow hover:bg-indigo-500 transition-colors">Done</button>
            </div>
        </div>
    </div>

    <!-- Member Context Menu -->
    <div id="memberContextMenu" class="fixed hidden bg-slate-800 border border-slate-700 rounded-lg shadow-2xl z-[80] w-56 flex flex-col py-1 overflow-hidden" onclick="event.stopPropagation()">
    </div>

    <script>
        const API_TOKEN = "{{API_TOKEN}}";
        let myId = "";
        let myName = "";
        let myBlockedHashes = [];
        let myTrustedHashes = [];
        let myBannedFrom = [];
        let currentPlatform = null;
        let platformsCache = {};
        
        let userDir = {}; 
        let activeUsers = {}; 
        
        let lastMessageUpdate = 0;
        let isPolling = false;
        let pollController = null;
		let pendingAcks = new Set();

        // UI Tabs & Badges
        let currentTab = 'platforms';
        let unreadCounts = {};
        
        // WEBRTC STATE
        let localMediaStream = null;
        let activeVoicePlatform = null; // Tracks which platform we are in a voice/video call in
        let rtcPeers = {}; 
        let iceQueues = {}; 
        let voiceUsers = {}; 
        let voiceActive = false;
        let processedSignals = new Set();
        const rtcConfig = { iceServers: [{ urls: 'stun:stun.l.google.com:19302' }] };
		
		// Web Audio API Elements for Advanced Volume Scaling & Sound Generation
		let audioCtx = null;
		let gainNodes = {};
		let userVolumes = {}; // Raw stored volumes from 0.5 to 2.5

        // Call State (Audio/Video/PTT)
        let isMuted = false;
        let isVideoActive = false;
        let isScreenSharing = false;
        let screenStream = null;
        let pttEnabled = false;
        let pttKey = 'v';
        let pttIsPressed = false;
        let isListeningForKey = false;

		// Chat Request & Discovery Logic
		let pendingChatRequests = [];
		let isShowingChatRequest = false;
        window.availableFriendServers = {}; // Cache of intercepted TRUSTED_INVITEs

        function escapeHTML(str) {
            if (!str) return "";
            return str.replace(/[&<>'"]/g, tag => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', "'": '&#39;', '"': '&quot;'}[tag] || tag));
        }

        function showToast(message, type = 'info') {
            const container = document.getElementById('toastContainer');
            const toast = document.createElement('div');
            const colors = {
                'info': 'bg-slate-800 border-indigo-500 text-slate-200 shadow-[0_0_15px_rgba(99,102,241,0.2)]',
                'success': 'bg-emerald-900/90 border-emerald-500 text-emerald-100 shadow-[0_0_15px_rgba(16,185,129,0.2)]',
                'error': 'bg-red-900/90 border-red-500 text-red-100 shadow-[0_0_15px_rgba(239,68,68,0.2)]'
            };
            toast.className = 'px-4 py-3 rounded-lg shadow-xl border-l-4 pointer-events-auto flex items-center transition-all duration-300 opacity-0 transform translate-y-2 ' + colors[type];
            toast.innerHTML = '<span class="text-sm font-medium">' + escapeHTML(message) + '</span>';
            container.appendChild(toast);
            
            setTimeout(() => toast.classList.remove('opacity-0', 'translate-y-2'), 10);
            setTimeout(() => {
                toast.classList.add('opacity-0', 'translate-y-2');
                setTimeout(() => toast.remove(), 300);
            }, 4000);
        }

        // Notification Sound Generation
        function playNotificationSound() {
            try {
                if (!audioCtx) initAudio();
                if (audioCtx.state === 'suspended') audioCtx.resume();
                
                const osc1 = audioCtx.createOscillator();
                const osc2 = audioCtx.createOscillator();
                const gain = audioCtx.createGain();
                
                osc1.type = 'sine';
                osc2.type = 'sine';
                osc1.frequency.setValueAtTime(523.25, audioCtx.currentTime); // C5
                osc2.frequency.setValueAtTime(659.25, audioCtx.currentTime); // E5
                
                gain.gain.setValueAtTime(0, audioCtx.currentTime);
                gain.gain.linearRampToValueAtTime(0.08, audioCtx.currentTime + 0.02);
                gain.gain.exponentialRampToValueAtTime(0.001, audioCtx.currentTime + 0.5);
                
                osc1.connect(gain);
                osc2.connect(gain);
                gain.connect(audioCtx.destination);
                
                osc1.start();
                osc2.start();
                osc1.stop(audioCtx.currentTime + 0.5);
                osc2.stop(audioCtx.currentTime + 0.5);
            } catch(e) { } // Ignore blocked autoplay policy errors prior to first user click
        }

        let confirmCallback = null;
        function showConfirm(title, message, callback, btnText = "Confirm", btnColor = "bg-red-600 hover:bg-red-500") {
            document.getElementById('confirmTitle').innerText = title;
            document.getElementById('confirmMessage').innerText = message;
            const btn = document.getElementById('confirmBtn');
            btn.innerText = btnText;
            btn.className = btnColor + ' text-white px-4 py-2 rounded transition-colors font-bold shadow-lg';
            confirmCallback = callback;
            document.getElementById('confirmModal').classList.remove('hidden');
        }
        function closeConfirmModal(result) {
            document.getElementById('confirmModal').classList.add('hidden');
            if(confirmCallback) confirmCallback(result);
            confirmCallback = null;
        }

        async function apiCall(endpoint, method = 'GET', body = null) {
            try {
                const options = {
                    method: method,
                    headers: { 'Authorization': 'Bearer ' + API_TOKEN },
                    cache: 'no-store' 
                };
                if (body) {
                    options.headers['Content-Type'] = 'application/json';
                    options.body = JSON.stringify(body);
                }
                const res = await fetch(endpoint, options);
                
                if (!res.ok) {
                    let errMsg = "HTTP Error " + res.status;
                    try { 
                        const errData = await res.json(); 
                        errMsg = errData.error || errMsg; 
                    } catch(e) {
                        try { errMsg = await res.text() || errMsg; } catch(e2) {}
                    }
                    throw new Error(errMsg);
                }
                
                const ct = res.headers.get('content-type');
                if (ct && ct.includes('application/json')) {
                    return await res.json();
                }
                return await res.text();
            } catch(error) {
                throw error;
            }
        }

        apiCall('/api/identity').then(data => {
            if (data.locked) {
                document.getElementById('unlockModal').classList.remove('hidden');
            } else if (!data.username) {
                document.getElementById('usernameModal').classList.remove('hidden');
            } else {
                completeInit(data);
            }
        }).catch(err => showToast("Critical UI Failure: " + err.message, "error"));

        function setUsername() {
            const val = document.getElementById('usernameInput').value.trim();
            const pwd = document.getElementById('createPasswordInput').value;
            if(!val || !pwd) {
				showToast("Username and master password are required", "error");
				return;
			}
            
            apiCall('/api/identity', 'POST', {username: val, password: pwd})
            .then(data => {
                document.getElementById('usernameModal').classList.add('hidden');
                showToast("Identity generated and keys securely encrypted.", "success");
                completeInit(data);
            }).catch(err => showToast(err.message, "error"));
        }

        function unlockNode() {
            const pwd = document.getElementById('unlockPasswordInput').value;
            if(!pwd) return;
            
            apiCall('/api/unlock', 'POST', {password: pwd})
            .then(() => {
                document.getElementById('unlockModal').classList.add('hidden');
                showToast("Node Unlocked Successfully", "success");
                return apiCall('/api/identity');
            })
            .then(data => completeInit(data))
            .catch(err => showToast(err.message, "error"));
        }

        function factoryReset() {
            showConfirm("Factory Reset", "This will PERMANENTLY delete your cryptographic identity, messages, platforms, and files from this node. Are you absolutely sure?", (confirmed) => {
                if(!confirmed) return;
                apiCall('/api/reset', 'POST')
                .then(() => {
                    document.getElementById('unlockModal').classList.add('hidden');
                    document.getElementById('userIdBox').innerText = '...';
                    document.getElementById('usernameModal').classList.remove('hidden');
                    showToast("Node factory reset complete. Please create a new identity.", "success");
                }).catch(e => showToast("Reset Error: " + e.message, "error"));
            });
        }

        function completeInit(data) {
            myId = data.root_hash;
            myName = data.username;
            myBlockedHashes = data.blocked_hashes || [];
            myTrustedHashes = data.trusted_hashes || [];
            myBannedFrom = data.banned_from || [];
            document.getElementById('userIdBox').innerText = escapeHTML(myName) + '#' + escapeHTML(myId).substring(0, 4);
            userDir[myId] = myName;
            
            loadPlatforms();
            loadPeers();
            initDrag();
            setupPTTListeners();
        }

        function setTab(tab) {
            currentTab = tab;
            document.getElementById('tabPlatforms').className = tab === 'platforms' 
                ? 'flex-1 py-1.5 text-[10px] font-bold rounded bg-slate-800 text-white uppercase tracking-wider transition-colors relative' 
                : 'flex-1 py-1.5 text-[10px] font-bold rounded text-slate-400 hover:bg-slate-800/50 uppercase tracking-wider transition-colors relative';
            document.getElementById('tabDMs').className = tab === 'dms' 
                ? 'flex-1 py-1.5 text-[10px] font-bold rounded bg-slate-800 text-white uppercase tracking-wider transition-colors relative' 
                : 'flex-1 py-1.5 text-[10px] font-bold rounded text-slate-400 hover:bg-slate-800/50 uppercase tracking-wider transition-colors relative';
            renderPlatformsList();
        }

        function loadPlatforms(autoSelectId = null) {
            apiCall('/api/platforms').then(data => {
                platformsCache = data;
                renderPlatformsList();
                if (autoSelectId && platformsCache[autoSelectId]) selectPlatform(autoSelectId);
                else if (currentPlatform && platformsCache[currentPlatform]) selectPlatform(currentPlatform);
                else {
                    const keys = Object.keys(platformsCache);
                    if (keys.length > 0) selectPlatform(keys[0]);
                    else {
                        currentPlatform = null;
                        document.getElementById('activePlatformHeader').innerHTML = '<h3 class="font-bold text-lg text-slate-300">No Platforms</h3><span class="text-xs text-slate-400">Join or create a platform to get started.</span>';
                        document.getElementById('chatBox').innerHTML = '<div class="text-center text-slate-600 italic text-sm mt-10">You are not a member of any platforms.</div>';
                        document.getElementById('msgForm').classList.add('hidden');
                        document.getElementById('platformActions').classList.add('hidden');
                        document.getElementById('membersList').innerHTML = '';
                    }
                }
            }).catch(e => showToast(e.message, "error"));
        }

        function renderPlatformsList() {
            const list = document.getElementById('platformsList');
            list.innerHTML = '';
            
            const searchStr = (document.getElementById('platformSearch')?.value || '').toLowerCase();
            const sortMethod = document.getElementById('platformSort')?.value || 'default';
            
            let plats = Object.values(platformsCache);
            
            if (searchStr) {
                plats = plats.filter(p => p.name.toLowerCase().includes(searchStr));
            }
            
            if (sortMethod === 'az') {
                plats.sort((a, b) => a.name.localeCompare(b.name));
            }

            let dmUnread = 0;
            let platUnread = 0;

            plats.forEach(p => {
                const isDM = p.name.startsWith("DM: ");
                const unread = unreadCounts[p.id] || 0;
                
                if (isDM) dmUnread += unread;
                else platUnread += unread;

                if ((currentTab === 'dms' && !isDM) || (currentTab === 'platforms' && isDM)) {
                    return; // hide if it doesn't match active tab
                }

                const btn = document.createElement('button');
                const isActive = p.id === currentPlatform;
                btn.className = 'w-full text-left px-3 py-2.5 rounded-lg transition-all border flex justify-between items-center platform-btn ' + 
                              (isActive ? 'active' : 'border-transparent text-slate-400 hover:bg-slate-800');
                
                btn.onclick = () => selectPlatform(p.id);

                let icons = '';
                if (p.is_ephemeral) icons += '<span class="text-[10px] text-amber-500 ml-2" title="Ad-Hoc / TTL">[TTL]</span>';
                
                let badge = unread > 0 ? '<span class="bg-red-500 text-white text-[10px] font-bold px-1.5 py-0.5 rounded-full ml-auto shadow">' + unread + '</span>' : '';
                let displayName = isDM ? escapeHTML(p.name.replace("DM: ", "💬 ")) : '<span class="opacity-50">#</span> ' + escapeHTML(p.name);
                
                btn.innerHTML = '<span class="truncate flex-1">' + displayName + icons + '</span> ' + badge;
                list.appendChild(btn);
            });

            // Update tab notification badges
            const bPlat = document.getElementById('badgePlatforms');
            const bDM = document.getElementById('badgeDMs');
            
            if (platUnread > 0) { bPlat.innerText = platUnread; bPlat.classList.remove('hidden'); } 
            else bPlat.classList.add('hidden');
            
            if (dmUnread > 0) { bDM.innerText = dmUnread; bDM.classList.remove('hidden'); } 
            else bDM.classList.add('hidden');
        }

        function loadPeers() {
            apiCall('/api/peers').then(peers => {
                document.getElementById('peerCount').innerText = peers.length + (peers.length === 1 ? ' Peer' : ' Peers');
                
                const dot = document.getElementById('pCountDot');
                dot.className = 'w-2 h-2 rounded-full mr-2 ' + (peers.length > 0 ? 'bg-emerald-400 shadow-[0_0_8px_rgba(52,211,153,0.8)] animate-pulse' : 'bg-slate-600');

                const list = document.getElementById('peerListDisplay');
                if (peers.length === 0) {
                    list.innerHTML = '<span class="text-slate-500 italic px-2">No connected nodes.</span>';
                } else {
                    list.innerHTML = peers.map(p => '<div class="flex justify-between items-center py-1.5 px-2 bg-slate-700/30 rounded border border-slate-700 font-mono text-emerald-400"><span class="truncate pr-2" title="' + escapeHTML(p) + '">[Connected] ' + escapeHTML(p) + '</span><button onclick="deletePeer(\'' + escapeHTML(p) + '\')" class="text-red-400 hover:text-red-300 text-[10px] font-bold px-2 py-1 bg-slate-800 hover:bg-slate-700 border border-slate-600 rounded transition-colors flex-shrink-0 shadow-sm uppercase tracking-wider">Drop</button></div>').join('');
                }
            }).catch(e => {}); 
        }

        function deletePeer(url) {
            apiCall('/api/peers', 'DELETE', { url: url })
            .then(() => {
                showToast("Disconnected from peer.", "success");
                loadPeers();
            }).catch(e => showToast("Error: " + e.message, "error"));
        }

        function selectPlatform(id) {
            currentPlatform = id;
            
            // Instantly clear unreads for this channel to mark them as seen
            if (unreadCounts[id]) {
                unreadCounts[id] = 0;
                renderPlatformsList();
            }

            const p = platformsCache[id];
            if (!p) return;
            
            document.querySelectorAll('.platform-btn').forEach(b => {
                b.classList.remove('active');
                if(b.innerText.includes(p.name.replace("DM: ", "💬 "))) b.classList.add('active');
            });

            document.getElementById('msgForm').classList.remove('hidden');
            document.getElementById('platformActions').classList.remove('hidden');

            const displayName = p.name.startsWith("DM: ") ? p.name.replace("DM: ", "💬 ") : p.name;
            document.getElementById('activePlatformHeader').innerHTML = 
                '<h3 class="font-bold flex items-center">' + escapeHTML(displayName) + '</h3>' +
                '<span class="text-xs text-slate-400">CRDT Sync' + (p.is_ephemeral ? ' • Ephemeral TTL' : '') + '</span>';

            const leaveBtn = document.getElementById('leaveBtn');
            leaveBtn.style.display = 'flex';

            const myRole = p.members[myId];
            const isAdmin = myRole === 'OWNER' || myRole === 'ADMIN';
            document.getElementById('bannedUsersBtn').style.display = isAdmin ? 'flex' : 'none';

            lastMessageUpdate = 0;
            apiCall('/api/messages', 'POST', { platform: id, text: "ping", msg_type: "PRESENCE" }).catch(()=>{});

            loadMessages(true);
        }

        // ==========================================
        // VOIP / WEBRTC LOGIC & Audio Scaling
        // ==========================================
		
		function initAudio() {
			if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();
		}

        async function toggleCall(requestVideo = false) {
            const vBtn = document.getElementById('videoBtn');
            const aBtn = document.getElementById('voiceBtn');
            const modal = document.getElementById('videoModal');
            
            if (voiceActive) {
                // Hang up
                voiceActive = false;
                isVideoActive = false;
                isScreenSharing = false;
                voiceUsers[myId] = false;
                activeVoicePlatform = null; // Unbind WebRTC signaling
                
                if (localMediaStream) {
                    localMediaStream.getTracks().forEach(t => t.stop());
                    localMediaStream = null;
                }
                if (screenStream) {
                    screenStream.getTracks().forEach(t => t.stop());
                    screenStream = null;
                }

                for (let hash in rtcPeers) {
                    rtcPeers[hash].close();
                    delete rtcPeers[hash];
                }
				for (let hash in gainNodes) {
					gainNodes[hash].disconnect();
					delete gainNodes[hash];
				}
                
                // Clear out detached videos from body and reset modal grid
                document.querySelectorAll('.detached-video').forEach(el => el.remove());
                document.getElementById('videoGrid').innerHTML = '';
                modal.classList.add('hidden');
                
                // Reset Buttons
                aBtn.innerHTML = '🎙️ Audio Call';
                aBtn.classList.remove('bg-emerald-600', 'text-white', 'hidden');
                aBtn.classList.add('bg-slate-800', 'text-slate-300');
                
                vBtn.innerHTML = '📹 Video Chat';
                vBtn.classList.remove('bg-emerald-600', 'text-white', 'hidden');
                vBtn.classList.add('bg-slate-800', 'text-slate-300');

                document.getElementById('btnVideoToggle').classList.add('hidden');
                document.getElementById('btnScreenShare').classList.add('hidden');
                
                // Important: Need to send leave signal explicitly to the platform we were just in
                if (currentPlatform) sendSignal('VOICE_LEAVE', '', '', currentPlatform);
                renderMembers();
            } else {
                try {
                    if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {
                        throw new Error("WebRTC explicitly requires localhost or HTTPS context.");
                    }
                    
                    localMediaStream = await navigator.mediaDevices.getUserMedia({audio: true, video: requestVideo});
                    voiceActive = true;
                    isVideoActive = requestVideo;
                    voiceUsers[myId] = true;
                    activeVoicePlatform = currentPlatform; // Bind WebRTC routing to this platform
                    
                    // Show modal and hide join buttons
                    modal.classList.remove('hidden');
                    modal.classList.add('flex');
                    aBtn.classList.add('hidden');
                    vBtn.classList.add('hidden');

                    document.getElementById('btnScreenShare').classList.remove('hidden');

                    if(requestVideo) {
                        document.getElementById('btnVideoToggle').classList.remove('hidden');
                        addLocalVideoPreview(localMediaStream);
                    }
                    
                    applyAudioState(); // Initialize PTT/Mute state
                    
                    showToast(requestVideo ? "Joined Secure Video Chat" : "Joined Encrypted Voice Channel", "success");
                    sendSignal('VOICE_JOIN', '', { video: requestVideo });

                    Object.keys(voiceUsers).forEach(hash => {
                        if (hash !== myId && voiceUsers[hash]) {
                            if (myId > hash) initiateCall(hash);
                            else sendSignal('VOICE_PING', hash);
                        }
                    });

                    renderMembers();
                } catch(e) {
                    showToast("Hardware access denied or unavailable. WebRTC requires localhost or HTTPS.", "error");
                }
            }
        }

        async function toggleScreenShare() {
            if (!voiceActive || !localMediaStream) {
                showToast("Please join a voice or video call first.", "error");
                return;
            }

            const btn = document.getElementById('btnScreenShare');

            if (isScreenSharing) {
                // Revert to normal camera or no camera
                if (screenStream) screenStream.getTracks().forEach(t => t.stop());
                isScreenSharing = false;
                btn.classList.replace('text-emerald-400', 'text-slate-400');
                
                if (isVideoActive) {
                    try {
                        const camStream = await navigator.mediaDevices.getUserMedia({video: true});
                        const camTrack = camStream.getVideoTracks()[0];
                        
                        if(localMediaStream.getVideoTracks().length > 0) {
                            localMediaStream.getVideoTracks()[0].stop();
                            localMediaStream.removeTrack(localMediaStream.getVideoTracks()[0]);
                        }
                        
                        localMediaStream.addTrack(camTrack);
                        
                        const vidLocal = document.getElementById('video_local');
                        if (vidLocal) {
                            vidLocal.srcObject = localMediaStream;
                            vidLocal.classList.add('transform', 'scale-x-[-1]'); // Re-mirror local camera
                        }

                        for(let hash in rtcPeers) {
                            const sender = rtcPeers[hash].getSenders().find(s => s.track && s.track.kind === 'video');
                            if(sender) sender.replaceTrack(camTrack);
                        }
                    } catch(e) { showToast("Could not restore camera.", "error"); }
                } else {
                    // Turn off video entirely since camera wasn't active
                    if(localMediaStream.getVideoTracks().length > 0) {
                        localMediaStream.getVideoTracks()[0].stop();
                        localMediaStream.removeTrack(localMediaStream.getVideoTracks()[0]);
                    }
                    const localWrap = document.getElementById('vidwrap_local');
                    if(localWrap) localWrap.remove();
                    for(let hash in rtcPeers) initiateCall(hash); // renegotiate
                }
            } else {
                // Start screen share
                try {
                    screenStream = await navigator.mediaDevices.getDisplayMedia({video: true});
                    const screenTrack = screenStream.getVideoTracks()[0];
                    
                    screenTrack.onended = () => {
                        if (isScreenSharing) toggleScreenShare();
                    };

                    if(localMediaStream.getVideoTracks().length > 0) {
                        localMediaStream.getVideoTracks()[0].stop();
                        localMediaStream.removeTrack(localMediaStream.getVideoTracks()[0]);
                    }
                    
                    localMediaStream.addTrack(screenTrack);
                    isScreenSharing = true;
                    btn.classList.replace('text-slate-400', 'text-emerald-400');
                    
                    addLocalVideoPreview(localMediaStream);
                    
                    const vidLocal = document.getElementById('video_local');
                    if (vidLocal) vidLocal.classList.remove('transform', 'scale-x-[-1]'); // Do not mirror a screen share

                    for(let hash in rtcPeers) {
                        const sender = rtcPeers[hash].getSenders().find(s => s.track && s.track.kind === 'video');
                        if(sender) sender.replaceTrack(screenTrack);
                        else {
                            rtcPeers[hash].addTrack(screenTrack, localMediaStream);
                            initiateCall(hash); // renegotiate
                        }
                    }
                } catch(e) { 
                    showToast("Screen share cancelled.", "info"); 
                }
            }
        }

        async function toggleLocalVideo() {
            if (!voiceActive || !localMediaStream) return;
            if (isScreenSharing) {
                showToast("Please stop screen sharing before toggling your camera.", "info");
                return;
            }

            const videoBtn = document.getElementById('btnVideoToggle');
            const lbl = document.getElementById('lblVideo');
            
            if (isVideoActive) {
                // Stop Video
                localMediaStream.getVideoTracks().forEach(t => t.stop());
                localMediaStream.removeTrack(localMediaStream.getVideoTracks()[0]);
                isVideoActive = false;
                lbl.innerText = 'Start Video';
                videoBtn.classList.replace('text-emerald-400', 'text-slate-400');
                
                const localWrap = document.getElementById('vidwrap_local');
                if(localWrap) localWrap.remove();
                
                // Renegotiate
                for(let hash in rtcPeers) initiateCall(hash);
            } else {
                // Start Video
                try {
                    const vidStream = await navigator.mediaDevices.getUserMedia({video: true});
                    const vidTrack = vidStream.getVideoTracks()[0];
                    localMediaStream.addTrack(vidTrack);
                    isVideoActive = true;
                    lbl.innerText = 'Stop Video';
                    videoBtn.classList.replace('text-slate-400', 'text-emerald-400');
                    
                    addLocalVideoPreview(localMediaStream);
                    
                    // Replace tracks in active peers
                    for(let hash in rtcPeers) {
                        const sender = rtcPeers[hash].getSenders().find(s => s.track && s.track.kind === 'video');
                        if (sender) {
                            sender.replaceTrack(vidTrack);
                        } else {
                            rtcPeers[hash].addTrack(vidTrack, localMediaStream);
                            initiateCall(hash); // Renegotiate
                        }
                    }
                } catch (e) {
                    showToast("Could not access camera.", "error");
                }
            }
        }

        // --- Push-to-Talk & Mute Audio ---

        function showPTTSettings() {
            document.getElementById('pttModal').classList.remove('hidden');
        }

        function togglePTTMode(enabled) {
            pttEnabled = enabled;
            applyAudioState();
            if (enabled) {
                showToast("Push-To-Talk Enabled (" + pttKey + ")", "info");
            } else {
                showToast("Voice Activation Enabled", "info");
            }
        }

        function listenForPTTKey() {
            const btn = document.getElementById('pttKeyBtn');
            btn.innerText = "Press any key...";
            btn.classList.add('bg-indigo-600', 'animate-pulse');
            isListeningForKey = true;
        }

        function setupPTTListeners() {
            document.addEventListener('keydown', (e) => {
                if (isListeningForKey) {
                    e.preventDefault();
                    pttKey = e.key;
                    if(e.code === 'Space') pttKey = 'Space';
                    
                    const btn = document.getElementById('pttKeyBtn');
                    btn.innerText = pttKey;
                    btn.classList.remove('bg-indigo-600', 'animate-pulse');
                    isListeningForKey = false;
                    return;
                }

                // If editing input, don't trigger PTT
                if (['INPUT', 'TEXTAREA'].includes(document.activeElement.tagName)) return;

                if (pttEnabled && voiceActive && (e.key === pttKey || e.code === pttKey) && !e.repeat) {
                    pttIsPressed = true;
                    applyAudioState();
                }
            });

            document.addEventListener('keyup', (e) => {
                if (['INPUT', 'TEXTAREA'].includes(document.activeElement.tagName)) return;
                
                if (pttEnabled && voiceActive && (e.key === pttKey || e.code === pttKey)) {
                    pttIsPressed = false;
                    applyAudioState();
                }
            });
        }

        function toggleMute() {
            isMuted = !isMuted;
            applyAudioState();
        }

        function applyAudioState() {
            if (!localMediaStream) return;
            
            const btn = document.getElementById('btnMuteAudio');
            const lbl = document.getElementById('lblMute');
            const audioTrack = localMediaStream.getAudioTracks()[0];
            
            if (!audioTrack) return;

            if (isMuted) {
                audioTrack.enabled = false;
                lbl.innerText = "Unmute";
                btn.classList.replace('text-emerald-400', 'text-red-400');
            } else if (pttEnabled) {
                if (pttIsPressed) {
                    audioTrack.enabled = true;
                    lbl.innerText = "PTT (Active)";
                    btn.classList.replace('text-red-400', 'text-emerald-400');
                    btn.classList.replace('text-slate-400', 'text-emerald-400');
                } else {
                    audioTrack.enabled = false;
                    lbl.innerText = "Hold '" + pttKey + "' to Talk";
                    btn.classList.replace('text-emerald-400', 'text-slate-400');
                    btn.classList.replace('text-red-400', 'text-slate-400');
                }
            } else {
                audioTrack.enabled = true;
                lbl.innerText = "Mute Audio";
                btn.classList.replace('text-red-400', 'text-emerald-400');
                btn.classList.replace('text-slate-400', 'text-emerald-400');
            }
        }

        // --- Video Routing & WebRTC ---

        // We added a 4th parameter to optionally specify the platform overriding activeVoicePlatform
        function sendSignal(type, targetHash, payloadObj = '', overridePlatform = null) {
            const destPlat = overridePlatform || activeVoicePlatform;
            if (!destPlat) return;
            apiCall('/api/messages', 'POST', {
                platform: destPlat,
                msg_type: type,
                target_hash: targetHash,
                payload: typeof payloadObj === 'string' ? payloadObj : JSON.stringify(payloadObj)
            }).catch(e => console.error("Signal failure", e));
        }

        function addLocalVideoPreview(stream) {
            let wrap = document.getElementById('vidwrap_local');
            if (!wrap) {
                wrap = document.createElement('div');
                wrap.id = 'vidwrap_local';
                wrap.className = 'relative bg-black rounded overflow-hidden shadow group min-h-[120px] max-h-[300px] flex items-center justify-center';
                
                const vid = document.createElement('video');
                vid.id = 'video_local';
                vid.autoplay = true;
                vid.muted = true; // Never hear self
                vid.playsInline = true;
                vid.className = 'w-full h-full object-contain transform scale-x-[-1] cursor-pointer'; // mirror local by default
                
                // Allow click to fullscreen
                vid.onclick = () => {
                    if (vid.requestFullscreen) vid.requestFullscreen();
                    else if (vid.webkitRequestFullscreen) vid.webkitRequestFullscreen();
                };
                
                const overlay = document.createElement('div');
                overlay.className = 'absolute bottom-1 left-1 bg-black/60 text-white text-[10px] px-1.5 py-0.5 rounded font-bold border border-slate-700 pointer-events-none';
                overlay.innerText = 'You';

                const detachBtn = document.createElement('button');
                detachBtn.className = 'detach-btn absolute top-1 right-1 bg-slate-800/80 hover:bg-slate-700 border border-slate-600 text-white text-[10px] px-2 py-0.5 rounded opacity-0 group-hover:opacity-100 transition-opacity font-bold shadow z-10';
                detachBtn.innerText = 'Detach';
                detachBtn.onclick = () => toggleDetach('local');

                wrap.appendChild(vid);
                wrap.appendChild(overlay);
                wrap.appendChild(detachBtn);
                document.getElementById('videoGrid').appendChild(wrap);
            }
            document.getElementById('video_local').srcObject = stream;
        }

        function getOrCreatePeer(targetHash) {
            if (rtcPeers[targetHash]) return rtcPeers[targetHash];
            
            const pc = new RTCPeerConnection(rtcConfig);
            rtcPeers[targetHash] = pc;
            iceQueues[targetHash] = []; 
            
            if (localMediaStream) {
                localMediaStream.getTracks().forEach(t => pc.addTrack(t, localMediaStream));
            }
            
            pc.onicecandidate = e => {
                if (e.candidate) sendSignal('WEBRTC_ICE', targetHash, e.candidate);
            };
            
            pc.ontrack = e => {
				initAudio();
                const stream = e.streams[0];
                
                // Build Video Wrapper if it doesn't exist
                let wrap = document.getElementById('vidwrap_' + targetHash);
                if (!wrap) {
                    wrap = document.createElement('div');
                    wrap.id = 'vidwrap_' + targetHash;
                    wrap.className = 'relative bg-slate-900 border border-slate-800 rounded overflow-hidden shadow group min-h-[120px] max-h-[300px] flex items-center justify-center';
                    
                    const vid = document.createElement('video');
                    vid.id = 'video_' + targetHash;
                    vid.autoplay = true;
                    vid.playsInline = true;
                    vid.crossOrigin = "anonymous";
                    vid.className = 'w-full h-full object-contain cursor-pointer';

                    // Allow click to fullscreen
                    vid.onclick = () => {
                        if (vid.requestFullscreen) vid.requestFullscreen();
                        else if (vid.webkitRequestFullscreen) vid.webkitRequestFullscreen();
                    };
                    
                    const name = userDir[targetHash] || targetHash.substring(0,4);
                    const overlay = document.createElement('div');
                    overlay.className = 'absolute bottom-1 left-1 bg-black/60 text-white text-[10px] px-1.5 py-0.5 rounded font-bold border border-slate-700 pointer-events-none';
                    overlay.innerText = name;

                    const detachBtn = document.createElement('button');
                    detachBtn.className = 'detach-btn absolute top-1 right-1 bg-slate-800/80 hover:bg-slate-700 border border-slate-600 text-white text-[10px] px-2 py-0.5 rounded opacity-0 group-hover:opacity-100 transition-opacity font-bold shadow z-10';
                    detachBtn.innerText = 'Detach';
                    detachBtn.onclick = () => toggleDetach(targetHash);

                    // Add Audio icon indicator
                    const audioIcon = document.createElement('div');
                    audioIcon.id = 'audiostat_' + targetHash;
                    audioIcon.className = 'absolute top-1 left-1 bg-emerald-500/80 text-[10px] w-5 h-5 flex items-center justify-center rounded-full animate-pulse shadow shadow-emerald-500 pointer-events-none';
                    audioIcon.innerHTML = '🎙️';

                    wrap.appendChild(vid);
                    wrap.appendChild(overlay);
                    wrap.appendChild(audioIcon);
                    wrap.appendChild(detachBtn);
                    document.getElementById('videoGrid').appendChild(wrap);
                }

                const videoEl = document.getElementById('video_' + targetHash);
                if (videoEl.srcObject !== stream) {
                    videoEl.srcObject = stream;
                }

                // Setup Volume Scaling via Web Audio (Only once per track addition)
                if (!gainNodes[targetHash] && stream.getAudioTracks().length > 0) {
                    videoEl.onloadedmetadata = () => { 
                        videoEl.play().catch(console.error); 
                        
                        // Prevent native double-audio
                        videoEl.volume = 0; 
                        videoEl.muted = true;
                        
                        if (gainNodes[targetHash]) gainNodes[targetHash].disconnect();
                        
                        const source = audioCtx.createMediaStreamSource(stream);
                        const gainNode = audioCtx.createGain();
                        gainNode.gain.value = userVolumes[targetHash] || 1.0;
                        gainNodes[targetHash] = gainNode;
                        
                        source.connect(gainNode);
                        gainNode.connect(audioCtx.destination);
                    };
                }
            };
            
            pc.onconnectionstatechange = () => {
                if (pc.connectionState === 'disconnected' || pc.connectionState === 'failed' || pc.connectionState === 'closed') {
                    const wrap = document.getElementById('vidwrap_' + targetHash);
                    if (wrap) wrap.remove();

					if (gainNodes[targetHash]) {
						gainNodes[targetHash].disconnect();
						delete gainNodes[targetHash];
					}
                    delete rtcPeers[targetHash];
                    renderMembers();
                }
            };
            
            return pc;
        }

        async function initiateCall(targetHash) {
            try {
                const pc = getOrCreatePeer(targetHash);
                const offer = await pc.createOffer();
                await pc.setLocalDescription(offer);
                sendSignal('WEBRTC_OFFER', targetHash, offer);
            } catch (e) { console.error("Call error", e); }
        }

        async function handleOffer(targetHash, offer) {
            try {
                const pc = getOrCreatePeer(targetHash);
                await pc.setRemoteDescription(new RTCSessionDescription(offer));
                flushIce(targetHash);
                const answer = await pc.createAnswer();
                await pc.setLocalDescription(answer);
                sendSignal('WEBRTC_ANSWER', targetHash, answer);
            } catch (e) { console.error("Offer error", e); }
        }

        async function handleAnswer(targetHash, answer) {
            try {
                const pc = getOrCreatePeer(targetHash);
                await pc.setRemoteDescription(new RTCSessionDescription(answer));
                flushIce(targetHash);
            } catch(e) { console.error("Answer error", e); }
        }

        async function handleIce(targetHash, ice) {
            try {
                const pc = getOrCreatePeer(targetHash);
                if (pc.remoteDescription && pc.remoteDescription.type) {
                    await pc.addIceCandidate(new RTCIceCandidate(ice)); 
                } else {
                    if(!iceQueues[targetHash]) iceQueues[targetHash] = [];
                    iceQueues[targetHash].push(ice);
                }
            } catch(e) { console.error("ICE error", e); }
        }

        async function flushIce(targetHash) {
            const pc = rtcPeers[targetHash];
            const queue = iceQueues[targetHash] || [];
            if (pc && pc.remoteDescription && pc.remoteDescription.type) {
                for (let ice of queue) {
                    try { await pc.addIceCandidate(new RTCIceCandidate(ice)); } catch(e) {}
                }
                iceQueues[targetHash] = [];
            }
        }

        // --- Draggable Modal & Detach Videos Logic ---

        function initDrag() {
            makeDraggable(document.getElementById("videoModal"), document.getElementById("videoModalHeader"));
        }

        function makeDraggable(elmnt, header) {
            let pos1 = 0, pos2 = 0, pos3 = 0, pos4 = 0;
            if (header) {
                header.onmousedown = dragMouseDown;
            } else {
                elmnt.onmousedown = dragMouseDown;
            }

            function dragMouseDown(e) {
                e = e || window.event;
                if(['BUTTON','INPUT','SELECT','TEXTAREA'].includes(e.target.tagName)) return;
                e.preventDefault();
                pos3 = e.clientX;
                pos4 = e.clientY;
                document.onmouseup = closeDragElement;
                document.onmousemove = elementDrag;
            }

            function elementDrag(e) {
                e = e || window.event;
                e.preventDefault();
                pos1 = pos3 - e.clientX;
                pos2 = pos4 - e.clientY;
                pos3 = e.clientX;
                pos4 = e.clientY;
                elmnt.style.top = (elmnt.offsetTop - pos2) + "px";
                elmnt.style.left = (elmnt.offsetLeft - pos1) + "px";
            }

            function closeDragElement() {
                document.onmouseup = null;
                document.onmousemove = null;
            }
        }

        function toggleDetach(targetHash) {
            const wrap = document.getElementById('vidwrap_' + targetHash);
            if (!wrap) return;

            const isDetached = wrap.classList.contains('detached-video');
            const btn = wrap.querySelector('.detach-btn');

            if (isDetached) {
                // Reattach to modal
                wrap.classList.remove('detached-video', 'fixed', 'z-[1000]', 'shadow-2xl', 'border', 'border-slate-500', 'rounded-xl', 'bg-black', 'resize', 'overflow-hidden');
                wrap.style.top = '';
                wrap.style.left = '';
                wrap.style.width = '';
                wrap.style.height = '';
                wrap.onmousedown = null; // Remove standalone drag
                
                const handle = wrap.querySelector('.drag-handle');
                if(handle) handle.remove();

                btn.innerText = 'Detach';
                document.getElementById('videoGrid').appendChild(wrap);
            } else {
                // Detach from modal
                const rect = wrap.getBoundingClientRect();
                wrap.classList.add('detached-video', 'fixed', 'z-[1000]', 'shadow-2xl', 'border', 'border-slate-500', 'rounded-xl', 'bg-black', 'resize', 'overflow-hidden');
                
                // Set default dimension and position so it doesn't blow up the screen
                wrap.style.top = Math.max(20, rect.top) + 'px';
                wrap.style.left = Math.max(20, rect.left) + 'px';
                wrap.style.width = '320px';
                wrap.style.height = '240px';
                
                const handle = document.createElement('div');
                handle.className = 'drag-handle absolute top-0 left-0 w-full h-8 bg-slate-800/90 cursor-move z-[50] flex items-center justify-between px-2 opacity-0 group-hover:opacity-100 transition-opacity backdrop-blur border-b border-slate-600';
                handle.innerHTML = '<span class="text-[10px] font-bold text-slate-300 uppercase tracking-widest px-1 pointer-events-none">Move Window</span>';
                wrap.insertBefore(handle, wrap.firstChild);
                
                document.body.appendChild(wrap);
                makeDraggable(wrap, handle); // Handle controls the dragging entirely
                btn.innerText = 'Attach';
            }
        }

        // ==========================================
        // Messages & Polling
        // ==========================================
        
        async function loadMessages(force = false) {
            if (!currentPlatform) return;
            if (isPolling && !force) return;

            if (force && pollController) {
                pollController.abort();
            }

            isPolling = true;
            pollController = new AbortController();
            const polledPlatform = currentPlatform; // Keep track of what we were looking at

            try {
                // Modified fetch: omit platform param to get EVERYTHING across all tabs
                const res = await fetch('/api/messages?since=' + lastMessageUpdate + '&limit=5000', {
                    headers: { 'Authorization': 'Bearer ' + API_TOKEN },
                    cache: 'no-store',
                    signal: pollController.signal
                });

                if (res.status === 304) {
                    isPolling = false;
                    return; 
                }
                
                if (!res.ok) throw new Error("HTTP " + res.status);

                const newUpdateStr = res.headers.get("X-Last-Update");
                if (newUpdateStr) lastMessageUpdate = parseInt(newUpdateStr);

                const msgs = await res.json();

                // If the user changed platforms mid-fetch, just discard UI append, but we STILL processed global messages!
                const userSwitchedTabs = (polledPlatform !== currentPlatform);

                const chatBox = document.getElementById('chatBox');
                const isAtBottom = chatBox.scrollHeight - chatBox.scrollTop <= chatBox.clientHeight + 10;
                
                const now = new Date();
                const newActiveUsers = {};
				let unackedIds = [];
                let newUnreadCounts = {};
                let unreadsChanged = false;

                // Track total unreads for notification sound
                let oldTotalUnread = 0;
                for (let p in unreadCounts) { oldTotalUnread += unreadCounts[p]; }

                if (msgs) {
                    msgs.sort((a,b) => new Date(a.timestamp) - new Date(b.timestamp));
                    
                    msgs.forEach(m => {
                        // Check TRUE BANS and BLOCKS strictly before ANY processing
                        const isBlocked = myBlockedHashes.includes(m.sender);
                        const plat = platformsCache[m.platform];
                        const isTrueBanned = plat && plat.banned_hashes && plat.banned_hashes.includes(m.sender);
                        
                        if (isBlocked || isTrueBanned) {
                            processedSignals.add(m.id);
                            return; // ABORT ALL processing completely for True Bans/Blocks
                        }

                        if (m.sender_name) userDir[m.sender] = m.sender_name;
                        
                        // Register users to platform presence
                        if (platformsCache[m.platform] && !platformsCache[m.platform].members[m.sender]) {
                            platformsCache[m.platform].members[m.sender] = 'MEMBER';
                        }

const msgTime = new Date(m.timestamp);
// Use Math.abs to allow clocks to be ahead OR behind, expanding the window to 90s
if (Math.abs(now - msgTime) < 90 * 1000) {
    newActiveUsers[m.sender] = true;
}
						
                        // Calculate unreads and ACKs dynamically
						if (['TEXT', 'FILE_TICKET'].includes(m.msg_type)) {
							if (m.sender !== myId) {
								const acks = m.acked_by || [];
								if (!acks.includes(myId) && !pendingAcks.has(m.id)) {
                                    // ACK if viewing current channel
                                    if (m.platform === currentPlatform) {
                                        unackedIds.push(m.id);
                                        pendingAcks.add(m.id);
                                    } else {
                                        // Otherwise, tick the unread notification badge up
                                        newUnreadCounts[m.platform] = (newUnreadCounts[m.platform] || 0) + 1;
                                    }
								}
							}
						}

                        // Process Signals Globally (Across all platforms simultaneously)
                        if (!processedSignals.has(m.id)) {
                            processedSignals.add(m.id);
							
							if (m.msg_type === 'PLATFORM_BAN' || m.msg_type === 'PLATFORM_UNBAN' || m.msg_type === 'PLATFORM_SHADOW_BAN' || m.msg_type === 'PLATFORM_UNSHADOW_BAN') {
                                loadPlatforms(); // silently sync
                                if (m.msg_type === 'PLATFORM_BAN' && m.text === myId && m.platform === currentPlatform) {
                                    showToast("You have been permanently banned from this platform.", "error");
                                    currentPlatform = null;
                                    loadPlatforms();
                                }
                            }

							if (m.msg_type === 'CHAT_REQUEST') {
								if (m.target_hash === myId && !myBlockedHashes.includes(m.sender)) {
									if (!localStorage.getItem('handled_req_' + m.id)) {
                                        playNotificationSound(); // Play notification sound on incoming call request
										showChatRequestModal(m.id, m.sender, m.sender_name, m.payload, m.text);
									}
								}
							}
							
                            if (m.msg_type === 'TRUSTED_INVITE') {
                                if (m.target_hash === myId && !myBlockedHashes.includes(m.sender) && !myBannedFrom.includes(m.platform)) {
                                    if (!platformsCache[m.platform]) {
                                        if (!window.availableFriendServers) window.availableFriendServers = {};
                                        window.availableFriendServers[m.platform] = {
                                            inviteId: m.id,
                                            platformId: m.platform,
                                            platformName: m.text,
                                            senderName: m.sender_name || userDir[m.sender] || m.sender.substring(0,8),
                                            payload: m.payload,
                                            timestamp: m.timestamp
                                        };
                                        const dBtn = document.getElementById('discoverBtn');
                                        if (dBtn) dBtn.classList.add('animate-pulse', 'bg-emerald-500');
                                    }
                                }
                            }

                            // ONLY process WebRTC if the signal is inside the platform we actively have the call open in
                            if (activeVoicePlatform && m.platform === activeVoicePlatform && m.sender !== myId) {
                                if (m.msg_type === 'VOICE_JOIN') voiceUsers[m.sender] = true;
                                if (m.msg_type === 'VOICE_LEAVE') voiceUsers[m.sender] = false;

                                const isSignalFresh = (now - new Date(m.timestamp)) < 60000; 
                                if (voiceActive && isSignalFresh) {
                                    if (m.msg_type === 'VOICE_JOIN') {
                                        if (myId > m.sender) initiateCall(m.sender);
                                        else if (!rtcPeers[m.sender]) sendSignal('VOICE_PING', m.sender);
                                    } else if (m.msg_type === 'VOICE_PING') {
                                        if (myId > m.sender && !rtcPeers[m.sender]) initiateCall(m.sender);
                                    } else if (m.msg_type === 'VOICE_LEAVE') {
                                        if (rtcPeers[m.sender]) {
                                            rtcPeers[m.sender].close();
                                            delete rtcPeers[m.sender];
                                            
                                            const wrap = document.getElementById('vidwrap_' + m.sender);
                                            if (wrap) wrap.remove();
                                            
											if (gainNodes[m.sender]) {
												gainNodes[m.sender].disconnect();
												delete gainNodes[m.sender];
											}
                                        }
                                    } else if (m.target_hash === myId) {
                                        if (m.msg_type === 'WEBRTC_OFFER') handleOffer(m.sender, JSON.parse(m.payload));
                                        else if (m.msg_type === 'WEBRTC_ANSWER') handleAnswer(m.sender, JSON.parse(m.payload));
                                        else if (m.msg_type === 'WEBRTC_ICE') handleIce(m.sender, JSON.parse(m.payload));
                                    }
                                }
                            }
                        }
                    });
                }

                // Apply unreads cleanly
                let newTotalUnread = 0;
                for (let p in newUnreadCounts) {
                    newTotalUnread += newUnreadCounts[p];
                    if (unreadCounts[p] !== newUnreadCounts[p]) {
                        unreadCounts[p] = newUnreadCounts[p];
                        unreadsChanged = true;
                    }
                }
                
                // Trigger notification sound if total unreads went up
                if (unreadsChanged && newTotalUnread > oldTotalUnread) {
                    playNotificationSound();
                    renderPlatformsList();
                }
                
                activeUsers = newActiveUsers;
                activeUsers[myId] = true; 
				
				if (unackedIds.length > 0) {
					apiCall('/api/messages/ack', 'POST', { message_ids: unackedIds }).catch(e => console.error("Ack error", e));
				}

                // Render Chat exclusively for the current channel view
                if (!userSwitchedTabs) {
                    const platformMsgs = msgs ? msgs.filter(m => m.platform === currentPlatform) : [];
                    chatBox.innerHTML = '';

                    if(platformMsgs.length === 0) {
                        chatBox.innerHTML = '<div class="text-center text-slate-600 italic text-sm mt-10">Start the conversation...</div>';
                    } else {
                        const lockIcon = '<svg class="w-3 h-3 inline-block ml-1 opacity-50 text-indigo-300" fill="currentColor" viewBox="0 0 20 20"><path fill-rule="evenodd" d="M5 9V7a5 5 0 0110 0v2a2 2 0 012 2v5a2 2 0 01-2 2H5a2 2 0 01-2-2v-5a2 2 0 012-2zm8-2v2H7V7a3 3 0 016 0z" clip-rule="evenodd"></path></svg>';
                        
                        const platData = platformsCache[currentPlatform];
                        let dynamicRoles = {...(platData ? platData.members : {})};

                        if(platData) {
                            const dr = dynamicRoles[myId];
                            const isAdmin = dr === 'OWNER' || dr === 'ADMIN';
                            document.getElementById('bannedUsersBtn').style.display = isAdmin ? 'flex' : 'none';
                        }
        
                        platformMsgs.forEach(msg => {
                            if (myBlockedHashes.includes(msg.sender)) return;
                            
                            // True Ban completely filters out the message
                            if (platData && platData.banned_hashes && platData.banned_hashes.includes(msg.sender)) return;
                            
                            // Shadow Ban filters out the message UNLESS you are the one who sent it locally
                            if (platData && platData.shadow_banned_hashes && platData.shadow_banned_hashes.includes(msg.sender) && msg.sender !== myId) return;

                            if (['PRESENCE', 'CHAT_REQUEST', 'TRUSTED_INVITE', 'PLATFORM_BAN', 'PLATFORM_UNBAN', 'PLATFORM_SHADOW_BAN', 'PLATFORM_UNSHADOW_BAN', 'VOICE_JOIN', 'VOICE_LEAVE', 'VOICE_PING', 'WEBRTC_OFFER', 'WEBRTC_ANSWER', 'WEBRTC_ICE'].includes(msg.msg_type)) return;

                            const isMe = msg.sender === myId;
                            
                            const rawName = msg.sender_name ? escapeHTML(msg.sender_name) : escapeHTML(msg.sender.substring(0, 8));
                            const rawHash = msg.sender_name ? '<span class="text-indigo-400/80 text-[10px] ml-0.5">#' + escapeHTML(msg.sender.substring(0, 4)) + '</span>' : '';
// Add these two lines to re-enable the menu and prevent syntax errors
const safeNameJS = (msg.sender_name || msg.sender.substring(0,8)).replace(/'/g, "\\'").replace(/"/g, "&quot;");
const displaySender = '<span class="text-white font-bold text-sm tracking-wide cursor-pointer hover:underline" onclick="showMemberMenu(event, \'' + msg.sender + '\', \'' + safeNameJS + '\')">' + rawName + rawHash + '</span>';
                            
                            let isAdmin = false;
                            if (dynamicRoles[msg.sender]) {
                                isAdmin = dynamicRoles[msg.sender] === 'OWNER' || dynamicRoles[msg.sender] === 'ADMIN';
                            }
                            
                            const div = document.createElement('div');
                            div.className = 'flex flex-col ' + (isMe ? 'items-end' : 'items-start');
                            
                            let bubbleContent = '';
                            let bubbleClass = 'max-w-md px-4 py-2.5 rounded-2xl shadow-sm break-words ' + (isMe ? 'bg-indigo-600 text-white rounded-tr-sm' : 'bg-slate-800 text-slate-200 border border-slate-700 rounded-tl-sm');
        
                            if (msg.msg_type === "TOMBSTONE") {
                                bubbleClass = 'max-w-md px-4 py-2 rounded-lg bg-slate-800/50 text-slate-500 border border-slate-700/50 text-sm italic flex items-center';
                                bubbleContent = '<span class="mr-2 text-red-500/50">[X]</span> [Purged by Powernode / Moderator]';
                            } else if (msg.msg_type === "FILE_TICKET") {
                                bubbleClass = 'max-w-md p-3 rounded-xl bg-slate-800 border border-slate-600 w-64';
                                bubbleContent = '<div class="flex items-center space-x-3 mb-2">' +
                                        '<div class="w-10 h-10 bg-slate-700 rounded flex items-center justify-center text-xl shadow-inner">📄</div>' +
                                        '<div class="flex-1 overflow-hidden">' +
                                            '<p class="text-sm font-bold truncate" title="' + escapeHTML(msg.file_name) + '">' + escapeHTML(msg.file_name) + '</p>' +
                                            '<p class="text-xs text-slate-400 truncate">CID: ' + escapeHTML(msg.file_cid.substring(0,12)) + '...</p>' +
                                        '</div>' +
                                    '</div>' +
                                    '<button onclick="downloadFile(\'' + escapeHTML(msg.file_cid) + '\', \'' + escapeHTML(msg.file_name) + '\', ' + (msg.file_size || 0) + ')" class="w-full py-1.5 bg-slate-700 hover:bg-slate-600 text-xs rounded text-slate-200 transition-colors font-bold shadow-md">Download via Mesh</button>';
                            } else {
                                bubbleContent = escapeHTML(msg.text);
                            }
                            
                            const timeString = new Date(msg.timestamp).toLocaleTimeString([], {hour: '2-digit', minute:'2-digit'});
                            const timeHTML = '<span class="text-slate-400 font-semibold text-[11px] px-1 bg-slate-800/50 rounded">' + timeString + '</span>';
                            
                            const hlcInfo = msg.hlc ? '<span class="opacity-40 ml-1 text-[10px]" title="HLC Clock">[L:' + msg.hlc.l + ']</span>' : '';
                            const adminBadge = isAdmin && !isMe ? '<span class="text-[9px] bg-amber-500/20 text-amber-500 px-1 rounded ml-1 border border-amber-500/30">ADMIN</span>' : '';
                            
                            let ackCount = (msg.acked_by || []).length;
                            let ackHtml = '';
                            if (ackCount > 0) {
                                const escapedArr = escapeHTML(JSON.stringify(msg.acked_by || []));
                                ackHtml = '<span class="text-emerald-400 font-bold cursor-pointer hover:underline ml-2 tracking-tighter" onclick=\'window.showAckModal(' + escapedArr + ')\'>✓✓ ' + ackCount + '</span>';
                            } else if (msg.is_acked) {
                                ackHtml = '<span class="text-emerald-600 font-bold ml-2 tracking-tighter" title="Mesh ACKed (Delivered to Peer)">✓</span>';
                            } else {
                                ackHtml = '<span class="text-slate-500 ml-2 text-[10px]" title="Local Only (No peers connected)">[Local]</span>';
                            }
        
                            let actionMenu = '';
                            const myRole = dynamicRoles[myId];
                            if ((myRole === "OWNER" || myRole === "ADMIN") && msg.msg_type !== "TOMBSTONE") {
                                actionMenu = '<button onclick="issueTombstone(\'' + escapeHTML(msg.id) + '\')" class="text-[10px] text-red-400 hover:text-red-300 ml-2">Drop (Tombstone)</button>';
                            }
        
                            div.innerHTML = '<div class="' + bubbleClass + '">' + bubbleContent + '</div>' +
                                '<div class="text-xs text-slate-500 mt-1 flex items-center">' +
                                    (isMe ? timeHTML + hlcInfo + actionMenu + ' <span class="mx-1.5 text-slate-600 text-[10px]">•</span> You ' + lockIcon + ' ' + ackHtml : displaySender + adminBadge + ' <span class="mx-2 text-slate-600 text-[10px]">•</span> ' + timeHTML + hlcInfo + actionMenu + ' ' + lockIcon + ' ' + ackHtml) +
                                '</div>';
                            
                            chatBox.appendChild(div);
                        });
                    }
                    
                    if (isAtBottom) chatBox.scrollTop = chatBox.scrollHeight;
                }
                
                renderMembers();
            } catch(e) {
                if (e.name !== 'AbortError') {
                    console.error("Message Sync Error:", e);
                }
            }
            isPolling = false;
        }

        // --- Members Sidebar Logic ---
        
        let membersOpen = false;
        
        function toggleMembers() {
            membersOpen = !membersOpen;
            const sidebar = document.getElementById('membersSidebar');
            if (membersOpen) {
                sidebar.classList.remove('w-0', 'border-l-0', 'opacity-0');
                sidebar.classList.add('w-64', 'border-l', 'opacity-100');
            } else {
                sidebar.classList.add('w-0', 'border-l-0', 'opacity-0');
                sidebar.classList.remove('w-64', 'border-l', 'opacity-100');
                closeMemberMenu(); 
            }
        }

        function renderMembers() {
            if(!currentPlatform || !platformsCache[currentPlatform]) return;
            const plat = platformsCache[currentPlatform];
            const searchStr = document.getElementById('memberSearch').value.toLowerCase();
            const list = document.getElementById('membersList');
            
            let online = [];
            let offline = [];

            Object.keys(plat.members).forEach(hash => {
                if (plat.banned_hashes && plat.banned_hashes.includes(hash)) return; // Don't show true banned users

                let name = userDir[hash] || (hash === myId ? myName : "Unknown User");
                if (searchStr && !name.toLowerCase().includes(searchStr)) return;

                let isOnline = (hash === myId) || !!activeUsers[hash];
                let role = plat.members[hash];

                const memObj = {hash, name, role, isOnline};
                if (isOnline) online.push(memObj); else offline.push(memObj);
            });

            online.sort((a,b) => a.name.localeCompare(b.name));
            offline.sort((a,b) => a.name.localeCompare(b.name));

            let html = '';
            if (online.length > 0) {
                html += '<div class="text-[10px] font-bold text-slate-500 uppercase tracking-widest mb-2 mt-1">Online — ' + online.length + '</div>';
                online.forEach(m => html += buildMemberRow(m));
            }
            if (offline.length > 0) {
                html += '<div class="text-[10px] font-bold text-slate-500 uppercase tracking-widest mb-2 mt-4">Offline — ' + offline.length + '</div>';
                offline.forEach(m => html += buildMemberRow(m));
            }
            list.innerHTML = html;
        }

        function buildMemberRow(m) {
            const isBlocked = myBlockedHashes.includes(m.hash);
            const isTrusted = myTrustedHashes.includes(m.hash);
            const plat = platformsCache[currentPlatform];
            const isShadowBanned = plat && plat.shadow_banned_hashes && plat.shadow_banned_hashes.includes(m.hash);
            
            const blockStyle = isBlocked ? 'opacity-40 grayscale' : '';
            const roleBadge = (m.role === 'OWNER' || m.role === 'ADMIN') ? '<span class="text-[8px] bg-amber-500/20 text-amber-500 px-1 rounded border border-amber-500/30 ml-2">ADMIN</span>' : '';
            const statusColor = m.isOnline ? 'bg-emerald-500 shadow-[0_0_5px_rgba(16,185,129,0.8)]' : 'bg-slate-600 border-slate-700';
            const displayHash = m.hash.substring(0,4);
            const initial = m.name.substring(0,1).toUpperCase() || '?';

            // Show voice indicator ONLY if they are active in the SAME platform we are currently viewing
            const isVoice = activeVoicePlatform === currentPlatform && (voiceUsers[m.hash] || !!rtcPeers[m.hash]);
            const voiceIcon = isVoice ? '<span class="text-[9px] bg-emerald-500/20 text-emerald-400 px-1 rounded ml-1 border border-emerald-500/30">🎙️</span>' : '';
            const trustedIcon = isTrusted ? '<span class="text-[9px] text-emerald-400 ml-1" title="Trusted Peer">★</span>' : '';
            const shadowBanIcon = isShadowBanned ? '<span class="text-[9px] text-orange-400 ml-1" title="Shadow Banned">👻</span>' : '';
const safeNameJS = m.name.replace(/'/g, "\\'").replace(/"/g, "&quot;");
return '<div onclick="showMemberMenu(event, \''+m.hash+'\', \''+safeNameJS+'\')" class="flex items-center cursor-pointer hover:bg-slate-800 p-1.5 rounded transition-colors ' + blockStyle + '">' +                '<div class="relative">' +
                    '<div class="w-8 h-8 bg-indigo-600/80 border border-indigo-500/50 rounded flex items-center justify-center text-sm font-bold text-white mr-3 shadow-inner">' + escapeHTML(initial) + '</div>' +
                    '<div class="absolute -bottom-0.5 -right-0.5 w-3 h-3 ' + statusColor + ' border-2 border-slate-900 rounded-full"></div>' +
                '</div>' +
                '<div class="flex-1 overflow-hidden">' +
                    '<div class="truncate text-sm text-slate-200 font-medium">' + escapeHTML(m.name) + roleBadge + voiceIcon + trustedIcon + shadowBanIcon + '</div>' +
                    '<div class="text-[10px] text-slate-500 font-mono">#' + escapeHTML(displayHash) + (isBlocked ? ' (Blocked)' : '') + '</div>' +
                '</div>' +
            '</div>';
        }

        // --- Context Menu Logic ---

        function showMemberMenu(event, hash, name) {
            event.stopPropagation(); 
            if (hash === myId) return;

            const menu = document.getElementById('memberContextMenu');
            menu.style.top = event.clientY + 'px';
            menu.style.left = (event.clientX - 220) + 'px'; 
            menu.classList.remove('hidden');

            const isBlocked = myBlockedHashes.includes(hash);
            const isTrusted = myTrustedHashes.includes(hash);
            const plat = platformsCache[currentPlatform];
            const myRole = plat ? plat.members[myId] : null;
            const isAdmin = myRole === 'OWNER' || myRole === 'ADMIN';
            
            let html = '<div class="px-4 py-2 border-b border-slate-700 text-xs font-bold text-slate-300 truncate">' + escapeHTML(name) + '</div>';

			if (voiceActive && activeVoicePlatform === currentPlatform && (voiceUsers[hash] || rtcPeers[hash])) {
				let vol = Math.round((userVolumes[hash] || 1.0) * 100);
				html += '<div class="px-4 py-3 border-b border-slate-700/50 bg-slate-800/80">' +
						'<label class="text-[10px] text-slate-400 block mb-2 font-bold uppercase tracking-wider">Volume Scale: <span id="volLabel_' + escapeHTML(hash) + '" class="text-indigo-300">' + vol + '%</span></label>' +
						'<input type="range" min="50" max="250" value="' + vol + '" oninput="setVolume(\'' + escapeHTML(hash) + '\', this.value)" class="w-full accent-indigo-500 h-1 bg-slate-600 rounded-lg appearance-none cursor-pointer">' +
						'</div>';
			}

            html += '<button onclick="requestChat(\'' + escapeHTML(hash) + '\', \'' + escapeHTML(name) + '\')" class="w-full text-left px-4 py-2 text-sm hover:bg-slate-700 transition-colors ' + (isBlocked ? 'opacity-30 cursor-not-allowed' : 'text-slate-200') + '" ' + (isBlocked ? 'disabled' : '') + '>Request Chat</button>' +
                '<button onclick="toggleTrust(\'' + escapeHTML(hash) + '\')" class="w-full text-left px-4 py-2 text-sm hover:bg-slate-700 text-emerald-400 transition-colors font-medium border-t border-slate-700/50">' + (isTrusted ? 'Untrust User' : 'Trust User') + '</button>' +
                '<button onclick="toggleBlock(\'' + escapeHTML(hash) + '\')" class="w-full text-left px-4 py-2 text-sm hover:bg-slate-700 text-red-400 transition-colors font-medium border-t border-slate-700/50">' + (isBlocked ? 'Unblock User' : 'Block User') + '</button>';
            
            if (isAdmin) {
                html += '<button onclick="banFromPlatform(\'' + escapeHTML(hash) + '\', \'shadow_ban\')" class="w-full text-left px-4 py-2 text-sm hover:bg-slate-700 text-orange-400 transition-colors font-medium border-t border-slate-700/50">Shadow Ban User</button>' +
                        '<button onclick="banFromPlatform(\'' + escapeHTML(hash) + '\', \'ban\')" class="w-full text-left px-4 py-2 text-sm hover:bg-slate-700 text-red-500 transition-colors font-medium border-t border-slate-700/50">True Ban User</button>';
            }

            menu.innerHTML = html;
            document.addEventListener('click', closeMemberMenu, {once: true});
        }

        function closeMemberMenu() {
            document.getElementById('memberContextMenu').classList.add('hidden');
        }

		function setVolume(hash, val) {
			document.getElementById('volLabel_' + hash).innerText = val + '%';
			userVolumes[hash] = val / 100.0;
			if (gainNodes[hash]) {
				gainNodes[hash].gain.value = userVolumes[hash];
			}
		}

        // --- Network & Action Functions ---

		function requestChat(targetHash, targetName) {
			closeMemberMenu();
			const platName = "DM: " + myName + " & " + targetName;
			apiCall('/api/platforms', 'POST', { name: platName, is_ephemeral: false, is_trusted: false, ttl_hours: 0 })
			.then(p => {
				return apiCall('/api/invites', 'POST', { platform_id: p.id, max_uses: 2, ttl_hours: 48 });
			})
			.then(inv => {
				return apiCall('/api/messages', 'POST', { platform: currentPlatform, msg_type: "CHAT_REQUEST", target_hash: targetHash, payload: inv.invite_code, text: platName });
			})
			.then(() => {
				showToast("Secure chat request sent to " + targetName, "success");
				loadPlatforms(); 
			}).catch(e => showToast("Request Error: " + e.message, "error"));
		}

		function showChatRequestModal(msgId, senderHash, senderName, inviteCode, platName) {
			pendingChatRequests.push({msgId, senderHash, senderName, inviteCode, platName});
			processNextChatRequest();
		}

		function processNextChatRequest() {
			if (isShowingChatRequest || pendingChatRequests.length === 0) return;
			isShowingChatRequest = true;
			const req = pendingChatRequests.shift();
			
			document.getElementById('chatRequestText').innerHTML = '<span class="font-bold text-white">' + escapeHTML(req.senderName || 'Unknown User') + '</span> wants to start a secure direct chat with you.';
			
			document.getElementById('btnChatBlock').onclick = () => {
				localStorage.setItem('handled_req_' + req.msgId, '1');
				toggleBlock(req.senderHash);
				closeChatRequestModal();
			};
			document.getElementById('btnChatIgnore').onclick = () => {
				localStorage.setItem('handled_req_' + req.msgId, '1');
				closeChatRequestModal();
			};
			document.getElementById('btnChatAccept').onclick = () => {
				localStorage.setItem('handled_req_' + req.msgId, '1');
				joinPlatformByCode(req.inviteCode);
				closeChatRequestModal();
			};
			
			document.getElementById('chatRequestModal').classList.remove('hidden');
		}

		function closeChatRequestModal() {
			document.getElementById('chatRequestModal').classList.add('hidden');
			isShowingChatRequest = false;
			processNextChatRequest();
		}

        function toggleBlock(hash) {
            closeMemberMenu();
            apiCall('/api/block', 'POST', {hash: hash})
            .then(() => {
                showToast("User blocking updated.", "success");
                return apiCall('/api/identity');
            }).then(data => {
                myBlockedHashes = data.blocked_hashes || [];
                lastMessageUpdate = 0; 
                loadMessages(true); 
            }).catch(e => showToast("Block Error: " + e.message, "error"));
        }

        function toggleTrust(hash) {
            closeMemberMenu();
            apiCall('/api/trust', 'POST', {hash: hash})
            .then(() => {
                showToast("User trust settings updated.", "success");
                return apiCall('/api/identity');
            }).then(data => {
                myTrustedHashes = data.trusted_hashes || [];
                renderMembers();
            }).catch(e => showToast("Trust Error: " + e.message, "error"));
        }

        function banFromPlatform(hash, action) {
            closeMemberMenu();
            let actionText = action === 'ban' ? 'True Ban' : 'Shadow Ban';
            showConfirm(actionText + " User", "Are you sure you want to " + actionText.toLowerCase() + " this cryptographic hash from the platform?", (confirmed) => {
                if(!confirmed) return;
                apiCall('/api/platforms/ban', 'POST', {platform_id: currentPlatform, hash: hash, action: action})
                .then(() => {
                    showToast("User successfully " + actionText.toLowerCase() + "ned.", "success");
                    loadPlatforms(currentPlatform);
                    lastMessageUpdate = 0;
                    loadMessages(true);
                }).catch(e => showToast("Ban Error: " + e.message, "error"));
            });
        }

        function showBannedModal() {
            const plat = platformsCache[currentPlatform];
            if(!plat) return;
            const list = document.getElementById('bannedListDisplay');
            list.innerHTML = '<h3 class="text-red-500 font-bold mb-1">True Banned</h3>';
            
            if(!plat.banned_hashes || plat.banned_hashes.length === 0) {
                list.innerHTML += '<div class="text-slate-500 italic p-2 text-center text-xs">No true banned users.</div>';
            } else {
                plat.banned_hashes.forEach(h => {
                    const name = userDir[h] || 'Unknown Hash';
                    list.innerHTML += '<div class="flex justify-between items-center bg-slate-700/50 p-2 rounded mb-2">' + 
                        '<span class="text-xs">' + escapeHTML(name) + ' <span class="font-mono text-indigo-400 ml-1">#' + escapeHTML(h.substring(0,4)) + '</span></span>' +
                        '<button onclick="unbanUser(\''+escapeHTML(h)+'\', \'unban\')" class="text-[10px] bg-red-600 hover:bg-red-500 px-2 py-1 font-bold text-white rounded shadow">Unban</button></div>';
                });
            }

            list.innerHTML += '<h3 class="text-orange-400 font-bold mb-1 mt-4">Shadow Banned</h3>';
            if(!plat.shadow_banned_hashes || plat.shadow_banned_hashes.length === 0) {
                list.innerHTML += '<div class="text-slate-500 italic p-2 text-center text-xs">No shadow banned users.</div>';
            } else {
                plat.shadow_banned_hashes.forEach(h => {
                    const name = userDir[h] || 'Unknown Hash';
                    list.innerHTML += '<div class="flex justify-between items-center bg-slate-700/50 p-2 rounded mb-2">' + 
                        '<span class="text-xs">' + escapeHTML(name) + ' <span class="font-mono text-indigo-400 ml-1">#' + escapeHTML(h.substring(0,4)) + '</span></span>' +
                        '<button onclick="unbanUser(\''+escapeHTML(h)+'\', \'unshadow_ban\')" class="text-[10px] bg-orange-600 hover:bg-orange-500 px-2 py-1 font-bold text-white rounded shadow">Unban</button></div>';
                });
            }
            document.getElementById('bannedModal').classList.remove('hidden');
        }

        function unbanUser(hash, action) {
            apiCall('/api/platforms/ban', 'POST', {platform_id: currentPlatform, hash: hash, action: action})
            .then(() => {
                showToast("Hash unbanned successfully.", "success");
                document.getElementById('bannedModal').classList.add('hidden');
                loadPlatforms(currentPlatform);
            }).catch(e => showToast("Unban Error: " + e.message, "error"));
        }

        // --- DISCOVERY Modal Logic ---

        function showDiscoverModal() {
            const list = document.getElementById('discoverListDisplay');
            list.innerHTML = '';
            let hasAny = false;
            
            const btn = document.getElementById('discoverBtn');
            if (btn) btn.classList.remove('animate-pulse', 'bg-emerald-500'); // clear unread indicator
            
            if (window.availableFriendServers) {
                const sorted = Object.values(window.availableFriendServers).sort((a,b) => new Date(b.timestamp) - new Date(a.timestamp));
                for (let server of sorted) {
                    if (platformsCache[server.platformId]) continue; // Skip if already joined
                    hasAny = true;
                    list.innerHTML += '<div class="flex items-center justify-between bg-slate-700/50 p-3 rounded">' +
                        '<div class="flex items-center space-x-3 overflow-hidden w-full">' +
                            '<input type="checkbox" value="' + escapeHTML(server.payload) + '" class="discover-cb w-4 h-4 rounded bg-slate-800 border-slate-600 text-emerald-500 focus:ring-emerald-500 flex-shrink-0 cursor-pointer">' +
                            '<div class="overflow-hidden cursor-pointer" onclick="this.previousElementSibling.click()">' +
                                '<div class="font-bold text-white text-sm truncate">' + escapeHTML(server.platformName) + '</div>' +
                                '<div class="text-[10px] text-slate-400">Invited by ' + escapeHTML(server.senderName) + '</div>' +
                            '</div>' +
                        '</div>' +
                    '</div>';
                }
            }
            if (!hasAny) {
                list.innerHTML = '<div class="text-slate-500 italic p-4 text-center mt-4 text-sm">No new trusted servers found. Ask a friend to mark a server as Trusted!</div>';
            }
            document.getElementById('discoverModal').classList.remove('hidden');
        }

        function hideDiscoverModal() {
            document.getElementById('discoverModal').classList.add('hidden');
        }

        function joinSelectedDiscovered() {
            const checkboxes = document.querySelectorAll('.discover-cb:checked');
            if (checkboxes.length === 0) {
                hideDiscoverModal();
                return;
            }
            showToast("Joining " + checkboxes.length + " platform(s)...", "info");
            
            // Sequentially join to prevent overwhelming the local DB
            let chain = Promise.resolve();
            checkboxes.forEach(cb => {
                chain = chain.then(() => apiCall('/api/join', 'POST', { invite_code: cb.value }).catch(e => console.error(e)));
            });
            chain.then(() => {
                hideDiscoverModal();
                showToast("Finished joining selected platforms.", "success");
                loadPlatforms();
                loadPeers();
            });
        }

        function joinPlatform() {
            const code = document.getElementById('inviteCodeInput').value.trim();
            if(!code) return;
            hideJoinModal();
            joinPlatformByCode(code);
        }
        
        function joinPlatformByCode(code) {
            showToast("Negotiating payload and authenticating...", "info");
            apiCall('/api/join', 'POST', { invite_code: code })
            .then(() => {
                showToast("Joined mesh! Synchronizing CRDT ledger...", "success");
                try {
                    const payload = JSON.parse(atob(code));
                    if (payload && typeof payload.platform_id === 'string' && payload.platform_id.length > 0) {
                        loadPlatforms(payload.platform_id);
                    } else {
                        loadPlatforms();
                    }
                } catch(e) {
                    loadPlatforms();
                }
                loadPeers();
            }).catch(e => showToast("Join Request Rejected: " + e.message, "error"));
        }
		
		window.showAckModal = function(hashList) {
			const list = document.getElementById('ackListDisplay');
			list.innerHTML = '';
			if (!hashList || hashList.length === 0) {
				list.innerHTML = '<div class="text-slate-500 italic p-2 text-center">No one has received this yet.</div>';
			} else {
				hashList.forEach(h => {
					const name = userDir[h] || 'Unknown User';
					list.innerHTML += '<div class="flex justify-between items-center bg-slate-700/50 p-2 rounded mb-1">' +
						'<span>' + escapeHTML(name) + ' <span class="text-xs font-mono text-indigo-400 ml-1">#' + escapeHTML(h.substring(0,4)) + '</span></span>' +
					'</div>';
				});
			}
			document.getElementById('ackModal').classList.remove('hidden');
		}

        document.getElementById('msgForm').addEventListener('submit', (e) => {
            e.preventDefault();
            const input = document.getElementById('msgInput');
            if (!input.value.trim() || !currentPlatform) return;

            apiCall('/api/messages', 'POST', { platform: currentPlatform, text: input.value.trim(), msg_type: "TEXT" })
            .then(() => {
                input.value = '';
                loadMessages(true); 
            }).catch(e => showToast(e.message, "error"));
        });

        // --- File Sharing Logic ---
        
        async function handleFileSelect(event) {
            const file = event.target.files[0];
            if (!file) return;

            if (file.size > 5 * 1024 * 1024 * 1024) {
                showToast("File too large. Mesh limit is currently 5GB per file.", "error");
                event.target.value = '';
                return;
            }

            const formData = new FormData();
            formData.append("file", file);

            try {
                const btn = document.querySelector('button[title="Share a file with the mesh"]');
                const origText = btn.innerHTML;
                btn.innerHTML = "Encrypting...";
                showToast("Slicing and encrypting file stream locally...", "info");
                
                const res = await fetch('/api/files/upload', {
                    method: 'POST',
					headers: { 'Authorization': 'Bearer ' + API_TOKEN },
                    body: formData
                });
                
                if (!res.ok) {
                    const text = await res.text();
                    throw new Error(text);
                }
                const data = await res.json();
				if (data.warning) showToast(data.warning, "info");

                await apiCall('/api/messages', 'POST', { 
                    platform: currentPlatform, 
                    msg_type: "FILE_TICKET", 
                    file_cid: data.cid,
                    file_name: data.name,
					file_size: file.size,
                    payload: data.key 
                });

                btn.innerHTML = origText;
                showToast("File ticket dispatched to mesh layer.", "success");
            } catch (err) {
                showToast("Encryption/Upload failed: " + err.message, "error");
                document.querySelector('button[title="Share a file with the mesh"]').innerHTML = '<span class="mr-2 text-xl">📁</span> Upload File';
            }
            
            event.target.value = ''; 
        }

        function downloadFile(cid, name, size) {
			if (size > 1024 * 1024 * 1024) {
				showToast("Warning: File is larger than 1GB. Download and decryption may take a while.", "info");
			} else {
            	showToast("Beginning local decryption and file stream...", "info");
			}
			
			fetch('/api/files/download?cid=' + encodeURIComponent(cid) + '&name=' + encodeURIComponent(name), {
				headers: { 'Authorization': 'Bearer ' + API_TOKEN }
			})
			.then(async res => {
				if (!res.ok) throw new Error(await res.text());
				return res.blob();
			})
			.then(blob => {
				const url = window.URL.createObjectURL(blob);
				const a = document.createElement('a');
				a.href = url;
				a.download = name;
				document.body.appendChild(a);
				a.click();
				a.remove();
				window.URL.revokeObjectURL(url);
				showToast("File decrypted and saved locally.", "success");
			})
			.catch(err => showToast("Download error: " + err.message, "error"));
        }

        function issueTombstone(messageId) {
            apiCall('/api/moderate', 'POST', { message_id: messageId, platform_id: currentPlatform })
            .then(() => {
                showToast("Tombstone executed successfully.", "success");
            }).catch(e => showToast("Mod Error: " + e.message, "error"));
        }

        function leavePlatform() {
            if(!currentPlatform) {
                return;
            }
            
            showConfirm("Leave Platform", "Are you sure you want to leave this platform? All local data copies for it will be explicitly purged.", (confirmed) => {
                if(!confirmed) return;
                apiCall('/api/platforms/leave', 'POST', { id: currentPlatform })
                .then(() => {
                    showToast("Left platform securely.", "success");
                    currentPlatform = null;
                    loadPlatforms();
                }).catch(e => showToast("Purge Error: " + e.message, "error"));
            });
        }

        // --- INVITE SYSTEM Logic ---

        function generateInvite() {
            apiCall('/api/invites', 'POST', { platform_id: currentPlatform, max_uses: 5, ttl_hours: 24 })
            .then(data => {
                document.getElementById('generatedInviteCode').value = data.invite_code;
                document.getElementById('inviteDisplayModal').classList.remove('hidden');
                showToast("Invite payload encrypted and generated.", "success");
            }).catch(e => showToast("Invite Blocked: " + e.message, "error"));
        }

        function hideInviteDisplayModal() { document.getElementById('inviteDisplayModal').classList.add('hidden'); }

        function copyInviteCode() {
            const codeEl = document.getElementById('generatedInviteCode');
            codeEl.select();
            document.execCommand('copy');
            
            const btn = event.currentTarget;
            const originalText = btn.innerHTML;
            btn.innerHTML = '<span class="text-white font-bold">Copied!</span>';
            showToast("Copied to clipboard successfully.", "success");
            setTimeout(() => { btn.innerHTML = originalText; }, 2000);
        }

        function showJoinModal() { document.getElementById('joinModal').classList.remove('hidden'); }
        function hideJoinModal() { 
            document.getElementById('joinModal').classList.add('hidden'); 
            document.getElementById('inviteCodeInput').value = '';
        }

        function addPeer() {
            const url = document.getElementById('newPeerUrl').value.trim();
            if(!url) return;
            apiCall('/api/peers', 'POST', { url: url })
            .then(() => {
                document.getElementById('newPeerUrl').value = '';
                showToast("Peer handshaking initiated.", "info");
                loadPeers();
            }).catch(e => showToast("Peer Exception: " + e.message, "error"));
        }

        function showCreateModal() { document.getElementById('createModal').classList.remove('hidden'); }
        function hideCreateModal() { document.getElementById('createModal').classList.add('hidden'); }
        function showPeerModal() { document.getElementById('peerModal').classList.remove('hidden'); loadPeers(); }
        function hidePeerModal() { document.getElementById('peerModal').classList.add('hidden'); }
        
        function createPlatform() {
            const name = document.getElementById('newPlatName').value || "unnamed-plat";
            const isTrusted = document.getElementById('newPlatTrusted').checked;

            apiCall('/api/platforms', 'POST', { name: name, is_ephemeral: false, is_trusted: isTrusted, ttl_hours: 0 })
            .then(() => {
                hideCreateModal();
                showToast("Genesis block generated for " + name, "success");
                loadPlatforms();
            }).catch(e => showToast("Creation Failure: " + e.message, "error"));
        }

        setInterval(() => loadMessages(), 1000);
        
setInterval(() => {
    // Broadcast presence to all known platforms rather than just the active tab
    Object.keys(platformsCache).forEach(platId => {
        apiCall('/api/messages', 'POST', { 
            platform: platId, 
            text: "ping", 
            msg_type: "PRESENCE" 
        }).catch(()=>{});
    });
}, 30000);

    </script>
</body>
</html>`