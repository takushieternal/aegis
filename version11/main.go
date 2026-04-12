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
	Devices          []string `json:"devices"`
	BlockedHashes    []string `json:"blocked_hashes"`
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
		if remote.Logical > h.Logical {
			h.Logical = remote.Logical + 1
		} else {
			h.Logical++
		}
	}
}

// ==========================================
// Models & Governance
// ==========================================

type GovernanceModel string

const (
	Dictatorship GovernanceModel = "PRIVATE_DICTATORSHIP"
	Democracy    GovernanceModel = "DEMOCRATIC_CONSENSUS"
)

type Role string

const (
	RoleOwner  Role = "OWNER"
	RoleAdmin  Role = "ADMIN"
	RoleMember Role = "MEMBER"
)

type Platform struct {
	ID           string          `json:"id"`
	ParentID     string          `json:"parent_id,omitempty"`
	Name         string          `json:"name"`
	IsEphemeral  bool            `json:"is_ephemeral"`
	TTL          time.Time       `json:"ttl,omitempty"`
	StateKey     string          `json:"-"`
	Governance   GovernanceModel `json:"governance"`
	Members      map[string]Role `json:"members"`
	BannedHashes []string        `json:"banned_hashes"`
}

type InviteContract struct {
	ID        string    `json:"id"`
	Platform  string    `json:"platform"`
	ExpiresAt time.Time `json:"expires_at"`
	MaxUses   int       `json:"max_uses"`
	Uses      int       `json:"uses"`
}

type InvitePayload struct {
	PlatformID   string `json:"platform_id"`
	PlatformName string `json:"platform_name"`
	Governance   string `json:"governance"`
	PeerURL      string `json:"peer_url"`
	InviteID     string `json:"invite_id"`
}

type Message struct {
	ID         string    `json:"id"`
	Platform   string    `json:"platform"`
	Sender     string    `json:"sender"`      // RootHash
	SenderName string    `json:"sender_name"` // Username
	Text       string    `json:"text"`
	Timestamp  time.Time `json:"timestamp"`

	Clock      HLC               `json:"hlc"`
	VectorMap  map[string]uint64 `json:"vector_map"`
	MsgType    string            `json:"msg_type"`             // TEXT, FILE_TICKET, TOMBSTONE, PRESENCE, POLL, VOTE, SUB_PLATFORM
	TargetMsg  string            `json:"target_msg,omitempty"` // For linking Votes to Polls
	TargetHash string            `json:"target_hash,omitempty"`// For nominating a user
	Payload    string            `json:"payload,omitempty"`    // For Invite Codes or AES Keys
	FileCID    string            `json:"file_cid,omitempty"`
	FileName   string            `json:"file_name,omitempty"`
	IsAcked    bool              `json:"is_acked"`
	
	PublicKey  string            `json:"public_key"` // Hex encoded ED25519 Public Key
	Signature  string            `json:"signature"`  // Hex encoded ED25519 Signature
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
	mu             sync.RWMutex
}

var node *AegisNode
var dbFile string
var currentPort string
var fileStoreDir string
var dbMutex sync.Mutex
var APIToken string
var isNodeLocked bool

// Replaced Wildcard CORS with Strict API Token Auth to prevent Fetch Hijacking
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

// Environment Helper: Bypassed strictly for IDE / Proxy compatibility
func isLocal(r *http.Request) bool {
	return true
}

// Safe JSON Error Response
func jsonError(w http.ResponseWriter, message string, statusCode int) {
	w.WriteHeader(statusCode)
	json.NewEncoder(w).Encode(map[string]string{"error": message})
}

// Secure ID Generation
func generateID(prefix string) string {
	b := make([]byte, 16)
	rand.Read(b)
	return fmt.Sprintf("%s_%x", prefix, b)
}

func main() {
	portFlag := flag.String("port", "8080", "Port to run the Aegis node on")
	flag.Parse()
	currentPort = *portFlag

	fmt.Printf("[Aegis] Starting Project Aegis Local Node on port %s...\n", currentPort)
	initNode()

	// Web UI & Core APIs
	http.HandleFunc("/", serveUI)
	http.HandleFunc("/api/identity", apiIdentity)
	http.HandleFunc("/api/unlock", apiUnlock)
	http.HandleFunc("/api/block", apiBlockUser)
	http.HandleFunc("/api/platforms/ban", apiBanUser)
	http.HandleFunc("/api/platforms", apiPlatforms)
	http.HandleFunc("/api/platforms/leave", apiLeavePlatform)
	http.HandleFunc("/api/messages", apiMessages)
	http.HandleFunc("/api/moderate", apiModerate)
	http.HandleFunc("/api/invites", apiInvites)
	http.HandleFunc("/api/join", apiJoin)
	http.HandleFunc("/api/peers", apiPeers)
	
	// File Sharing Endpoints
	http.HandleFunc("/api/files/upload", apiUploadFile)
	http.HandleFunc("/api/files/download", apiDownloadFile)
	
	// P2P Endpoints
	http.HandleFunc("/p2p/message", p2pReceiveMessage)
	http.HandleFunc("/p2p/files", p2pServeFile)

	// Replay Cache Garbage Collector
	go func() {
		for {
			time.Sleep(15 * time.Minute)
			cleanReplayCache()
		}
	}()

	url := "http://localhost:" + currentPort
	fmt.Printf("[Web] Aegis Local Interface running at: %s\n", url)

	go func() {
		time.Sleep(500 * time.Millisecond)
		openBrowser(url)
	}()

	log.Fatal(http.ListenAndServe(":"+currentPort, nil))
}

func openBrowser(url string) {
	var err error
	switch runtime.GOOS {
	case "linux":
		err = exec.Command("xdg-open", url).Start()
	case "windows":
		err = exec.Command("rundll32", "url.dll,FileProtocolHandler", url).Start()
	case "darwin":
		err = exec.Command("open", url).Start()
	default:
		err = fmt.Errorf("unsupported platform")
	}
	if err != nil {
		log.Printf("Could not open browser: %v", err)
	}
}

func initNode() {
	// Generate local API token for this session
	tokenBytes := make([]byte, 16)
	rand.Read(tokenBytes)
	APIToken = hex.EncodeToString(tokenBytes)

	node = &AegisNode{
		Platforms:      make(map[string]Platform),
		Messages:       make([]Message, 0),
		Invites:        make([]InviteContract, 0),
		Peers:          make([]string, 0),
		Clock:          HLC{Physical: time.Now().UnixNano(), Logical: 0},
		SeenSignatures: make(map[string]int64),
	}

	dbFile = fmt.Sprintf("aegis_local_store_%s.json", currentPort)
	fileStoreDir = fmt.Sprintf("aegis_files_%s", currentPort)
	os.MkdirAll(fileStoreDir, 0700)

	if _, err := os.Stat(dbFile); os.IsNotExist(err) {
		fmt.Println("[Key] Generating Master Identity Key...")
		pub, priv, err := ed25519.GenerateKey(rand.Reader)
		if err != nil {
			log.Fatalf("Failed to generate keys: %v", err)
		}

		hash := sha256.Sum256(pub)
		rootHash := hex.EncodeToString(hash[:])

		node.Identity = AegisIdentity{
			Username:      "", // Left blank to trigger UI Prompt
			PublicKey:     hex.EncodeToString(pub),
			PrivateKey:    priv,
			RootHash:      rootHash,
			SeedPhrase:    []string{"abandon", "ability", "able", "about", "above", "absent", "absorb"},
			Devices:       []string{"device_01_local"},
			BlockedHashes: make([]string, 0),
		}

		node.Platforms["root"] = Platform{
			ID:         "root",
			Name:       "Root Identity Ledger",
			Governance: Dictatorship,
			Members:    map[string]Role{rootHash: RoleOwner},
		}

		isNodeLocked = false // Will be locked upon password creation
		saveLocalDB()
	} else {
		fmt.Println("[Unlock] Unlocking local database...")
		isNodeLocked = true
		loadLocalDB()
		if node.Identity.BlockedHashes == nil {
			node.Identity.BlockedHashes = make([]string, 0)
			saveLocalDB()
		}
	}
}

func saveLocalDB() {
	node.mu.RLock()
	data, _ := json.MarshalIndent(node, "", "  ")
	node.mu.RUnlock()

	dbMutex.Lock()
	defer dbMutex.Unlock()
	
	tmpFile := dbFile + ".tmp"
	os.WriteFile(tmpFile, data, 0600)
	os.Rename(tmpFile, dbFile)
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
		node.mu.Unlock()
	}
}

// ==========================================
// Cryptography Security Checks & Helpers
// ==========================================

func deriveKey(password string) []byte {
	hash := sha256.Sum256([]byte(password))
	return hash[:]
}

func encryptData(data []byte, password string) string {
	key := deriveKey(password)
	block, _ := aes.NewCipher(key)
	gcm, _ := cipher.NewGCM(block)
	nonce := make([]byte, gcm.NonceSize())
	rand.Read(nonce)
	ciphertext := gcm.Seal(nonce, nonce, data, nil)
	return base64.StdEncoding.EncodeToString(ciphertext)
}

func decryptData(cryptoText string, password string) ([]byte, error) {
	data, err := base64.StdEncoding.DecodeString(cryptoText)
	if err != nil {
		return nil, err
	}
	key := deriveKey(password)
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

func verifyMessageSignature(msg Message) bool {
	node.mu.RLock()
	if _, seen := node.SeenSignatures[msg.Signature]; seen {
		node.mu.RUnlock()
		return false // Reject Replay Attack
	}
	node.mu.RUnlock()

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
	payloadToVerify := fmt.Sprintf("%s:%s:%s:%d", msg.ID, msg.Platform, msg.Text, msg.Timestamp.UnixNano())
	if !ed25519.Verify(pubBytes, []byte(payloadToVerify), sigBytes) {
		return false
	}
	
	drift := time.Since(msg.Timestamp)
	if drift > 15*time.Minute || drift < -15*time.Minute {
		return false
	}

	node.mu.Lock()
	node.SeenSignatures[msg.Signature] = time.Now().UnixNano()
	node.mu.Unlock()

	return true
}

// ==========================================
// Roles & Effective Moderation Evaluator
// ==========================================

func getEffectiveRoles(platID string) map[string]Role {
	node.mu.RLock()
	defer node.mu.RUnlock()

	plat, exists := node.Platforms[platID]
	if !exists {
		return nil
	}

	roles := make(map[string]Role)
	for k, v := range plat.Members {
		roles[k] = v
	}

	if plat.Governance != Democracy {
		return roles
	}

	type Poll struct {
		Timestamp time.Time
		Target    string
		Votes     map[string]string // Map enforces "One Vote Per User Hash"
	}
	polls := make(map[string]*Poll)

	for _, m := range node.Messages {
		if m.Platform != platID {
			continue
		}
		if m.MsgType == "POLL" {
			polls[m.ID] = &Poll{Timestamp: m.Timestamp, Target: m.TargetHash, Votes: make(map[string]string)}
		} else if m.MsgType == "VOTE" && m.TargetMsg != "" {
			if p, ok := polls[m.TargetMsg]; ok {
				p.Votes[m.Sender] = m.Text
			}
		}
	}

	var latestPassed *Poll
	now := time.Now()
	for _, p := range polls {
		yays, nays := 0, 0
		for _, v := range p.Votes {
			if v == "YAY" {
				yays++
			} else if v == "NAY" {
				nays++
			}
		}
		
		if now.Sub(p.Timestamp) >= 24*time.Hour {
			if yays > nays {
				if latestPassed == nil || p.Timestamp.After(latestPassed.Timestamp) {
					latestPassed = p
				}
			}
		}
	}

	if latestPassed != nil {
		for k, v := range roles {
			if v == RoleOwner {
				roles[k] = RoleMember
			}
		}
		roles[latestPassed.Target] = RoleOwner
	}

	return roles
}

// ==========================================
// P2P Networking & Discovery
// ==========================================

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

func registerPeer(rawURL string, remoteAddr string, doReverse bool) {
	if rawURL == "" {
		return
	}
	peerURL := strings.TrimSpace(rawURL)
	peerURL = strings.TrimRight(peerURL, "/")

	if strings.Contains(peerURL, "localhost") || strings.Contains(peerURL, "127.0.0.1") {
		if remoteAddr != "" {
			host, _, err := net.SplitHostPort(remoteAddr)
			if err == nil {
				if host == "::1" {
					host = "127.0.0.1"
				}
				port := "8080"
				if strings.Contains(peerURL, ":") {
					parts := strings.Split(peerURL, ":")
					port = parts[len(parts)-1]
				}
				peerURL = fmt.Sprintf("http://%s:%s", host, port)
			}
		}
	}

	if !strings.HasPrefix(peerURL, "http://") && !strings.HasPrefix(peerURL, "https://") {
		return
	}
	
	parsed, err := url.Parse(peerURL)
	if err != nil {
		return
	}

	// High Severity Fix: Block strict SSRF Vectors
	ips, err := net.LookupIP(parsed.Hostname())
	if err != nil {
		return
	}
	for _, ip := range ips {
		if ip.IsLoopback() || ip.IsPrivate() || ip.IsMulticast() || ip.IsLinkLocalUnicast() || ip.IsUnspecified() {
			fmt.Printf("[Security] Blocked potential SSRF attempt to IP: %s\n", ip.String())
			return
		}
	}

	myAddr := getLocalIP()
	
	if peerURL == fmt.Sprintf("http://localhost:%s", currentPort) ||
		peerURL == fmt.Sprintf("http://127.0.0.1:%s", currentPort) ||
		peerURL == fmt.Sprintf("http://%s:%s", myAddr, currentPort) {
		return
	}

	checkClient := http.Client{Timeout: 2 * time.Second}
	resp, err := checkClient.Get(peerURL + "/api/identity")
	if err != nil || resp.StatusCode != http.StatusOK {
		return
	}
	if resp != nil {
		resp.Body.Close()
	}

	node.mu.Lock()
	exists := false
	for _, p := range node.Peers {
		if p == peerURL {
			exists = true
			break
		}
	}
	if !exists {
		node.Peers = append(node.Peers, peerURL)
		fmt.Printf("[P2P] Verified & Registered New Peer: %s\n", peerURL)
	}
	node.mu.Unlock()

	if !exists {
		go saveLocalDB()
		if doReverse {
			go func() {
				me := fmt.Sprintf("http://%s:%s", myAddr, currentPort)
				reqPayload, _ := json.Marshal(map[string]string{"url": me})
				client := http.Client{Timeout: 3 * time.Second}
				client.Post(peerURL+"/api/peers", "application/json", bytes.NewBuffer(reqPayload))
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
			
			node.mu.Lock()
			node.Identity.Username = req.Username
			
			// Encrypt and protect keys dynamically
			node.Identity.EncryptedPrivKey = encryptData(node.Identity.PrivateKey, req.Password)
			seedData, _ := json.Marshal(node.Identity.SeedPhrase)
			node.Identity.EncryptedSeed = encryptData(seedData, req.Password)
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
	
	node.mu.Lock()
	defer node.mu.Unlock()
	
	privKey, err1 := decryptData(node.Identity.EncryptedPrivKey, req.Password)
	seedData, err2 := decryptData(node.Identity.EncryptedSeed, req.Password)
	
	if err1 != nil || err2 != nil {
		jsonError(w, "Invalid master password", http.StatusUnauthorized)
		return
	}
	
	node.Identity.PrivateKey = privKey
	json.Unmarshal(seedData, &node.Identity.SeedPhrase)
	isNodeLocked = false
	
	json.NewEncoder(w).Encode(map[string]string{"status": "unlocked"})
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
		node.mu.Unlock()
		
		saveLocalDB()
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
			Action     string `json:"action"` // "ban" or "unban"
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			jsonError(w, "Invalid payload format", http.StatusBadRequest)
			return
		}

		roles := getEffectiveRoles(req.PlatformID)
		myRole := roles[node.Identity.RootHash]
		if myRole != RoleOwner && myRole != RoleAdmin {
			jsonError(w, "Unauthorized action", http.StatusForbidden)
			return
		}

		node.mu.Lock()
		plat := node.Platforms[req.PlatformID]
		
		found := -1
		for i, h := range plat.BannedHashes {
			if h == req.Hash {
				found = i
				break
			}
		}
		
		if req.Action == "ban" && found < 0 {
			plat.BannedHashes = append(plat.BannedHashes, req.Hash)
		} else if req.Action == "unban" && found >= 0 {
			plat.BannedHashes = append(plat.BannedHashes[:found], plat.BannedHashes[found+1:]...)
		}
		
		node.Platforms[req.PlatformID] = plat
		node.mu.Unlock()
		
		saveLocalDB()
		json.NewEncoder(w).Encode(map[string]string{"status": "success"})
	} else {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
	}
}

func apiPeers(w http.ResponseWriter, r *http.Request) {
	if r.Method != "GET" && !checkLocalAuth(w, r) { return } // Let external nodes call GET without auth for basic network polling if allowed
	w.Header().Set("Content-Type", "application/json")
	
	if r.Method == "GET" {
		node.mu.RLock()
		defer node.mu.RUnlock()
		json.NewEncoder(w).Encode(node.Peers)
		return
	}
	
	if r.Method == "POST" {
		var req struct { URL string `json:"url"` }
		json.NewDecoder(r.Body).Decode(&req)
		go registerPeer(req.URL, r.RemoteAddr, true) // Ensure non-blocking
		node.mu.RLock()
		json.NewEncoder(w).Encode(node.Peers)
		node.mu.RUnlock()
	} else {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
	}
}

func apiPlatforms(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }
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
			TTLHours    int    `json:"ttl_hours"`
			Governance  string `json:"governance"`
			ParentID    string `json:"parent_id"` 
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
			jsonError(w, "Invalid payload format", http.StatusBadRequest)
			return
		}

		id := generateID("plat")
		p := Platform{
			ID:          id,
			ParentID:    req.ParentID,
			Name:        req.Name,
			IsEphemeral: req.IsEphemeral,
			Governance:  GovernanceModel(req.Governance),
			Members:     map[string]Role{node.Identity.RootHash: RoleOwner},
		}

		if req.IsEphemeral {
			p.TTL = time.Now().Add(time.Duration(req.TTLHours) * time.Hour)
		}

		node.mu.Lock()
		node.Platforms[id] = p
		node.mu.Unlock()
		
		go saveLocalDB()
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

		if req.ID == "root" {
			jsonError(w, "Cannot leave the root identity ledger platform", http.StatusForbidden)
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
		
		node.mu.Unlock()

		saveLocalDB()
		json.NewEncoder(w).Encode(map[string]string{"status": "success"})
	} else {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
	}
}

func apiMessages(w http.ResponseWriter, r *http.Request) {
	if r.Method != "GET" && !checkLocalAuth(w, r) { return } // Enable paginated GET for remote peers syncing
	w.Header().Set("Content-Type", "application/json")

	if r.Method == "GET" {
		node.mu.RLock()
		platformID := r.URL.Query().Get("platform")
		filtered := make([]Message, 0)
		for _, m := range node.Messages {
			if m.Platform == platformID {
				filtered = append(filtered, m)
			}
		}
		node.mu.RUnlock()
		
		limitStr := r.URL.Query().Get("limit")
		limit := 2000 // Paginate max messages per sync block
		if limitStr != "" {
			fmt.Sscanf(limitStr, "%d", &limit)
		}
		if len(filtered) > limit {
			filtered = filtered[len(filtered)-limit:]
		}

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
		}

		node.Clock.Increment()
		msg.ID = generateID("msg")
		msg.Sender = node.Identity.RootHash
		msg.SenderName = node.Identity.Username
		msg.PublicKey = node.Identity.PublicKey
		msg.Timestamp = time.Now()
		msg.Clock = node.Clock
		msg.IsAcked = false 

		if msg.MsgType == "" {
			msg.MsgType = "TEXT"
		}

		payloadToSign := fmt.Sprintf("%s:%s:%s:%d", msg.ID, msg.Platform, msg.Text, msg.Timestamp.UnixNano())
		sig := ed25519.Sign(node.Identity.PrivateKey, []byte(payloadToSign))
		msg.Signature = hex.EncodeToString(sig)

		node.Messages = append(node.Messages, msg)
		
		if plat, exists := node.Platforms[msg.Platform]; exists {
			if _, memberExists := plat.Members[msg.Sender]; !memberExists {
				plat.Members[msg.Sender] = RoleMember
				node.Platforms[msg.Platform] = plat
			}
		}
		node.mu.Unlock()
		
		go saveLocalDB()
		go broadcastMessageToPeers(msg)

		w.WriteHeader(http.StatusCreated)
		json.NewEncoder(w).Encode(msg)
	} else {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
	}
}

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

		roles := getEffectiveRoles(req.PlatformID)
		myRole := roles[node.Identity.RootHash]
		
		if myRole != RoleOwner && myRole != RoleAdmin {
			jsonError(w, "Unauthorized: Powernode required", http.StatusForbidden)
			return
		}

		var tombstoneMsg Message
		node.mu.Lock()
		node.Clock.Increment()
		for i, m := range node.Messages {
			if m.ID == req.MessageID {
				node.Messages[i].MsgType = "TOMBSTONE"
				node.Messages[i].Text = ""
				node.Messages[i].FileCID = ""
				node.Messages[i].Clock = node.Clock
				node.Messages[i].IsAcked = false 
				tombstoneMsg = node.Messages[i]
				break
			}
		}
		node.mu.Unlock()

		saveLocalDB()

		if tombstoneMsg.ID != "" {
			go broadcastMessageToPeers(tombstoneMsg)
		}
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
			ID:        generateID("inv")[:16],
			Platform:  req.PlatformID,
			MaxUses:   req.MaxUses,
			ExpiresAt: time.Now().Add(time.Duration(req.TTLHours) * time.Hour),
		}

		node.Invites = append(node.Invites, inv)
		node.mu.Unlock()

		payload := InvitePayload{
			PlatformID:   req.PlatformID,
			PlatformName: plat.Name,
			Governance:   string(plat.Governance),
			PeerURL:      fmt.Sprintf("http://%s:%s", getLocalIP(), currentPort),
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

		node.mu.Lock()
		if _, platExists := node.Platforms[payload.PlatformID]; !platExists {
			node.Platforms[payload.PlatformID] = Platform{
				ID:         payload.PlatformID,
				Name:       payload.PlatformName,
				Governance: GovernanceModel(payload.Governance),
				Members:    map[string]Role{node.Identity.RootHash: RoleMember},
			}
		}
		node.mu.Unlock()

		// Background Handshake to prevent locking the UI client
		go registerPeer(payload.PeerURL, "", true)

		go func(peerURL, platformID string) {
			time.Sleep(500 * time.Millisecond) 
			syncURL := fmt.Sprintf("%s/api/messages?platform=%s&limit=1000", peerURL, platformID)
			client := http.Client{Timeout: 5 * time.Second}
			syncResp, err := client.Get(syncURL)
			
			if err == nil && syncResp != nil {
				defer syncResp.Body.Close()

				// LimitReader prevents unbounded payload memory exhaustion/OOM attacks
				limitReader := io.LimitReader(syncResp.Body, 5*1024*1024)

				var pastMsgs []Message
				if err := json.NewDecoder(limitReader).Decode(&pastMsgs); err == nil {
					node.mu.Lock()
					for _, m := range pastMsgs {
						if !verifyMessageSignature(m) {
							continue 
						}

						exists := false
						for _, existing := range node.Messages {
							if existing.ID == m.ID {
								exists = true
								break
							}
						}
						if !exists {
							m.IsAcked = true
							node.Messages = append(node.Messages, m)
							node.Clock.Update(m.Clock)
						}
						
						if plat, ok := node.Platforms[m.Platform]; ok {
							if _, memExists := plat.Members[m.Sender]; !memExists {
								plat.Members[m.Sender] = RoleMember
								node.Platforms[m.Platform] = plat
							}
						}
					}
					node.mu.Unlock()
					saveLocalDB()
				}
			}
		}(strings.TrimRight(strings.TrimSpace(payload.PeerURL), "/"), payload.PlatformID)

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

func apiUploadFile(w http.ResponseWriter, r *http.Request) {
	if !checkLocalAuth(w, r) { return }

	currentSize := getDirSize(fileStoreDir)
	if currentSize > 5*1024*1024*1024 {
		jsonError(w, "Node storage strictly forbids uploads. Hard quota > 5GB exceeded.", http.StatusForbidden)
		return
	}
	
	r.Body = http.MaxBytesReader(w, r.Body, 105<<20)
	err := r.ParseMultipartForm(100 << 20)
	if err != nil {
		jsonError(w, "File too large. Limit is 100MB.", http.StatusBadRequest)
		return
	}

	file, header, err := r.FormFile("file")
	if err != nil {
		jsonError(w, "Invalid file upload structure", http.StatusBadRequest)
		return
	}
	defer file.Close()

	fileKey := make([]byte, 32)
	rand.Read(fileKey)
	iv := make([]byte, 16)
	rand.Read(iv)

	block, _ := aes.NewCipher(fileKey)
	stream := cipher.NewCTR(block, iv)

	hasher := sha256.New()
	tempPath := filepath.Join(fileStoreDir, generateID("temp"))
	outFile, err := os.Create(tempPath)
	if err != nil {
		jsonError(w, "Storage failure", http.StatusInternalServerError)
		return
	}

	outFile.Write(iv) // Prepend IV
	multiWriter := io.MultiWriter(hasher, &cipher.StreamWriter{S: stream, W: outFile})

	io.Copy(multiWriter, file)
	outFile.Close()

	cid := hex.EncodeToString(hasher.Sum(nil))
	finalPath := filepath.Join(fileStoreDir, cid)
	os.Rename(tempPath, finalPath)

	warningMsg := ""
	if currentSize > 2.5*1024*1024*1024 {
		warningMsg = "Warning: Node storage exceeds 2.5GB. Approaching hard limit."
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]string{
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

	var fileKeyHex string
	node.mu.RLock()
	peers := append([]string{}, node.Peers...)
	for _, m := range node.Messages {
		if m.FileCID == cid && m.MsgType == "FILE_TICKET" {
			fileKeyHex = m.Payload
			break
		}
	}
	node.mu.RUnlock()

	if fileKeyHex == "" {
		http.Error(w, "Access Denied: Keys not found on authenticated ledger", http.StatusForbidden)
		return
	}
	aesKey, _ := hex.DecodeString(fileKeyHex)

	path := filepath.Join(fileStoreDir, cid)
	if _, err := os.Stat(path); os.IsNotExist(err) {
		found := false
		for _, peer := range peers {
			client := http.Client{Timeout: 30 * time.Second} 
			resp, err := client.Get(peer + "/p2p/files?cid=" + cid)
			if err == nil && resp.StatusCode == http.StatusOK {
				outFile, err := os.Create(path)
				if err == nil {
					io.Copy(outFile, resp.Body)
					outFile.Close()
					resp.Body.Close()
					found = true
					break
				}
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

	iv := make([]byte, 16)
	io.ReadFull(inFile, iv)

	block, _ := aes.NewCipher(aesKey)
	stream := cipher.NewCTR(block, iv)

	w.Header().Set("Content-Disposition", fmt.Sprintf("attachment; filename=\"%s\"", name))
	w.Header().Set("Content-Type", "application/octet-stream")

	reader := &cipher.StreamReader{S: stream, R: inFile}
	io.Copy(w, reader)
}

func p2pReceiveMessage(w http.ResponseWriter, r *http.Request) {
	// Intentionally lacks checkLocalAuth to allow mesh P2P traffic. Uses Ed25519 signatures to verify data integrity.
	if r.Method == "POST" {
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
		if plat, ok := node.Platforms[msg.Platform]; ok {
			for _, bh := range plat.BannedHashes {
				if bh == msg.Sender {
					node.mu.Unlock()
					w.WriteHeader(http.StatusOK) 
					return
				}
			}
		}

		exists := false
		for _, m := range node.Messages {
			if m.ID == msg.ID {
				if msg.MsgType == "TOMBSTONE" && m.MsgType != "TOMBSTONE" {
					m.MsgType = "TOMBSTONE"
					m.Text = ""
					m.FileCID = ""
					m.Clock = msg.Clock
					exists = false 
				} else {
					exists = true
				}
				break
			}
		}

		if !exists {
			node.Clock.Update(msg.Clock)
			msg.IsAcked = true 
			node.Messages = append(node.Messages, msg)
			
			if plat, ok := node.Platforms[msg.Platform]; ok {
				if _, memExists := plat.Members[msg.Sender]; !memExists {
					plat.Members[msg.Sender] = RoleMember
					node.Platforms[msg.Platform] = plat
				}
			}
		}
		node.mu.Unlock()

		if !exists {
			go saveLocalDB()
		}

		w.WriteHeader(http.StatusOK)
	} else {
		jsonError(w, "Method not allowed", http.StatusMethodNotAllowed)
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

    <!-- UI Overlay Systems (Toasts & Confirm Modals) -->
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

    <!-- Header / Nav -->
    <header class="bg-slate-900 border-b border-slate-700 p-4 flex justify-between items-center shadow-lg z-10">
        <div class="flex items-center space-x-3">
            <div class="w-8 h-8 rounded bg-indigo-500 flex items-center justify-center font-bold text-white shadow-[0_0_15px_rgba(99,102,241,0.5)]">A</div>
            <h1 class="text-xl font-bold tracking-wider">AEGIS <span class="text-xs text-indigo-400 align-top">v2.0-Secure</span></h1>
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
            <div class="p-4 border-b border-slate-800 flex justify-between items-center">
                <h2 class="text-xs font-bold text-slate-400 uppercase tracking-widest">Platforms</h2>
                <div class="flex space-x-1">
                    <button onclick="showJoinModal()" class="bg-slate-800 hover:bg-slate-700 text-slate-300 px-2 py-1 rounded text-xs transition-colors border border-slate-700 shadow-sm" title="Join with Invite Code">+ Join</button>
                    <button onclick="showCreateModal()" class="bg-indigo-600/80 hover:bg-indigo-500 text-white px-2 py-1 rounded text-xs transition-colors border border-indigo-500/50 shadow-sm" title="Create Platform">New</button>
                </div>
            </div>
            <div id="platformsList" class="flex-1 overflow-y-auto p-3 space-y-1">
                <!-- Platforms rendered here -->
            </div>
        </aside>

        <!-- Chat Area -->
        <main class="flex-1 flex flex-col bg-slate-900/60 backdrop-blur-sm relative">
            <div class="p-4 border-b border-slate-800 flex justify-between items-center bg-slate-900/90">
                <div id="activePlatformHeader">
                    <h3 class="font-bold text-lg text-slate-300">Select a Platform</h3>
                </div>
                <div class="flex space-x-2 hidden" id="platformActions">
                    <button onclick="createSubPlatform()" class="text-xs bg-slate-800 hover:bg-slate-700 text-slate-300 px-3 py-1.5 rounded border border-slate-700 transition-colors flex items-center shadow-sm" id="subPlatBtn" style="display:none;">
                        <span class="mr-1">Create Sub-Platform</span>
                    </button>
                    <button onclick="showBannedModal()" class="text-xs bg-slate-800 hover:bg-slate-700 text-slate-300 px-3 py-1.5 rounded border border-slate-700 transition-colors flex items-center shadow-sm" id="bannedUsersBtn" style="display:none;">
                        <span class="mr-1">Banned Users</span>
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
                <!-- Messages populated here -->
            </div>

            <!-- Input Area -->
            <div class="absolute bottom-0 w-full p-4 bg-gradient-to-t from-slate-900 via-slate-900 to-transparent">
                <form id="msgForm" class="flex space-x-2 bg-slate-800/90 backdrop-blur border border-slate-700 p-2 rounded-xl shadow-xl hidden">
                    <input type="file" id="filePicker" class="hidden" onchange="handleFileSelect(event)">
                    <button type="button" onclick="document.getElementById('filePicker').click()" class="bg-slate-700 hover:bg-slate-600 text-slate-300 px-4 py-2 rounded-lg transition-colors border border-slate-600 font-bold" title="Share a file with the mesh">[File]</button>
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

    <!-- Unlock Database Modal -->
    <div id="unlockModal" class="fixed inset-0 bg-black/80 backdrop-blur-sm hidden flex items-center justify-center z-[70]">
        <div class="bg-slate-900 border border-slate-700 p-8 rounded-2xl w-96 shadow-2xl text-center">
            <div class="w-16 h-16 bg-indigo-600 rounded-2xl mx-auto mb-4 flex items-center justify-center text-2xl font-bold shadow-lg shadow-indigo-500/20">
				<svg class="w-8 h-8 text-white" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M12 15v2m-6 4h12a2 2 0 002-2v-6a2 2 0 00-2-2H6a2 2 0 00-2 2v6a2 2 0 002 2zm10-10V7a4 4 0 00-8 0v4h8z"></path></svg>
			</div>
            <h2 class="text-2xl font-bold mb-2">Unlock Node</h2>
            <p class="text-xs text-slate-400 mb-6">Enter your master password to decrypt your identity keys.</p>
            <input type="password" id="unlockPasswordInput" class="w-full bg-slate-800 border border-slate-700 rounded-xl px-4 py-3 text-white outline-none focus:border-indigo-500 mb-4 text-center font-bold" placeholder="Master Password">
            <button onclick="unlockNode()" class="w-full bg-indigo-600 hover:bg-indigo-500 text-white px-4 py-3 rounded-xl font-bold transition-all shadow-lg shadow-indigo-600/30">Unlock Mesh</button>
        </div>
    </div>

    <!-- Username Generation Modal (Mandatory first login) -->
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

    <!-- Create Platform Modal -->
    <div id="createModal" class="fixed inset-0 bg-black/60 backdrop-blur-sm hidden flex items-center justify-center z-[60]">
        <div class="bg-slate-900 border border-slate-700 p-6 rounded-xl w-96 shadow-2xl">
            <h2 class="text-xl font-bold mb-4">Initialize Platform</h2>
            <div class="space-y-4">
                <div>
                    <label class="block text-xs text-slate-400 mb-1">Name</label>
                    <input type="text" id="newPlatName" class="w-full bg-slate-800 border border-slate-700 rounded px-3 py-2 text-white outline-none focus:border-indigo-500" placeholder="# secret-project">
                </div>
                <div>
                    <label class="block text-xs text-slate-400 mb-1">Governance [Spec 7.1]</label>
                    <select id="newPlatGov" class="w-full bg-slate-800 border border-slate-700 rounded px-3 py-2 text-white outline-none focus:border-indigo-500">
                        <option value="PRIVATE_DICTATORSHIP">Dictatorship (Owner Control)</option>
                        <option value="DEMOCRATIC_CONSENSUS">Democracy (Consensus)</option>
                    </select>
                </div>
                <div class="flex items-center space-x-2 mt-2">
                    <input type="checkbox" id="newPlatEph" class="rounded bg-slate-800 border-slate-700 text-indigo-500 focus:ring-indigo-500 focus:ring-offset-slate-900">
                    <label class="text-sm text-slate-300">Ephemeral (Ad-Hoc TTL)</label>
                </div>
            </div>
            <div class="flex justify-end space-x-3 mt-6">
                <button onclick="hideCreateModal()" class="px-4 py-2 text-slate-400 hover:text-white transition-colors">Cancel</button>
                <button onclick="createPlatform()" class="bg-indigo-600 hover:bg-indigo-500 text-white px-4 py-2 rounded transition-colors">Generate Genesis Block</button>
            </div>
        </div>
    </div>

    <!-- Join Platform Modal -->
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

    <!-- Generated Invite Display Modal -->
    <div id="inviteDisplayModal" class="fixed inset-0 bg-black/60 backdrop-blur-sm hidden flex items-center justify-center z-[60]">
        <div class="bg-slate-900 border border-slate-700 p-6 rounded-xl w-[28rem] shadow-2xl">
            <h2 class="text-xl font-bold mb-2">Platform Invite Generated</h2>
            <p class="text-xs text-slate-400 mb-4">Share this code securely with a friend. It contains network mapping and cryptographic keys for them to establish a direct connection to your node.</p>
            <textarea id="generatedInviteCode" class="w-full bg-slate-800 border border-slate-700 rounded px-3 py-2 text-emerald-300 outline-none focus:border-indigo-500 text-xs font-mono h-24 resize-none shadow-inner" readonly></textarea>
            <div class="flex justify-end space-x-3 mt-6">
                <button onclick="hideInviteDisplayModal()" class="px-4 py-2 text-slate-400 hover:text-white transition-colors">Close</button>
                <button onclick="copyInviteCode()" class="bg-emerald-600 hover:bg-emerald-500 text-white px-4 py-2 rounded transition-colors flex items-center">
                    <svg class="w-4 h-4 mr-2" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M8 16H6a2 2 0 01-2-2V6a2 2 0 012-2h8a2 2 0 012 2v2m-6 12h8a2 2 0 002-2v-8a2 2 0 00-2-2h-8a2 2 0 00-2 2v8a2 2 0 002 2z"></path></svg>
                    Copy Code
                </button>
            </div>
        </div>
    </div>

    <!-- Peer Network Modal -->
    <div id="peerModal" class="fixed inset-0 bg-black/60 backdrop-blur-sm hidden flex items-center justify-center z-[60]">
        <div class="bg-slate-900 border border-slate-700 p-6 rounded-xl w-96 shadow-2xl">
            <h2 class="text-xl font-bold mb-4">Network Peers</h2>
            <div class="space-y-4">
                <div id="peerListDisplay" class="bg-slate-800 rounded p-2 text-sm text-slate-300 min-h-[60px] max-h-32 overflow-y-auto">
                    <!-- Peers injected here -->
                </div>
                <div>
                    <label class="block text-xs text-slate-400 mb-1">Add Peer Address (Manual Override)</label>
                    <input type="text" id="newPeerUrl" class="w-full bg-slate-800 border border-slate-700 rounded px-3 py-2 text-white outline-none focus:border-emerald-500" placeholder="http://192.168.1.5:8081">
                </div>
            </div>
            <div class="flex justify-end space-x-3 mt-6">
                <button onclick="hidePeerModal()" class="px-4 py-2 text-slate-400 hover:text-white transition-colors">Close</button>
                <button onclick="addPeer()" class="bg-emerald-600 hover:bg-emerald-500 text-white px-4 py-2 rounded transition-colors">Connect</button>
            </div>
        </div>
    </div>

    <!-- Banned Users Modal -->
    <div id="bannedModal" class="fixed inset-0 bg-black/60 backdrop-blur-sm hidden flex items-center justify-center z-[60]">
        <div class="bg-slate-900 border border-slate-700 p-6 rounded-xl w-96 shadow-2xl">
            <h2 class="text-xl font-bold mb-4 text-red-400">Banned Hash Ledgers</h2>
            <div id="bannedListDisplay" class="bg-slate-800 rounded p-2 text-sm text-slate-300 min-h-[60px] max-h-48 overflow-y-auto space-y-2">
                <!-- Populated via JS -->
            </div>
            <div class="flex justify-end mt-6">
                <button onclick="document.getElementById('bannedModal').classList.add('hidden')" class="px-4 py-2 bg-slate-700 text-white rounded hover:bg-slate-600 transition-colors">Close Control Panel</button>
            </div>
        </div>
    </div>

    <!-- Member Context Menu -->
    <div id="memberContextMenu" class="fixed hidden bg-slate-800 border border-slate-700 rounded-lg shadow-2xl z-[80] w-48 flex flex-col py-1 overflow-hidden" onclick="event.stopPropagation()">
    </div>

    <script>
        // === Core State & Auth ===
        const API_TOKEN = "{{API_TOKEN}}";
        let myId = "";
        let myName = "";
        let myBlockedHashes = [];
        let currentPlatform = "root";
        let platformsCache = {};
        
        let userDir = {}; // Maps Hash -> Username globally based on message history
        let activeUsers = {}; // Maps Hash -> Boolean based on recent mesh activity

        function escapeHTML(str) {
            if (!str) return "";
            return str.replace(/[&<>'"]/g, tag => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', "'": '&#39;', '"': '&quot;'}[tag] || tag));
        }

        // === Custom UI Systems ===
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

        // 1. Identity & Initialization
        fetch('/api/identity', {headers: {'Authorization': 'Bearer ' + API_TOKEN}}).then(async r => {
            if(!r.ok) throw new Error("Server communication failure.");
            return r.json();
        }).then(data => {
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
            fetch('/api/identity', {
                method: 'POST',
                headers: {'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN},
                body: JSON.stringify({username: val, password: pwd})
            }).then(async r => {
                if(!r.ok) throw new Error("Failed to set identity.");
                return r.json();
            }).then(data => {
                document.getElementById('usernameModal').classList.add('hidden');
                showToast("Identity generated and keys securely encrypted.", "success");
                completeInit(data);
            }).catch(err => showToast(err.message, "error"));
        }

        function unlockNode() {
            const pwd = document.getElementById('unlockPasswordInput').value;
            if(!pwd) return;
            fetch('/api/unlock', {
                method: 'POST',
                headers: {'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN},
                body: JSON.stringify({password: pwd})
            }).then(async r => {
                if(!r.ok) throw new Error("Invalid master password");
                document.getElementById('unlockModal').classList.add('hidden');
                showToast("Node Unlocked Successfully", "success");
                
                const res = await fetch('/api/identity', {headers: {'Authorization': 'Bearer ' + API_TOKEN}});
                const data = await res.json();
                completeInit(data);
            }).catch(err => showToast(err.message, "error"));
        }

        function completeInit(data) {
            myId = data.root_hash;
            myName = data.username;
            myBlockedHashes = data.blocked_hashes || [];
            document.getElementById('userIdBox').innerText = escapeHTML(myName) + '#' + escapeHTML(myId).substring(0, 4);
            userDir[myId] = myName;
            
            loadPlatforms();
            loadPeers();
        }

        // 2. Load Platforms
        function loadPlatforms(autoSelectId = null) {
            fetch('/api/platforms', {headers: {'Authorization': 'Bearer ' + API_TOKEN}}).then(async r => {
                if(!r.ok) throw new Error("Failed to fetch platform ledgers.");
                return r.json();
            }).then(data => {
                platformsCache = data;
                const list = document.getElementById('platformsList');
                list.innerHTML = '';
                
                Object.values(data).forEach(p => {
                    const btn = document.createElement('button');
                    const isActive = p.id === currentPlatform;
                    const isSub = p.parent_id !== "";
                    btn.className = 'w-full text-left px-3 py-2.5 rounded-lg transition-all border flex justify-between items-center platform-btn ' + 
                                  (isActive ? 'active' : 'border-transparent text-slate-400 hover:bg-slate-800') + (isSub ? ' ml-4 border-l-2 border-indigo-900 w-11/12' : '');
                    
                    btn.onclick = () => selectPlatform(p.id);

                    let icons = '';
                    if (p.is_ephemeral) icons += '<span class="text-[10px] text-amber-500 ml-2" title="Ad-Hoc / TTL">[TTL]</span>';
                    if (isSub) icons += '<span class="text-[10px] text-indigo-400 ml-2" title="Child Sub-Platform">[SUB]</span>';
                    
                    const govTag = p.governance === 'PRIVATE_DICTATORSHIP' ? 'DICT' : 'DEMO';
                    const govColor = p.governance === 'PRIVATE_DICTATORSHIP' ? 'bg-indigo-900/50 text-indigo-300 border-indigo-700' : 'bg-emerald-900/50 text-emerald-300 border-emerald-700';

                    btn.innerHTML = '<span><span class="opacity-50">#</span> ' + escapeHTML(p.name) + icons + '</span>' +
                                    '<span class="text-[9px] px-1.5 py-0.5 rounded border ' + govColor + '">' + govTag + '</span>';
                    list.appendChild(btn);
                });

                if (autoSelectId && platformsCache[autoSelectId]) selectPlatform(autoSelectId);
                else if (platformsCache[currentPlatform]) selectPlatform(currentPlatform);
                else if (platformsCache["root"]) selectPlatform("root");
            }).catch(e => showToast(e.message, "error"));
        }

        // Load Peers
        function loadPeers() {
            fetch('/api/peers', {headers: {'Authorization': 'Bearer ' + API_TOKEN}}).then(r => r.json()).then(peers => {
                document.getElementById('peerCount').innerText = peers.length + (peers.length === 1 ? ' Peer' : ' Peers');
                
                const dot = document.getElementById('pCountDot');
                dot.className = 'w-2 h-2 rounded-full mr-2 ' + (peers.length > 0 ? 'bg-emerald-400 shadow-[0_0_8px_rgba(52,211,153,0.8)] animate-pulse' : 'bg-slate-600');

                const list = document.getElementById('peerListDisplay');
                if (peers.length === 0) {
                    list.innerHTML = '<span class="text-slate-500 italic">No connected nodes.</span>';
                } else {
                    list.innerHTML = peers.map(p => '<div class="py-1 border-b border-slate-700 last:border-0 font-mono text-emerald-400">[Connected] ' + escapeHTML(p) + '</div>').join('');
                }
            }).catch(e => {}); // Silent failure for heartbeat checks
        }

        // 3. Platform Selection
        function selectPlatform(id) {
            currentPlatform = id;
            const p = platformsCache[id];
            if (!p) return;
            
            document.querySelectorAll('.platform-btn').forEach(b => {
                b.classList.remove('active');
                if(b.innerText.includes(p.name)) b.classList.add('active');
            });

            document.getElementById('msgForm').classList.remove('hidden');
            document.getElementById('platformActions').classList.remove('hidden');

            const govName = p.governance === 'PRIVATE_DICTATORSHIP' ? 'Dictatorship' : 'Democracy';
            document.getElementById('activePlatformHeader').innerHTML = 
                '<h3 class="font-bold flex items-center">' + escapeHTML(p.name) + '</h3>' +
                '<span class="text-xs text-slate-400">CRDT Sync • ' + govName + (p.is_ephemeral ? ' • Ephemeral TTL' : '') + '</span>';

            const leaveBtn = document.getElementById('leaveBtn');
            if(id === 'root') leaveBtn.style.display = 'none';
            else leaveBtn.style.display = 'flex';

            const myRole = p.members[myId];
            const isAdmin = myRole === 'OWNER' || myRole === 'ADMIN';
            document.getElementById('subPlatBtn').style.display = isAdmin ? 'flex' : 'none';
            document.getElementById('bannedUsersBtn').style.display = isAdmin ? 'flex' : 'none';

            // Automatic Presence Broadcast
            fetch('/api/messages', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN },
                body: JSON.stringify({ platform: id, text: "ping", msg_type: "PRESENCE" })
            }).catch(()=>{});

            loadMessages();
        }

        // 4. Messages & UI Rendering
        function loadMessages() {
            if(!currentPlatform) return;
            fetch('/api/messages?platform=' + currentPlatform, {headers: {'Authorization': 'Bearer ' + API_TOKEN}}).then(r => r.json()).then(msgs => {
                const chatBox = document.getElementById('chatBox');
                const isAtBottom = chatBox.scrollHeight - chatBox.scrollTop <= chatBox.clientHeight + 10;
                
                const now = new Date();
                
                msgs.forEach(m => {
                    if (m.sender_name) userDir[m.sender] = m.sender_name;
                    const msgTime = new Date(m.timestamp);
                    if ((now - msgTime) < 10 * 60 * 1000) {
                        activeUsers[m.sender] = true;
                    }
                });
                
                chatBox.innerHTML = '';
                if(!msgs || msgs.length === 0) {
                    chatBox.innerHTML = '<div class="text-center text-slate-600 italic text-sm mt-10">Start the conversation...</div>';
                } else {
                    msgs.sort((a,b) => new Date(a.timestamp) - new Date(b.timestamp));
                    
                    const lockIcon = '<svg class="w-3 h-3 inline-block ml-1 opacity-50 text-indigo-300" fill="currentColor" viewBox="0 0 20 20"><path fill-rule="evenodd" d="M5 9V7a5 5 0 0110 0v2a2 2 0 012 2v5a2 2 0 01-2 2H5a2 2 0 01-2-2v-5a2 2 0 012-2zm8-2v2H7V7a3 3 0 016 0z" clip-rule="evenodd"></path></svg>';
                    
                    let polls = {};
                    msgs.forEach(m => {
                        if (m.msg_type === 'POLL') {
                            polls[m.id] = { yays: 0, nays: 0, timestamp: new Date(m.timestamp), target: m.target_hash, votes: {} };
                        }
                    });
                    msgs.forEach(m => {
                        if (m.msg_type === 'VOTE' && polls[m.target_msg]) {
                            polls[m.target_msg].votes[m.sender] = m.text; // Ensure Vote Stuffing mitigation happens on UI side too
                        }
                    });

                    // Recalculate unique votes
                    Object.keys(polls).forEach(pid => {
                        let y = 0, n = 0;
                        Object.values(polls[pid].votes).forEach(v => {
                            if(v==='YAY') y++; else if(v==='NAY') n++;
                        });
                        polls[pid].yays = y;
                        polls[pid].nays = n;
                    });
                    
                    const platData = platformsCache[currentPlatform];
                    let dynamicRoles = {...(platData ? platData.members : {})};
                    if (platData && platData.governance === 'DEMOCRATIC_CONSENSUS') {
                        let latestPassed = null;
                        Object.keys(polls).forEach(pid => {
                            const p = polls[pid];
                            if ((now - p.timestamp) >= 24*60*60*1000 && p.yays > p.nays) {
                                if (!latestPassed || p.timestamp > latestPassed.timestamp) latestPassed = p;
                            }
                        });
                        if (latestPassed) {
                            Object.keys(dynamicRoles).forEach(k => { if (dynamicRoles[k] === 'OWNER') dynamicRoles[k] = 'MEMBER'; });
                            dynamicRoles[latestPassed.target] = 'OWNER';
                        }
                    }

                    if(platData) {
                        const dr = dynamicRoles[myId];
                        const isAdmin = dr === 'OWNER' || dr === 'ADMIN';
                        document.getElementById('subPlatBtn').style.display = isAdmin ? 'flex' : 'none';
                        document.getElementById('bannedUsersBtn').style.display = isAdmin ? 'flex' : 'none';
                    }
    
                    msgs.forEach(msg => {
                        if (myBlockedHashes.includes(msg.sender) || msg.msg_type === 'PRESENCE') return;
                        
                        const isMe = msg.sender === myId;
                        const displaySender = msg.sender_name ? escapeHTML(msg.sender_name) + '#' + escapeHTML(msg.sender.substring(0, 4)) : escapeHTML(msg.sender.substring(0, 8));
                        
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
                                '<button onclick="downloadFile(\'' + escapeHTML(msg.file_cid) + '\', \'' + escapeHTML(msg.file_name) + '\')" class="w-full py-1.5 bg-slate-700 hover:bg-slate-600 text-xs rounded text-slate-200 transition-colors font-bold shadow-md">Download via Mesh</button>';
                        } else if (msg.msg_type === "SUB_PLATFORM") {
                            bubbleClass = 'max-w-md p-4 rounded-xl bg-indigo-900/50 border border-indigo-700 text-indigo-200';
                            bubbleContent = '<div class="font-bold mb-2 flex items-center"><svg class="w-4 h-4 mr-1 text-indigo-400" fill="none" stroke="currentColor" viewBox="0 0 24 24"><path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M19 11H5m14 0a2 2 0 012 2v6a2 2 0 01-2 2H5a2 2 0 01-2-2v-6a2 2 0 012-2m14 0V9a2 2 0 00-2-2M5 11V9a2 2 0 002-2m0 0V5a2 2 0 012-2h6a2 2 0 012 2v2M7 7h10"></path></svg> Child Platform Issued</div>' + 
                                            '<div class="text-xs mb-3 font-mono bg-indigo-950 p-2 rounded">#' + escapeHTML(msg.text) + '</div>' + 
                                            '<button onclick="joinPlatformCode(\'' + escapeHTML(msg.payload) + '\')" class="bg-indigo-600 hover:bg-indigo-500 px-3 py-2 rounded text-white text-sm font-bold w-full shadow">Accept Transfer</button>';
                        } else if (msg.msg_type === "POLL") {
                            const pData = polls[msg.id] || {yays:0, nays:0};
                            const isPassedStrict = ((now - new Date(msg.timestamp)) >= 24*60*60*1000 && pData.yays > pData.nays);
                            const isCurrentlyWinning = (pData.yays > pData.nays);
                            
                            bubbleClass = 'max-w-md p-4 rounded-xl bg-slate-800 border ' + (isPassedStrict ? 'border-emerald-600 shadow-[0_0_10px_rgba(5,150,105,0.2)]' : 'border-slate-600');
                            bubbleContent = '<div class="font-bold mb-2 flex items-center text-slate-300">🗳️ Server Consensus Poll</div>' + 
                                            '<div class="text-sm mb-3">Nominate <span class="font-mono text-emerald-400 font-bold bg-slate-900 px-1 rounded">' + escapeHTML(msg.target_hash.substring(0,8)) + '</span> for ownership?</div>' + 
                                            (isPassedStrict ? '<div class="text-[10px] font-bold text-emerald-500 mb-2 uppercase tracking-wider">Poll Passed & Action Executed</div>' : (isCurrentlyWinning ? '<div class="text-[10px] text-amber-500 mb-2">Winning (Pending 24hr expiry)</div>' : '<div class="text-[10px] text-slate-500 mb-2">Voting Open (24hr limit)</div>')) +
                                            '<div class="flex space-x-2">' + 
                                                '<button onclick="castVote(\'' + escapeHTML(msg.id) + '\', \'YAY\')" class="flex-1 bg-slate-700 hover:bg-emerald-600/50 py-1.5 rounded text-xs font-bold border border-slate-600">YAY (' + pData.yays + ')</button>' +
                                                '<button onclick="castVote(\'' + escapeHTML(msg.id) + '\', \'NAY\')" class="flex-1 bg-slate-700 hover:bg-red-600/50 py-1.5 rounded text-xs font-bold border border-slate-600">NAY (' + pData.nays + ')</button>' +
                                            '</div>';
                        } else if (msg.msg_type === "VOTE") {
                            return; // Always visually hide underlying votes to reduce spam
                        } else {
                            bubbleContent = escapeHTML(msg.text);
                        }
                        
                        const timeString = new Date(msg.timestamp).toLocaleTimeString([], {hour: '2-digit', minute:'2-digit'});
                        const ackIcon = msg.is_acked ? '<span class="text-emerald-500 font-bold" title="Mesh ACKed (Delivered to Peer)">[Delivered]</span>' : '<span class="text-slate-500" title="Local Only (No peers connected)">[Local]</span>';
                        const hlcInfo = msg.hlc ? '<span class="opacity-40 ml-1" title="HLC Clock">[L:' + msg.hlc.l + ']</span>' : '';
                        const adminBadge = isAdmin && !isMe ? '<span class="text-[9px] bg-amber-500/20 text-amber-500 px-1 rounded ml-1 border border-amber-500/30">ADMIN</span>' : '';
    
                        let actionMenu = '';
                        const myRole = dynamicRoles[myId];
                        if ((myRole === "OWNER" || myRole === "ADMIN") && msg.msg_type !== "TOMBSTONE") {
                            actionMenu = '<button onclick="issueTombstone(\'' + escapeHTML(msg.id) + '\')" class="text-[10px] text-red-400 hover:text-red-300 ml-2">Drop (Tombstone)</button>';
                        }
    
                        div.innerHTML = '<div class="' + bubbleClass + '">' + bubbleContent + '</div>' +
                            '<div class="text-[10px] text-slate-500 mt-1 px-1 flex items-center">' +
                                (isMe ? timeString + hlcInfo + actionMenu + ' <span class="mx-1">•</span> You ' + lockIcon + ' ' + ackIcon : displaySender + adminBadge + ' <span class="mx-1">•</span> ' + timeString + hlcInfo + actionMenu + ' ' + lockIcon) +
                            '</div>';
                        
                        chatBox.appendChild(div);
                    });
                }
                
                if (isAtBottom) chatBox.scrollTop = chatBox.scrollHeight;
                
                renderMembers();
            }).catch(e => {}); // Silent fail on heartbeat loops
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
                closeMemberMenu(); // close menu if open
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
                // If they are banned at a platform level, do not render them in the general members list
                if (plat.banned_hashes && plat.banned_hashes.includes(hash)) return;

                let name = userDir[hash] || (hash === myId ? myName : "Unknown User");
                if (searchStr && !name.toLowerCase().includes(searchStr)) return;

                let isOnline = (hash === myId) || !!activeUsers[hash];
                let role = plat.members[hash];

                const memObj = {hash, name, role, isOnline};
                if (isOnline) online.push(memObj); else offline.push(memObj);
            });

            // Sort A-Z strictly within presence chunks
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
            const blockStyle = isBlocked ? 'opacity-40 grayscale' : '';
            const roleBadge = (m.role === 'OWNER' || m.role === 'ADMIN') ? '<span class="text-[8px] bg-amber-500/20 text-amber-500 px-1 rounded border border-amber-500/30 ml-2">ADMIN</span>' : '';
            const statusColor = m.isOnline ? 'bg-emerald-500 shadow-[0_0_5px_rgba(16,185,129,0.8)]' : 'bg-slate-600 border-slate-700';
            const displayHash = m.hash.substring(0,4);
            const initial = m.name.substring(0,1).toUpperCase() || '?';
            
            return '<div onclick="showMemberMenu(event, \''+escapeHTML(m.hash)+'\', \''+escapeHTML(m.name)+'\')" class="flex items-center cursor-pointer hover:bg-slate-800 p-1.5 rounded transition-colors ' + blockStyle + '">' +
                '<div class="relative">' +
                    '<div class="w-8 h-8 bg-indigo-600/80 border border-indigo-500/50 rounded flex items-center justify-center text-sm font-bold text-white mr-3 shadow-inner">' + escapeHTML(initial) + '</div>' +
                    '<div class="absolute -bottom-0.5 -right-0.5 w-3 h-3 ' + statusColor + ' border-2 border-slate-900 rounded-full"></div>' +
                '</div>' +
                '<div class="flex-1 overflow-hidden">' +
                    '<div class="truncate text-sm text-slate-200 font-medium">' + escapeHTML(m.name) + roleBadge + '</div>' +
                    '<div class="text-[10px] text-slate-500 font-mono">#' + escapeHTML(displayHash) + (isBlocked ? ' (Blocked)' : '') + '</div>' +
                '</div>' +
            '</div>';
        }

        // --- Context Menu Logic ---

        function showMemberMenu(event, hash, name) {
            event.stopPropagation(); // prevent closing instantly
            if (hash === myId) return;

            const menu = document.getElementById('memberContextMenu');
            menu.style.top = event.clientY + 'px';
            menu.style.left = (event.clientX - 160) + 'px'; 
            menu.classList.remove('hidden');

            const isBlocked = myBlockedHashes.includes(hash);
            const plat = platformsCache[currentPlatform];
            const myRole = plat ? plat.members[myId] : null;
            const isAdmin = myRole === 'OWNER' || myRole === 'ADMIN';
            const isDemocracy = plat && plat.governance === 'DEMOCRATIC_CONSENSUS';
            
            let html = '<div class="px-4 py-2 border-b border-slate-700 text-xs font-bold text-slate-300 truncate">' + escapeHTML(name) + '</div>' +
                '<button onclick="startDM(\'' + escapeHTML(hash) + '\', \'' + escapeHTML(name) + '\')" class="w-full text-left px-4 py-2 text-sm hover:bg-slate-700 transition-colors ' + (isBlocked ? 'opacity-30 cursor-not-allowed' : 'text-slate-200') + '" ' + (isBlocked ? 'disabled' : '') + '>Direct Message</button>' +
                '<button onclick="toggleBlock(\'' + escapeHTML(hash) + '\')" class="w-full text-left px-4 py-2 text-sm hover:bg-slate-700 text-red-400 transition-colors font-medium border-t border-slate-700/50">' + (isBlocked ? 'Unblock User' : 'Block User') + '</button>';
            
            if (isAdmin) {
                html += '<button onclick="banFromPlatform(\'' + escapeHTML(hash) + '\')" class="w-full text-left px-4 py-2 text-sm hover:bg-slate-700 text-red-500 transition-colors font-medium border-t border-slate-700/50">Ban from Platform</button>';
            }
            if (isDemocracy) {
                html += '<button onclick="nominateLeader(\'' + escapeHTML(hash) + '\')" class="w-full text-left px-4 py-2 text-sm hover:bg-slate-700 text-emerald-400 transition-colors font-medium border-t border-slate-700/50">Nominate Leader</button>';
            }

            menu.innerHTML = html;
            document.addEventListener('click', closeMemberMenu, {once: true});
        }

        function closeMemberMenu() {
            document.getElementById('memberContextMenu').classList.add('hidden');
        }

        // --- Sub-Platform & Governance Action Functions ---

        function startDM(hash, name) {
            closeMemberMenu();
            showConfirm("Secure DM Protocol", "To DM securely via P2P:\n\n1. Click 'New Platform'.\n2. Name it something private.\n3. Generate an invite and send it to them via an out-of-band secure channel.", ()=>{}, "Understood", "bg-indigo-600 hover:bg-indigo-500");
        }

        function toggleBlock(hash) {
            closeMemberMenu();
            fetch('/api/block', {
                method: 'POST',
                headers: {'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN},
                body: JSON.stringify({hash: hash})
            }).then(async r => {
                if(!r.ok) throw new Error(await r.text());
                showToast("User blocking updated.", "success");
                return fetch('/api/identity', {headers: {'Authorization': 'Bearer ' + API_TOKEN}}).then(r=>r.json());
            }).then(data => {
                myBlockedHashes = data.blocked_hashes || [];
                loadMessages(); 
            }).catch(e => showToast("Network Error: " + e.message, "error"));
        }

        function banFromPlatform(hash) {
            closeMemberMenu();
            showConfirm("Ban User", "Are you sure you want to permanently ban this cryptographic hash from the platform?", (confirmed) => {
                if(!confirmed) return;
                fetch('/api/platforms/ban', {
                    method: 'POST',
                    headers: {'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN},
                    body: JSON.stringify({platform_id: currentPlatform, hash: hash, action: 'ban'})
                }).then(async r => {
                    if(!r.ok) throw new Error(await r.text());
                    showToast("User securely banished from ledger.", "success");
                    loadPlatforms(currentPlatform);
                    loadMessages();
                }).catch(e => showToast("Ban Error: " + e.message, "error"));
            });
        }

        function showBannedModal() {
            const plat = platformsCache[currentPlatform];
            if(!plat) return;
            const list = document.getElementById('bannedListDisplay');
            list.innerHTML = '';
            if(!plat.banned_hashes || plat.banned_hashes.length === 0) {
                list.innerHTML = '<div class="text-slate-500 italic p-2 text-center mt-4">No banned users on this ledger.</div>';
            } else {
                plat.banned_hashes.forEach(h => {
                    const name = userDir[h] || 'Unknown Hash Ledger';
                    list.innerHTML += '<div class="flex justify-between items-center bg-slate-700/50 p-3 rounded mb-2">' + 
                        '<span>' + escapeHTML(name) + ' <span class="text-xs font-mono text-indigo-400 ml-2">#' + escapeHTML(h.substring(0,6)) + '</span></span>' +
                        '<button onclick="unbanUser(\''+escapeHTML(h)+'\')" class="text-xs bg-indigo-600 hover:bg-indigo-500 px-3 py-1.5 font-bold text-white rounded shadow">Unban</button></div>';
                });
            }
            document.getElementById('bannedModal').classList.remove('hidden');
        }

        function unbanUser(hash) {
            fetch('/api/platforms/ban', {
                method: 'POST',
                headers: {'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN},
                body: JSON.stringify({platform_id: currentPlatform, hash: hash, action: 'unban'})
            }).then(async r => {
                if(!r.ok) throw new Error(await r.text());
                showToast("Hash unbanned successfully.", "success");
                document.getElementById('bannedModal').classList.add('hidden');
                loadPlatforms(currentPlatform);
            }).catch(e => showToast("Error: " + e.message, "error"));
        }

        function nominateLeader(hash) {
            closeMemberMenu();
            fetch('/api/messages', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN },
                body: JSON.stringify({ platform: currentPlatform, msg_type: "POLL", target_hash: hash })
            }).then(loadMessages).catch(e => showToast("Consensus Dispatch Failed: " + e.message, "error"));
        }

        function castVote(pollId, voteType) {
            fetch('/api/messages', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN },
                body: JSON.stringify({ platform: currentPlatform, msg_type: "VOTE", target_msg: pollId, text: voteType })
            }).then(()=>showToast("Voted " + voteType + " mapped securely to DAG.", "success")).then(loadMessages).catch(e => showToast(e.message, "error"));
        }

        function createSubPlatform() {
            const name = prompt("Enter the title for the new Sub-Platform:");
            if(!name) return;

            fetch('/api/platforms', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN },
                body: JSON.stringify({ name: name, governance: 'DEMOCRATIC_CONSENSUS', is_ephemeral: false, ttl_hours: 0, parent_id: currentPlatform })
            }).then(async r => {
                if(!r.ok) throw new Error(await r.text());
                return r.json();
            }).then(p => {
                return fetch('/api/invites', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN },
                    body: JSON.stringify({ platform_id: p.id, max_uses: 1000, ttl_hours: 8760 }) // basically forever
                });
            }).then(async r => {
                if(!r.ok) throw new Error(await r.text());
                return r.json();
            }).then(inv => {
                fetch('/api/messages', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN },
                    body: JSON.stringify({ platform: currentPlatform, msg_type: "SUB_PLATFORM", payload: inv.invite_code, text: name })
                }).then(() => {
                    showToast("Sub-Platform dispatched successfully.", "success");
                    loadPlatforms(currentPlatform); // remain in parent, just refresh
                });
            }).catch(e => showToast("Init Error: " + e.message, "error"));
        }

        // Hook reused for both direct invite paste and sub-platform button pushes
        function joinPlatformCode(code) {
            document.getElementById('inviteCodeInput').value = code;
            joinPlatform();
        }

        // 5. User Actions
        document.getElementById('msgForm').addEventListener('submit', (e) => {
            e.preventDefault();
            const input = document.getElementById('msgInput');
            if (!input.value.trim() || !currentPlatform) return;

            fetch('/api/messages', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN },
                body: JSON.stringify({ platform: currentPlatform, text: input.value.trim(), msg_type: "TEXT" })
            }).then(async r => {
                if(!r.ok) throw new Error(await r.text());
                input.value = '';
                loadMessages();
            }).catch(e => showToast(e.message, "error"));
        });

        // --- File Sharing Logic ---
        
        async function handleFileSelect(event) {
            const file = event.target.files[0];
            if (!file) return;

            if (file.size > 100 * 1024 * 1024) {
                showToast("File too large. Mesh limit is currently 100MB per file.", "error");
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
                
                if (!res.ok) throw new Error(await res.text());
                const data = await res.json();
				
				if (data.warning) showToast(data.warning, "info");

                await fetch('/api/messages', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN },
                    body: JSON.stringify({ 
                        platform: currentPlatform, 
                        msg_type: "FILE_TICKET", 
                        file_cid: data.cid,
                        file_name: data.name,
                        payload: data.key // Disperse AES key via authenticated CRDT message mesh
                    })
                });

                btn.innerHTML = origText;
                showToast("File ticket dispatched to mesh layer.", "success");
                loadMessages();
            } catch (err) {
                showToast("Encryption/Upload failed: " + err.message, "error");
                document.querySelector('button[title="Share a file with the mesh"]').innerHTML = "[File]";
            }
            
            event.target.value = ''; 
        }

        function downloadFile(cid, name) {
            showToast("Beginning local decryption and file stream...", "info");
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

        // --- Core Moderation ---

        function issueTombstone(messageId) {
            fetch('/api/moderate', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN },
                body: JSON.stringify({ message_id: messageId, platform_id: currentPlatform })
            }).then(async r => {
                if(!r.ok) throw new Error(await r.text());
                showToast("Tombstone executed successfully.", "success");
                loadMessages();
            }).catch(e => showToast("Mod Error: " + e.message, "error"));
        }

        function leavePlatform() {
            if(!currentPlatform || currentPlatform === 'root') {
                showToast("Cannot leave the local root mesh.", "error");
                return;
            }
            
            showConfirm("Leave Platform", "Are you sure you want to leave this platform? All local data copies for it will be explicitly purged.", (confirmed) => {
                if(!confirmed) return;
                fetch('/api/platforms/leave', {
                    method: 'POST',
                    headers: { 'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN },
                    body: JSON.stringify({ id: currentPlatform })
                }).then(async r => {
                    if(!r.ok) throw new Error(await r.text());
                    showToast("Left platform securely.", "success");
                    currentPlatform = 'root';
                    loadPlatforms('root');
                }).catch(e => showToast("Purge Error: " + e.message, "error"));
            });
        }

        // --- INVITE SYSTEM Logic ---

        function generateInvite() {
            fetch('/api/invites', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN },
                body: JSON.stringify({ platform_id: currentPlatform, max_uses: 5, ttl_hours: 24 })
            }).then(async r => {
                if(!r.ok) throw new Error(await r.text());
                return r.json();
            }).then(data => {
                document.getElementById('generatedInviteCode').value = data.invite_code;
                document.getElementById('inviteDisplayModal').classList.remove('hidden');
                showToast("Invite payload encrypted and generated.", "success");
            }).catch(e => showToast("Invite Auth Failure: " + e.message, "error"));
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

        function joinPlatform() {
            const code = document.getElementById('inviteCodeInput').value.trim();
            if(!code) return;

            showToast("Negotiating payload and authenticating...", "info");

            fetch('/api/join', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN },
                body: JSON.stringify({ invite_code: code })
            }).then(async r => {
                if(!r.ok) throw new Error(await r.text());
                hideJoinModal();
                showToast("Joined mesh! Synchronizing CRDT ledger...", "success");
                try {
                    const payload = JSON.parse(atob(code));
                    loadPlatforms(payload.platform_id);
                } catch(e) {
                    loadPlatforms();
                }
                loadPeers();
            }).catch(e => showToast("Join Request Rejected: " + e.message, "error"));
        }

        // --- Network Logic ---

        function addPeer() {
            const url = document.getElementById('newPeerUrl').value.trim();
            if(!url) return;
            fetch('/api/peers', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN },
                body: JSON.stringify({ url: url })
            }).then(async r => {
                if(!r.ok) throw new Error(await r.text());
                document.getElementById('newPeerUrl').value = '';
                showToast("Peer handshaking initiated.", "info");
                loadPeers();
            }).catch(e => showToast("Peer Exception: " + e.message, "error"));
        }

        // Modal Controls
        function showCreateModal() { document.getElementById('createModal').classList.remove('hidden'); }
        function hideCreateModal() { document.getElementById('createModal').classList.add('hidden'); }
        function showPeerModal() { document.getElementById('peerModal').classList.remove('hidden'); loadPeers(); }
        function hidePeerModal() { document.getElementById('peerModal').classList.add('hidden'); }
        
        function createPlatform() {
            const name = document.getElementById('newPlatName').value || "unnamed-plat";
            const gov = document.getElementById('newPlatGov').value;
            const eph = document.getElementById('newPlatEph').checked;

            fetch('/api/platforms', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json', 'Authorization': 'Bearer ' + API_TOKEN },
                body: JSON.stringify({ name: name, governance: gov, is_ephemeral: eph, ttl_hours: eph ? 24 : 0, parent_id: "" })
            }).then(async r => {
                if(!r.ok) throw new Error(await r.text());
                hideCreateModal();
                showToast("Genesis block generated for " + name, "success");
                loadPlatforms();
            }).catch(e => showToast("Creation Failure: " + e.message, "error"));
        }

        // Polling loop
        setInterval(loadMessages, 2000);
    </script>
</body>
</html>`