package main

import (
	"bytes"
	"compress/gzip"
	"crypto/ed25519"
	"crypto/rand"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"html"
	"io"
	"log"
	"net"
	"net/http"
	"os"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"sync"
	"time"
)

// =============================================================================
// [System Constants & Architecture Specs]
// =============================================================================

const (
	RelayVersion      = "v3.0.0-PRO-STICKY"
	MaxTrafficEntries = 150               // Number of live traffic lines to keep in memory
	MaxMessageMemory  = 250000            // Threshold before memory-to-disk offloading (placeholder)
	DefaultPort       = "8080"
	DefaultDiskGB     = 20
	DefaultRetention  = 14                // Extended retention for persistent mesh
	AuthExpiryMinutes = 15                // Signature drift allowance for high-latency nodes
	HandshakeTimeout  = 5 * time.Second
	GCInterval        = 1 * time.Hour
)

// =============================================================================
// [Aegis Protocol Structs]
// =============================================================================

// HLC (Hybrid Logical Clock) provides causal ordering of events without 
// requiring perfect clock synchronization across the distributed mesh.
type HLC struct {
	Physical int64 `json:"p"` // Wall clock time (nanoseconds)
	Logical  int   `json:"l"` // Monotonic counter for concurrent events
}

// Update implements the HLC advancement algorithm.
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
		h.Physical = maxPhysical
		if remote.Logical > h.Logical {
			h.Logical = remote.Logical + 1
		} else {
			h.Logical++
		}
	}
}

// Message is the atomic unit of the Aegis protocol.
type Message struct {
	ID         string    `json:"id"`          // Unique message UUID
	Platform   string    `json:"platform"`    // Destination platform ID
	Sender     string    `json:"sender"`      // Sender's RootHash (SHA256 of PubKey)
	SenderName string    `json:"sender_name"` // Display name (metadata)
	Text       string    `json:"text"`        // Encrypted payload or system command
	Timestamp  time.Time `json:"timestamp"`

	Clock      HLC               `json:"hlc"`
	VectorMap  map[string]uint64 `json:"vector_map"` // Causality tracking
	MsgType    string            `json:"msg_type"`   // TEXT, FILE_TICKET, PRESENCE, TOMBSTONE, etc.
	TargetHash string            `json:"target_hash,omitempty"`
	Payload    string            `json:"payload,omitempty"`
	FileCID    string            `json:"file_cid,omitempty"`
	FileName   string            `json:"file_name,omitempty"`
	FileSize   int64             `json:"file_size,omitempty"`
	IsAcked    bool              `json:"is_acked"`
	AckedBy    []string          `json:"acked_by,omitempty"`
	
	PublicKey  string            `json:"public_key"` // Sender's Ed25519 Public Key
	Signature  string            `json:"signature"`  // Ed25519 Signature of payload
}

// RelayNode encapsulates the entire state of the persistent matchmaker.
type RelayNode struct {
	RootHash       string
	PublicKey      string
	PrivateKey     []byte
	Messages       []Message
	Peers          map[string]time.Time // Tracks URL -> JoinTime
	SeenSignatures map[string]int64     // Replay protection: Signature -> ExpiryNano
	Clock          HLC
	LastUpdate     int64                // Milliseconds since epoch for sync delta
	StartTime      time.Time
	mu             sync.RWMutex
}

// SystemMetrics provides real-time telemetry for the dashboard.
type SystemMetrics struct {
	TotalMessages    uint64  `json:"total_messages"`
	TotalFiles       uint64  `json:"total_files"`
	ActivePeerCount  int     `json:"active_peers"`
	UnreachablePeers int     `json:"unreachable_peers"`
	DiskUsageBytes   int64   `json:"disk_usage_bytes"`
	MemoryAllocated  uint64  `json:"memory_allocated"`
	Goroutines       int     `json:"goroutines"`
	UptimeSeconds    float64 `json:"uptime_seconds"`
}

// =============================================================================
// [Global State Management]
// =============================================================================

var (
	node          *RelayNode
	metrics       SystemMetrics
	serverPort    string
	fileStoreDir  = "aegis_relay_files"
	maxDiskBytes  int64
	maxRetention  time.Duration
	
	// Networking Security
	ipTracker = make(map[string][]time.Time)
	ipMutex   sync.Mutex

	// Logging & Dashboard Buffers
	trafficLog   []string
	trafficMutex sync.Mutex
)

// =============================================================================
// [Boot & Lifecycle Management]
// =============================================================================

func main() {
	// 1. Configuration Parsing
	portFlag := flag.String("port", DefaultPort, "TCP Port for the Relay")
	diskFlag := flag.Int64("max-disk", DefaultDiskGB, "Storage quota in GB")
	retentionFlag := flag.Int("retention", DefaultRetention, "Retention days for stale data")
	flag.Parse()

	serverPort = *portFlag
	maxDiskBytes = *diskFlag * 1024 * 1024 * 1024
	maxRetention = time.Duration(*retentionFlag) * 24 * time.Hour

	// 2. Logging Setup
	setupLogger()

	log.Println("==========================================================")
	log.Printf("🛡️  AEGIS CLOUD RELAY CORE %s", RelayVersion)
	log.Println("==========================================================")
	log.Printf("[System] Mode: PERSISTENT MESH (Manual Disconnect Only)")
	log.Printf("[System] Quota: %d GB | Retention: %d Days", *diskFlag, *retentionFlag)

	// 3. Filesystem Prep
	if err := os.MkdirAll(fileStoreDir, 0700); err != nil {
		log.Fatalf("[Critical] Storage initialization failed: %v", err)
	}

	// 4. Cryptographic Identity Generation
	initRelayIdentity()

	// 5. Route Registration
	mux := http.NewServeMux()
	
	// Administrative & Monitoring
	mux.HandleFunc("/", withCORS(withGzip(serveLanding)))
	mux.HandleFunc("/api/ping", withCORS(withGzip(apiPing)))
	mux.HandleFunc("/api/metrics", withCORS(withGzip(apiMetrics)))
	
	// Peer Management (PEX)
	mux.HandleFunc("/api/peers", withCORS(withGzip(apiPeers)))
	
	// Mesh Messaging (Sync & Push)
	mux.HandleFunc("/api/messages", withCORS(withGzip(apiMessagesSync)))
	mux.HandleFunc("/p2p/sync", withCORS(withGzip(apiMessagesSync)))
	mux.HandleFunc("/p2p/message", withCORS(withRateLimit(p2pReceiveMessage)))
	
	// Object Storage (Files)
	mux.HandleFunc("/api/files/download", withCORS(p2pServeFile))
	mux.HandleFunc("/p2p/files", withCORS(p2pServeFile))
	mux.HandleFunc("/p2p/files/push", withCORS(withRateLimit(p2pReceiveFile)))

	// 6. Background Service Spawning
	go maintenanceLoop()       // Peer health & ping tracking
	go garbageCollectionLoop() // Disk & Memory pruning
	go metricsLoop()           // Telemetry gathering

	// 7. Server Start
	log.Printf("[Network] Listening on 0.0.0.0:%s", serverPort)
	server := &http.Server{
		Addr:         ":" + serverPort,
		Handler:      mux,
		ReadTimeout:  15 * time.Second,
		WriteTimeout: 60 * time.Second,
		IdleTimeout:  120 * time.Second,
	}

	if err := server.ListenAndServe(); err != nil {
		log.Fatalf("[Fatal] ListenAndServe failed: %v", err)
	}
}

func setupLogger() {
	logFile, err := os.OpenFile("relay.log", os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0666)
	if err != nil {
		fmt.Printf("Critical: Log system failure: %v\n", err)
		os.Exit(1)
	}
	// Duplex output to stdout and log file
	log.SetOutput(io.MultiWriter(os.Stdout, logFile))
	log.SetFlags(log.Ldate | log.Ltime | log.Lmicroseconds)
}

func initRelayIdentity() {
	pub, priv, err := ed25519.GenerateKey(rand.Reader)
	if err != nil {
		log.Fatalf("[Crypto] Keygen failure: %v", err)
	}
	hash := sha256.Sum256(pub)
	
	node = &RelayNode{
		RootHash:       hex.EncodeToString(hash[:]),
		PublicKey:      hex.EncodeToString(pub),
		PrivateKey:     priv,
		Messages:       make([]Message, 0),
		Peers:          make(map[string]time.Time),
		SeenSignatures: make(map[string]int64),
		Clock:          HLC{Physical: time.Now().UnixNano(), Logical: 0},
		LastUpdate:     time.Now().UnixMilli(),
		StartTime:      time.Now(),
	}
	log.Printf("[Crypto] Relay Identity Hash: %s", node.RootHash)
}

// =============================================================================
// [Middleware & Performance Optimization]
// =============================================================================

type gzipResponseWriter struct {
	io.Writer
	http.ResponseWriter
}

func (w gzipResponseWriter) Write(b []byte) (int, error) {
	return w.Writer.Write(b)
}

// withGzip applies transparent compression to JSON/HTML payloads.
func withGzip(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if !strings.Contains(r.Header.Get("Accept-Encoding"), "gzip") {
			next.ServeHTTP(w, r)
			return
		}
		w.Header().Set("Content-Encoding", "gzip")
		gz := gzip.NewWriter(w)
		defer gz.Close()
		next.ServeHTTP(gzipResponseWriter{Writer: gz, ResponseWriter: w}, r)
	}
}

// withCORS facilitates cross-origin mesh handshakes.
func withCORS(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Access-Control-Allow-Origin", "*")
		w.Header().Set("Access-Control-Allow-Methods", "POST, GET, OPTIONS, DELETE")
		w.Header().Set("Access-Control-Allow-Headers", "Accept, Content-Type, Content-Length, Authorization")
		
		if r.Method == "OPTIONS" {
			w.WriteHeader(http.StatusOK)
			return
		}
		next.ServeHTTP(w, r)
	}
}

// withRateLimit defends against connection exhaustion and spam.
func withRateLimit(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		ip, _, _ := net.SplitHostPort(r.RemoteAddr)
		
		ipMutex.Lock()
		now := time.Now()
		timestamps := ipTracker[ip]
		
		var valid []time.Time
		for _, t := range timestamps {
			if now.Sub(t) < 10*time.Second {
				valid = append(valid, t)
			}
		}
		valid = append(valid, now)
		ipTracker[ip] = valid
		
		if len(valid) > 40 { // Slightly relaxed for high-speed mesh sync
			ipMutex.Unlock()
			log.Printf("[Security] Throttling suspected spammer: %s", ip)
			http.Error(w, "Rate limit exceeded. Mesh cooling down.", http.StatusTooManyRequests)
			return
		}
		ipMutex.Unlock()
		next.ServeHTTP(w, r)
	}
}

// =============================================================================
// [Core Protocol Engine]
// =============================================================================

func verifyMessageSignature(msg Message) bool {
	node.mu.RLock()
	if _, seen := node.SeenSignatures[msg.Signature]; seen {
		node.mu.RUnlock()
		return false // Replay attack detected
	}
	node.mu.RUnlock()

	pubBytes, err := hex.DecodeString(msg.PublicKey)
	if err != nil || len(pubBytes) != ed25519.PublicKeySize {
		return false
	}

	// Verify the hash of the public key matches the declared sender hash
	hash := sha256.Sum256(pubBytes)
	if hex.EncodeToString(hash[:]) != msg.Sender {
		return false
	}

	sigBytes, err := hex.DecodeString(msg.Signature)
	if err != nil || len(sigBytes) != ed25519.SignatureSize {
		return false
	}

	// Reconstruct the payload for verification (Protocol Design 4.2)
	payloadToVerify := fmt.Sprintf("%d:%s:%d:%s:%d:%s:%d:%s:%d:%s:%d:%s:%d",
		len(msg.ID), msg.ID, 
		len(msg.Platform), msg.Platform, 
		len(msg.MsgType), msg.MsgType,
		len(msg.TargetHash), msg.TargetHash, 
		len(msg.Text), msg.Text, 
		len(msg.FileCID), msg.FileCID,
		msg.Timestamp.UnixNano())

	if !ed25519.Verify(pubBytes, []byte(payloadToVerify), sigBytes) {
		return false
	}

	// Signature Age Validation
	drift := time.Since(msg.Timestamp)
	if drift > time.Duration(AuthExpiryMinutes)*time.Minute || drift < -time.Duration(AuthExpiryMinutes)*time.Minute {
		return false
	}

	// Cache signature to prevent replay
	node.mu.Lock()
	node.SeenSignatures[msg.Signature] = time.Now().UnixNano()
	node.mu.Unlock()

	return true
}

func broadcastMessageToPeers(msg Message) {
	node.mu.RLock()
	peers := make([]string, 0, len(node.Peers))
	for p := range node.Peers {
		peers = append(peers, p)
	}
	node.mu.RUnlock()

	if len(peers) == 0 {
		return
	}

	payload, _ := json.Marshal(msg)
	for _, peerURL := range peers {
		go func(pURL string) {
			client := http.Client{Timeout: HandshakeTimeout}
			client.Post(pURL+"/p2p/message", "application/json", bytes.NewBuffer(payload))
		}(peerURL)
	}
}

// =============================================================================
// [API Implementation]
// =============================================================================

func serveLanding(w http.ResponseWriter, r *http.Request) {
	trafficMutex.Lock()
	trafficHTML := ""
	for _, logLine := range trafficLog {
		trafficHTML += fmt.Sprintf("<div class='log-line'>%s</div>", html.EscapeString(logLine))
	}
	trafficMutex.Unlock()

	node.mu.RLock()
	uptime := time.Since(node.StartTime).Round(time.Second)
	msgCount := len(node.Messages)
	peerCount := len(node.Peers)
	node.mu.RUnlock()

	w.Header().Set("Content-Type", "text/html")
	fmt.Fprintf(w, `<!DOCTYPE html>
	<html>
	<head>
		<title>Aegis Cloud Relay Console</title>
		<meta http-equiv="refresh" content="5">
		<style>
			:root { --bg: #0f172a; --card: #1e293b; --accent: #10b981; --text: #f8fafc; --muted: #64748b; }
			body { background: var(--bg); color: var(--text); font-family: 'JetBrains Mono', monospace; padding: 2rem; margin: 0; display: flex; justify-content: center; }
			.card { background: var(--card); border: 1px solid #334155; border-radius: 16px; padding: 2.5rem; width: 100%%; max-width: 1000px; box-shadow: 0 25px 50px -12px rgba(0,0,0,0.5); }
			h1 { color: var(--accent); margin: 0 0 1rem 0; font-size: 1.5rem; border-left: 4px solid var(--accent); padding-left: 1rem; }
			.grid { display: grid; grid-template-cols: repeat(4, 1fr); gap: 1.5rem; margin: 2rem 0; }
			.box { background: var(--bg); border: 1px solid #334155; padding: 1.25rem; border-radius: 12px; text-align: center; }
			.val { display: block; font-size: 1.5rem; font-weight: 800; color: #38bdf8; }
			.label { font-size: 0.65rem; color: var(--muted); text-transform: uppercase; letter-spacing: 0.1em; margin-top: 0.5rem; }
			.feed-container { background: var(--bg); border-radius: 12px; padding: 1rem; border: 1px solid #334155; height: 400px; overflow-y: auto; }
			.log-line { font-size: 0.8rem; padding: 0.4rem 0; border-bottom: 1px solid #1e293b; color: #cbd5e1; white-space: pre-wrap; }
			.footer { margin-top: 2rem; text-align: center; color: var(--muted); font-size: 0.7rem; }
		</style>
	</head>
	<body>
		<div class="card">
			<h1>AEGIS CLOUD RELAY CORE - CONSOLE</h1>
			<p style="color:var(--muted); font-size: 0.9rem;">Relay Hash: <code style="color:var(--accent)">%s</code></p>
			
			<div class="grid">
				<div class="box"><span class="val">%d</span><span class="label">Peers</span></div>
				<div class="box"><span class="val">%d</span><span class="label">Messages</span></div>
				<div class="box"><span class="val">%v</span><span class="label">Uptime</span></div>
				<div class="box"><span class="val">%s</span><span class="label">Disk Usage</span></div>
			</div>

			<h3 style="color:#38bdf8; font-size: 1rem; margin-bottom: 0.75rem;">LIVE TRAFFIC FEED (Ring Buffer)</h3>
			<div class="feed-container">%s</div>
			
			<div class="footer">Aegis Secure Mesh Protocol &bull; Node Identity Persistence Enabled &bull; %s</div>
		</div>
	</body>
	</html>`, node.RootHash, peerCount, msgCount, uptime, fmt.Sprintf("%.2f MB", float64(metrics.DiskUsageBytes)/1024/1024), trafficHTML, RelayVersion)
}

func apiPing(w http.ResponseWriter, r *http.Request) {
	json.NewEncoder(w).Encode(map[string]string{
		"root_hash": node.RootHash,
		"version":   RelayVersion,
		"status":    "alive_relay",
	})
}

func apiMetrics(w http.ResponseWriter, r *http.Request) {
	json.NewEncoder(w).Encode(metrics)
}

func apiPeers(w http.ResponseWriter, r *http.Request) {
	// [PEX] Peer Exchange Logic
	if r.Method == http.MethodGet {
		node.mu.RLock()
		defer node.mu.RUnlock()
		
		now := time.Now()
		var tier1, tier2, tier3 []string
		
		// Tiered stability discovery: Only share nodes that have proven uptime
		for url, joinedAt := range node.Peers {
			uptime := now.Sub(joinedAt)
			if uptime >= 10*time.Minute {
				tier3 = append(tier3, url)
			} else if uptime >= 5*time.Minute {
				tier2 = append(tier2, url)
			} else if uptime >= 2*time.Minute {
				tier1 = append(tier1, url)
			}
		}

		// Prioritize long-lived anchors in the response
		final := append(tier3, tier2...)
		final = append(final, tier1...)
		if len(final) > 100 {
			final = final[:100]
		}
		json.NewEncoder(w).Encode(final)
		return
	}

	// Peer Registration
	if r.Method == http.MethodPost {
		var req struct{ URL string `json:"url"` }
		if err := json.NewDecoder(r.Body).Decode(&req); err == nil && req.URL != "" {
			peerURL := strings.TrimRight(strings.TrimSpace(req.URL), "/")
			if strings.HasPrefix(peerURL, "http") {
				node.mu.Lock()
				if _, exists := node.Peers[peerURL]; !exists {
					node.Peers[peerURL] = time.Now()
					log.Printf("[Mesh] Handshake: Persistent peer registered: %s", peerURL)
				}
				node.mu.Unlock()
			}
		}
		w.WriteHeader(http.StatusOK)
		return
	}

	// [Manual] Peer Drop (The ONLY way a peer leaves the STICKY ledger)
	if r.Method == http.MethodDelete {
		var req struct{ URL string `json:"url"` }
		if err := json.NewDecoder(r.Body).Decode(&req); err == nil && req.URL != "" {
			peerURL := strings.TrimRight(strings.TrimSpace(req.URL), "/")
			node.mu.Lock()
			delete(node.Peers, peerURL)
			node.mu.Unlock()
			log.Printf("[Mesh] Manual Ejection: Peer removed from discovery: %s", peerURL)
		}
		w.WriteHeader(http.StatusOK)
		return
	}
}

func apiMessagesSync(w http.ResponseWriter, r *http.Request) {
	platformID := r.URL.Query().Get("platform")
	sinceStr := r.URL.Query().Get("since")
	
	var since int64
	fmt.Sscanf(sinceStr, "%d", &since)

	// Long-polling Implementation (AWS CPU Preservation)
	if since > 0 {
		deadline := time.Now().Add(10 * time.Second)
		for time.Now().Before(deadline) {
			node.mu.RLock()
			updated := node.LastUpdate > since
			node.mu.RUnlock()
			
			if updated {
				break
			}
			
			select {
			case <-r.Context().Done():
				return // Client disconnected
			default:
				time.Sleep(500 * time.Millisecond)
			}
		}
	}

	node.mu.RLock()
	lastUpdate := node.LastUpdate
	var filtered []Message
	for _, m := range node.Messages {
		if platformID != "" && m.Platform != platformID {
			continue
		}
		// Privacy Guard: Stripping invite codes from global relay sync
		if m.MsgType == "TRUSTED_INVITE" {
			stripped := m
			stripped.Payload = ""
			filtered = append(filtered, stripped)
		} else {
			filtered = append(filtered, m)
		}
	}
	node.mu.RUnlock()

	// Limit response size to prevent bandwidth spikes
	if len(filtered) > 1000 {
		filtered = filtered[len(filtered)-1000:]
	}

	w.Header().Set("X-Last-Update", fmt.Sprintf("%d", lastUpdate))
	json.NewEncoder(w).Encode(filtered)
}

func p2pReceiveMessage(w http.ResponseWriter, r *http.Request) {
	// Guard memory with MaxBytesReader
	var msg Message
	if err := json.NewDecoder(http.MaxBytesReader(w, r.Body, 1<<20)).Decode(&msg); err != nil {
		http.Error(w, "Malformed request", http.StatusBadRequest)
		return
	}

	if !verifyMessageSignature(msg) {
		http.Error(w, "Unauthorized cryptographic signature", http.StatusUnauthorized)
		return
	}

	node.mu.Lock()
	exists := false
	for i, m := range node.Messages {
		if m.ID == msg.ID {
			exists = true
			// Atomic tombstone application
			if msg.MsgType == "TOMBSTONE" && m.MsgType != "TOMBSTONE" {
				node.Messages[i].MsgType = "TOMBSTONE"
				node.Messages[i].Text = ""
				node.Messages[i].FileCID = ""
				node.LastUpdate = time.Now().UnixMilli()
			}
			break
		}
	}

	if !exists {
		node.Clock.Update(msg.Clock)
		msg.IsAcked = true
		node.Messages = append(node.Messages, msg)
		node.LastUpdate = time.Now().UnixMilli()

		// System Command: Content Deletion
		if msg.MsgType == "TOMBSTONE_CMD" {
			for i, m := range node.Messages {
				if m.ID == msg.Text && m.Sender == msg.Sender { 
					node.Messages[i].MsgType = "TOMBSTONE"
					node.Messages[i].Text = ""
					node.Messages[i].FileCID = ""
					node.LastUpdate = time.Now().UnixMilli()
					break
				}
			}
		}
	}
	node.mu.Unlock()

	if !exists {
		go broadcastMessageToPeers(msg)
		
		// Update Live Dashboard Traffic Buffer
		trafficMutex.Lock()
		safeID := "unknown"
		if len(msg.Sender) >= 8 { safeID = msg.Sender[:8] }
		
		logLine := fmt.Sprintf("[%s] %-12s | Src:%s | Plat:%s", 
			time.Now().Format("15:04:05"), 
			msg.MsgType, 
			safeID, 
			msg.Platform[:8])
			
		trafficLog = append([]string{logLine}, trafficLog...)
		if len(trafficLog) > MaxTrafficEntries {
			trafficLog = trafficLog[:MaxTrafficEntries]
		}
		trafficMutex.Unlock()
	}
}

// =============================================================================
// [File & Object Storage]
// =============================================================================

func getDiskSpaceBytes(dir string) int64 {
	var size int64
	filepath.Walk(dir, func(_ string, info os.FileInfo, err error) error {
		if err == nil && !info.IsDir() {
			size += info.Size()
		}
		return nil
	})
	return size
}

func p2pReceiveFile(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost { return }
	
	cid := r.URL.Query().Get("cid")
	if len(cid) != 64 {
		http.Error(w, "Invalid CID", http.StatusBadRequest)
		return
	}

	// Verify the ledger contains a valid FILE_TICKET for this upload
	node.mu.RLock()
	isVerified := false
	for _, m := range node.Messages {
		if m.FileCID == cid && m.MsgType == "FILE_TICKET" {
			isVerified = true
			break
		}
	}
	node.mu.RUnlock()

	if !isVerified {
		http.Error(w, "Unauthorized: CID not found in ledger", http.StatusForbidden)
		return
	}

	// Quota Check
	if getDiskSpaceBytes(fileStoreDir) > maxDiskBytes {
		http.Error(w, "Storage quota reached", http.StatusInsufficientStorage)
		return
	}

	path := filepath.Join(fileStoreDir, cid)
	if _, err := os.Stat(path); err == nil {
		w.WriteHeader(http.StatusOK) // File already exists
		return
	}

	// Stream to disk (Max 5.1GB)
	outFile, err := os.Create(path)
	if err != nil {
		http.Error(w, "IO Failure", http.StatusInternalServerError)
		return
	}
	defer outFile.Close()

	if _, err := io.Copy(outFile, http.MaxBytesReader(w, r.Body, 5<<30)); err != nil {
		os.Remove(path)
		return
	}

	log.Printf("[Files] Secure Storage Committed: %s", cid[:12])
	w.WriteHeader(http.StatusOK)
}

func p2pServeFile(w http.ResponseWriter, r *http.Request) {
	cid := r.URL.Query().Get("cid")
	path := filepath.Join(fileStoreDir, cid)
	
	if _, err := os.Stat(path); os.IsNotExist(err) {
		http.Error(w, "Object not found", http.StatusNotFound)
		return
	}
	
	w.Header().Set("Content-Type", "application/octet-stream")
	w.Header().Set("Cache-Control", "public, max-age=31536000") // Immutability
	http.ServeFile(w, r, path)
}

// =============================================================================
// [Background Maintenance Service]
// =============================================================================

func maintenanceLoop() {
	for {
		time.Sleep(10 * time.Minute)
		
		node.mu.RLock()
		peers := make([]string, 0, len(node.Peers))
		for p := range node.Peers { peers = append(peers, p) }
		node.mu.RUnlock()

		unreachableCount := 0
		for _, pURL := range peers {
			client := http.Client{Timeout: 3 * time.Second}
			resp, err := client.Get(pURL + "/api/ping")
			if err != nil || resp.StatusCode != http.StatusOK {
				unreachableCount++
			}
			if resp != nil {
				resp.Body.Close()
			}
		}

		node.mu.Lock()
		metrics.UnreachablePeers = unreachableCount
		node.mu.Unlock()
		
		if unreachableCount > 0 {
			log.Printf("[Mesh] Health Check: %d nodes currently offline. Preserving in persistent ledger.", unreachableCount)
		}
	}
}

func garbageCollectionLoop() {
	for {
		time.Sleep(GCInterval)
		
		cutoff := time.Now().Add(-maxRetention)
		
		// 1. Message Ledger Pruning
		node.mu.Lock()
		var fresh []Message
		for _, m := range node.Messages {
			if m.Timestamp.After(cutoff) {
				fresh = append(fresh, m)
			}
		}
		// Memory cap enforcement
		if len(fresh) > MaxMessageMemory {
			fresh = fresh[len(fresh)-MaxMessageMemory:]
		}
		node.Messages = fresh
		
		// 2. Replay Protection Cleanup
		sigCutoff := time.Now().UnixNano() - int64(30*time.Minute)
		for sig, ts := range node.SeenSignatures {
			if ts < sigCutoff {
				delete(node.SeenSignatures, sig)
			}
		}
		node.mu.Unlock()

		// 3. Binary Storage Eviction (Oldest First)
		if currentSize := getDiskSpaceBytes(fileStoreDir); currentSize > maxDiskBytes {
			files, _ := os.ReadDir(fileStoreDir)
			sort.Slice(files, func(i, j int) bool {
				iI, _ := files[i].Info()
				jI, _ := files[j].Info()
				return iI.ModTime().Before(jI.ModTime())
			})
			
			for _, f := range files {
				info, _ := f.Info()
				os.Remove(filepath.Join(fileStoreDir, f.Name()))
				currentSize -= info.Size()
				if currentSize < int64(float64(maxDiskBytes)*0.85) {
					break
				}
			}
			log.Println("[GC] Quota enforcement: Evicted oldest binary objects.")
		}
	}
}

func metricsLoop() {
	for {
		time.Sleep(15 * time.Second)
		
		var mem runtime.MemStats
		runtime.ReadMemStats(&mem)
		
		node.mu.RLock()
		metrics.ActivePeerCount = len(node.Peers)
		metrics.TotalMessages = uint64(len(node.Messages))
		metrics.MemoryAllocated = mem.Alloc
		metrics.Goroutines = runtime.NumGoroutine()
		metrics.UptimeSeconds = time.Since(node.StartTime).Seconds()
		metrics.DiskUsageBytes = getDiskSpaceBytes(fileStoreDir)
		node.mu.RUnlock()
	}
}