package main

import (
        "crypto/ed25519"
        "crypto/rand"
        "crypto/sha256"
        "encoding/hex"
        "encoding/json"
        "flag"
        "fmt"
        "io"
        "log"
        "net"
        "net/http"
        "os"
        "path/filepath"
        "sort"
        "strings"
        "sync"
        "time"
)

// ==========================================
// Aegis Protocol Structs
// ==========================================

type HLC struct {
        Physical int64 `json:"p"`
        Logical  int   `json:"l"`
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

type RelayNode struct {
        RootHash       string
        PublicKey      string
        PrivateKey     []byte
        Messages       []Message
        Peers          map[string]time.Time
        SeenSignatures map[string]int64
        Clock          HLC
        LastUpdate     int64
        mu             sync.RWMutex
}

var (
        node          *RelayNode
        serverPort    string
        fileStoreDir  = "aegis_relay_files"
        maxDiskGB     int64
        maxRetention  time.Duration

        // Security
        ipTracker = make(map[string][]time.Time)
        ipMutex   sync.Mutex
)

// ==========================================
// Boot & Initialization
// ==========================================

func main() {
        portFlag := flag.String("port", "8080", "Port to run the Aegis Cloud Relay on")
        diskFlag := flag.Int64("max-disk", 20, "Maximum disk usage for relayed files in GB")
        retentionFlag := flag.Int("retention", 7, "Number of days to keep messages/files before purging")
        flag.Parse()

        serverPort = *portFlag
        maxDiskGB = *diskFlag * 1024 * 1024 * 1024
        maxRetention = time.Duration(*retentionFlag) * 24 * time.Hour

        fmt.Println("==================================================")
        fmt.Println("🛡️  AEGIS CLOUD RELAY (HEADLESS MESH PROPAGATOR) 🛡️")
        fmt.Println("==================================================")
        fmt.Printf("[Config] Port: %s | Max File Disk: %d GB | Retention: %d Days\n", serverPort, *diskFlag, *retentionFlag)

        os.MkdirAll(fileStoreDir, 0700)
        initRelayIdentity()

        http.HandleFunc("/", withCORS(serveLanding))
        http.HandleFunc("/api/ping", withCORS(apiPing))
        http.HandleFunc("/api/peers", withCORS(apiPeers))
        http.HandleFunc("/api/messages", withCORS(apiMessagesSync))
        http.HandleFunc("/p2p/message", withCORS(withRateLimit(p2pReceiveMessage)))

        http.HandleFunc("/api/files/download", withCORS(p2pServeFile))
        http.HandleFunc("/p2p/files", withCORS(p2pServeFile))
        http.HandleFunc("/p2p/files/push", withCORS(withRateLimit(p2pReceiveFile)))

        go maintenanceLoop()
        go garbageCollectionLoop()

        log.Printf("[System] Relay is active and listening on 0.0.0.0:%s", serverPort)
        log.Fatal(http.ListenAndServe(":"+serverPort, nil))
}

func initRelayIdentity() {
        pub, priv, err := ed25519.GenerateKey(rand.Reader)
        if err != nil {
                log.Fatalf("Failed to generate relay keys: %v", err)
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
        }
        fmt.Printf("[Identity] Relay Root Hash Generated: %s\n", node.RootHash[:12])
}

// ==========================================
// Security & Middleware
// ==========================================

func withCORS(next http.HandlerFunc) http.HandlerFunc {
        return func(w http.ResponseWriter, r *http.Request) {
                w.Header().Set("Access-Control-Allow-Origin", "*")
                w.Header().Set("Access-Control-Allow-Methods", "POST, GET, OPTIONS")
                w.Header().Set("Access-Control-Allow-Headers", "Accept, Content-Type, Content-Length, Accept-Encoding, Authorization")

                if r.Method == "OPTIONS" {
                        w.WriteHeader(http.StatusOK)
                        return
                }
                next.ServeHTTP(w, r)
        }
}

func withRateLimit(next http.HandlerFunc) http.HandlerFunc {
        return func(w http.ResponseWriter, r *http.Request) {
                ip, _, err := net.SplitHostPort(r.RemoteAddr)
                if err != nil {
                        ip = r.RemoteAddr
                }

                ipMutex.Lock()
                now := time.Now()
                timestamps := ipTracker[ip]

                var valid []time.Time
                for _, t := range timestamps {
                        if now.Sub(t) < 5*time.Second {
                                valid = append(valid, t)
                        }
                }
                valid = append(valid, now)
                ipTracker[ip] = valid

                if len(valid) > 20 {
                        ipMutex.Unlock()
                        http.Error(w, "Rate limit exceeded", http.StatusTooManyRequests)
                        return
                }
                ipMutex.Unlock()

                next.ServeHTTP(w, r)
        }
}

// Add this helper function above verifyMessageSignature in main2.go
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


func verifyMessageSignature(msg Message) bool {
        cacheKey := fmt.Sprintf("%s_%d", msg.Signature, len(msg.AckedBy))

        node.mu.RLock()
        if _, seen := node.SeenSignatures[cacheKey]; seen {
                node.mu.RUnlock()
                return false
        }
        node.mu.RUnlock()

        pubBytes, err := hex.DecodeString(msg.PublicKey)
        if err != nil || len(pubBytes) != ed25519.PublicKeySize { return false }

        hash := sha256.Sum256(pubBytes)
        if hex.EncodeToString(hash[:]) != msg.Sender { return false }

        sigBytes, err := hex.DecodeString(msg.Signature)
        if err != nil || len(sigBytes) != ed25519.SignatureSize { return false }

        payloadToVerify := fmt.Sprintf("%s:%s:%s:%s:%s:%s:%d", msg.ID, msg.Platform, msg.MsgType, msg.TargetHash, msg.Text, msg.FileCID, msg.Timestamp.UnixNano())
        if !ed25519.Verify(pubBytes, []byte(payloadToVerify), sigBytes) {
                return false
        }

        drift := time.Since(msg.Timestamp)
        if drift > maxRetention || drift < -15*time.Minute {
                return false
        }

        node.mu.Lock()
        node.SeenSignatures[cacheKey] = time.Now().UnixNano()
        node.mu.Unlock()

        return true
}

// ==========================================
// Endpoints
// ==========================================

func serveLanding(w http.ResponseWriter, r *http.Request) {
        if r.URL.Path != "/" {
                http.NotFound(w, r)
                return
        }
        w.Header().Set("Content-Type", "text/html")
        html := fmt.Sprintf(`<html><body style="background:#0f172a;color:#10b981;font-family:monospace;padding:3rem;">
                <h2>🛡️ Aegis Cloud Relay Active (Secure v3.1)</h2>
                <p>Relay Hash: %s</p>
                <p>Status: Routing packets and punching NATs securely.</p>
        </body></html>`, node.RootHash)
        w.Write([]byte(html))
}

func apiPing(w http.ResponseWriter, r *http.Request) {
        w.Header().Set("Content-Type", "application/json")
        json.NewEncoder(w).Encode(map[string]string{
                "root_hash": node.RootHash,
                "status":    "alive_relay",
        })
}

func apiPeers(w http.ResponseWriter, r *http.Request) {
        w.Header().Set("Content-Type", "application/json")

        if r.Method == "GET" {
                node.mu.RLock()
                var peerList []string
                for url := range node.Peers {
                        peerList = append(peerList, url)
                }
                node.mu.RUnlock()
                json.NewEncoder(w).Encode(peerList)
                return
        }

        if r.Method == "POST" {
                var req struct { URL string `json:"url"` }
                if err := json.NewDecoder(r.Body).Decode(&req); err == nil && req.URL != "" {
                        peerURL := strings.TrimRight(strings.TrimSpace(req.URL), "/")
                        if strings.HasPrefix(peerURL, "http://") || strings.HasPrefix(peerURL, "https://") {
                                node.mu.Lock()
                                node.Peers[peerURL] = time.Now()
                                node.mu.Unlock()
                                log.Printf("[Mesh] Registered new peer address: %s", peerURL)
                        }
                }
                w.WriteHeader(http.StatusOK)
                return
        }
}

func apiMessagesSync(w http.ResponseWriter, r *http.Request) {
        if r.Method != "GET" { return }
        w.Header().Set("Content-Type", "application/json")

        limitStr := r.URL.Query().Get("limit")
        sinceStr := r.URL.Query().Get("since")
        var since int64
        if sinceStr != "" { fmt.Sscanf(sinceStr, "%d", &since) }

        if since > 0 {
                node.mu.RLock()
                currentUpdate := node.LastUpdate
                node.mu.RUnlock()

                if currentUpdate <= since {
                        for i := 0; i < 20; i++ {
                                time.Sleep(500 * time.Millisecond)
                                node.mu.RLock()
                                currentUpdate = node.LastUpdate
                                node.mu.RUnlock()
                                if currentUpdate > since {
                                        break
                                }
                        }
                        if currentUpdate <= since {
                                w.WriteHeader(http.StatusNotModified)
                                return
                        }
                }
        }

        node.mu.RLock()
        lastUpdate := node.LastUpdate

        filtered := make([]Message, len(node.Messages))
        copy(filtered, node.Messages)
        node.mu.RUnlock()

        limit := 2000
        if limitStr != "" { fmt.Sscanf(limitStr, "%d", &limit) }

        if len(filtered) > limit {
                filtered = filtered[len(filtered)-limit:]
        }

        w.Header().Set("X-Last-Update", fmt.Sprintf("%d", lastUpdate))
        json.NewEncoder(w).Encode(filtered)
}

func p2pReceiveMessage(w http.ResponseWriter, r *http.Request) {
        if r.Method != "POST" { return }

        r.Body = http.MaxBytesReader(w, r.Body, 1<<20)

        var msg Message
        if err := json.NewDecoder(r.Body).Decode(&msg); err != nil {
                http.Error(w, "Invalid payload format", http.StatusBadRequest)
                return
        }

        if !verifyMessageSignature(msg) {
                http.Error(w, "Invalid signature or replay detected", http.StatusUnauthorized)
                return
        }

        node.mu.Lock()
        exists := false
        for i, m := range node.Messages {
                if m.ID == msg.ID {
                        exists = true
                        if msg.MsgType == "TOMBSTONE" && m.MsgType != "TOMBSTONE" {
                                node.Messages[i].MsgType = "TOMBSTONE"
                                node.Messages[i].Text = ""
                                node.Messages[i].FileCID = ""
                                node.LastUpdate = time.Now().UnixMilli()
                        }
                        if len(msg.AckedBy) > 0 {
                                merged := make(map[string]bool)
                                for _, a := range m.AckedBy { merged[a] = true }
                                for _, a := range msg.AckedBy {
                                        if !merged[a] {
                                                merged[a] = true
                                                node.Messages[i].AckedBy = append(node.Messages[i].AckedBy, a)
                                                node.LastUpdate = time.Now().UnixMilli()
                                        }
                                }
                        }
                        break
                }
        }

        if !exists {
                node.Clock.Update(msg.Clock)
                msg.IsAcked = true
                node.Messages = append(node.Messages, msg)
                node.LastUpdate = time.Now().UnixMilli()
        }
        node.mu.Unlock()

        w.WriteHeader(http.StatusOK)
}

// ==========================================
// File Management
// ==========================================

func getDirSize(path string) int64 {
        var size int64
        filepath.Walk(path, func(_ string, info os.FileInfo, err error) error {
                if err == nil && !info.IsDir() { size += info.Size() }
                return nil
        })
        return size
}

func p2pReceiveFile(w http.ResponseWriter, r *http.Request) {
        if r.Method != "POST" { return }

        cid := r.URL.Query().Get("cid")
        if cid == "" || len(cid) != 64 {
                http.Error(w, "Invalid cid", http.StatusBadRequest)
                return
        }

        // Security Fix: Hex decode validation prevents path traversal injections
        if _, err := hex.DecodeString(cid); err != nil {
                http.Error(w, "Malformed cid", http.StatusBadRequest)
                return
        }

        // Security Fix: Verify the blind relay actually has the file ticket
        node.mu.RLock()
        isValidTicket := false
        for _, m := range node.Messages {
                if m.FileCID == cid && m.MsgType == "FILE_TICKET" {
                        isValidTicket = true
                        break
                }
        }
        node.mu.RUnlock()

        if !isValidTicket {
                http.Error(w, "Rejected: CID not found in relay ledger", http.StatusForbidden)
                return
        }

        if getDirSize(fileStoreDir) > maxDiskGB {
                http.Error(w, "Relay storage quota exceeded", http.StatusForbidden)
                return
        }

        path := filepath.Join(fileStoreDir, cid)
        if _, err := os.Stat(path); err == nil {
                w.WriteHeader(http.StatusOK)
                return
        }

        r.Body = http.MaxBytesReader(w, r.Body, 5<<30+100<<20)

        tempPath := filepath.Join(fileStoreDir, "temp_"+cid)
        outFile, err := os.Create(tempPath)
        if err != nil {
                http.Error(w, "Storage failure", http.StatusInternalServerError)
                return
        }

        _, err = io.Copy(outFile, r.Body)
        outFile.Close()

        if err != nil {
                os.Remove(tempPath)
                return
        }

        os.Rename(tempPath, path)
        log.Printf("[Files] Relaying new file: %s\n", cid[:12])
        w.WriteHeader(http.StatusOK)
}

func p2pServeFile(w http.ResponseWriter, r *http.Request) {
        cid := r.URL.Query().Get("cid")
        if cid == "" || len(cid) != 64 {
                http.Error(w, "Invalid cid", http.StatusBadRequest)
                return
        }

        path := filepath.Join(fileStoreDir, cid)
        if _, err := os.Stat(path); os.IsNotExist(err) {
                http.Error(w, "File not found on relay", http.StatusNotFound)
                return
        }

        w.Header().Set("Content-Type", "application/octet-stream")
        http.ServeFile(w, r, path)
}

// ==========================================
// Background Workers
// ==========================================

func maintenanceLoop() {
        for {
                time.Sleep(10 * time.Minute)

                node.mu.RLock()
                peerList := make([]string, 0, len(node.Peers))
                for p := range node.Peers { peerList = append(peerList, p) }
                node.mu.RUnlock()

                deadPeers := make([]string, 0)
                for _, pURL := range peerList {
                        client := http.Client{Timeout: 4 * time.Second}
                        resp, err := client.Get(pURL + "/api/ping")
                        if err != nil || resp.StatusCode != http.StatusOK {
                                deadPeers = append(deadPeers, pURL)
                        }
                        if resp != nil { resp.Body.Close() }
                }

                node.mu.Lock()
                for _, dead := range deadPeers {
                        delete(node.Peers, dead)
                }
                node.mu.Unlock()

                if len(deadPeers) > 0 {
                        log.Printf("[Mesh] Dropped %d dead peers. Active connections: %d\n", len(deadPeers), len(node.Peers))
                }
        }
}

func garbageCollectionLoop() {
        for {
                time.Sleep(1 * time.Hour)
                log.Println("[System] Running Garbage Collection...")

                cutoffTime := time.Now().Add(-maxRetention)

                node.mu.Lock()
                var freshMsgs []Message
                for _, m := range node.Messages {
                        if m.Timestamp.After(cutoffTime) {
                                freshMsgs = append(freshMsgs, m)
                        }
                }
                purgedCount := len(node.Messages) - len(freshMsgs)
                node.Messages = freshMsgs
                node.mu.Unlock()

                if purgedCount > 0 {
                        log.Printf("[GC] Purged %d old messages from memory.\n", purgedCount)
                }

                node.mu.Lock()
                sigCutoff := time.Now().UnixNano() - int64(15*time.Minute)
                for sig, timestamp := range node.SeenSignatures {
                        if timestamp < sigCutoff {
                                delete(node.SeenSignatures, sig)
                        }
                }
                node.mu.Unlock()

                currentSize := getDirSize(fileStoreDir)
                if currentSize > maxDiskGB {
                        log.Printf("[GC] Disk space %d GB exceeds %d GB max. Beginning eviction...\n", currentSize/(1024*1024*1024), maxDiskGB/(1024*1024*1024))

                        files, err := os.ReadDir(fileStoreDir)
                        if err == nil {
                                sort.Slice(files, func(i, j int) bool {
                                        iInfo, _ := files[i].Info()
                                        jInfo, _ := files[j].Info()
                                        return iInfo.ModTime().Before(jInfo.ModTime())
                                })

                                for _, f := range files {
                                        fInfo, _ := f.Info()
                                        if !fInfo.IsDir() {
                                                os.Remove(filepath.Join(fileStoreDir, f.Name()))
                                                currentSize -= fInfo.Size()
                                                if currentSize < int64(float64(maxDiskGB)*0.8) {
                                                        break
                                                }
                                        }
                                }
                                log.Println("[GC] Eviction complete.")
                        }
                }
        }
}