// jl_tool - Jungle Leopard Display control utility
//
// Reverse-engineered from the Jungle Leopard Display Electron app source.
// Tested target: 1920×462 display, firmware v2.2, model D215-FL7707N-9.16inch-hor
//
// Serial protocol frame format (both directions):
//
//	[0x55 0xAA LEN_L LEN_H KEY DATA... CHK_L CHK_H]
//
//	LEN  = 7 + len(DATA)   (total frame length, little-endian)
//	CHK  = sum(all bytes before checksum) & 0xFFFF  (little-endian)
//
// Confirmed command keys (from device.js):
//
//	 1  restart         – reboot the device (no payload)
//	 3  brightness      – set backlight 0-100 (1-byte payload)
//	               also used as JPEG frame-size announcement in stream mode
//	 6  getInfo         – query device (no payload) → JSON response
//	12  otaInit         – prepare file upload: [0xF2,0xFF, size 4×LE, 0,0,0,0]
//	17  liveTrigger     – enter live-display mode (no payload)
//	21  motionTimeout   – set motion sensor timeout (v2.8+, 2-byte payload)
//	32  setRegion       – write region/config string (UTF-8 payload)
//	33  closeDevice     – soft-close signal (v3.1+, no payload)
//	35  setSerialNum    – set serial number
//	37  setMotor        – motor control (region "sulcs" only)
//
// Usage:
//
//	jl_tool [flags] <command> [args]
package main

import (
	"bufio"
	"bytes"
	"context"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"image"
	"image/color"
	"image/jpeg"
	"image/png"
	"log"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"time"

	"github.com/chromedp/chromedp"
	"go.bug.st/serial"
	xdraw "golang.org/x/image/draw"
)

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

const (
	defaultDevice = "/dev/ttyACM0"
	defaultBaud   = 2_000_000

	frameHdr0 = 0x55
	frameHdr1 = 0xAA

	// Known command keys
	keyRestart    = 1
	keyBrightness = 3
	keyGetInfo    = 6
	keyListDir    = 7 // CONFIRMED: list directory; payload = UTF-8 path (empty = root)
	keyReadFile   = 8 // UNKNOWN: no response to file path queries
	keyWriteFile  = 9 // UNKNOWN: no response to file path queries
	// key 5:  returns 0x05 regardless of path – meaning unknown (maybe firmware sub-version)
	// key 10: returns 0x01 for dirs, 0x07 for file paths – meaning unclear; 0x07 may be
	//         "file type" rather than "write failed"
	// key 12: [0xF1,0xFF,size,0…] returns 0x00 and accepts data – LIKELY video upload
	//         (the OTA write path: [0xF2,0xFF,size,0…] writes firmware; 0xF1 may write video)
	// key 16: returns 0x01 for dirs, 0x02 for file paths – possibly a type/stat indicator
	keyWriteFile2 = 10 // still under investigation
	keyOTAInit      = 12
	keyLiveTrigger  = 17
	keyMotionTimer  = 21
	keySetRegion    = 32
	keyCloseDevice  = 33
	keySetSerialNum = 35
	keySetMotor     = 37

	// Streaming
	dispW          = 1920
	dispH          = 462
	quality        = 80
	maxFPS         = 30
	// JS source: maxSize = 90 KB for 9.16-inch model at firmware ≤ v2.8.
	// Quality is auto-reduced by 5 per retry until the frame fits.
	defaultMaxFrameKB = 90

	// Default desktop capture region – edit to match your monitor layout.
	// Use xrandr / wlr-randr to find offsets.
	captureX = 0
	captureY = 0
	captureW = 1920
	captureH = 1080
)

// ---------------------------------------------------------------------------
// Global CLI flags
// ---------------------------------------------------------------------------

var (
	fDevice  = flag.String("device", defaultDevice, "Serial device path")
	fBaud    = flag.Int("baud", defaultBaud, "Baud rate (try 115200 if 2000000 fails)")
	fTimeout = flag.Duration("timeout", 3*time.Second, "Read timeout for command responses")
	fVerbose = flag.Bool("v", false, "Print TX/RX hex frames")
	fUnsafe  = flag.Bool("unsafe", false, "Include dangerous keys (restart, OTA, etc.) in probe-scan")
	fKey     = flag.Int("key", 0, "Override command key for writefile (0 = use default key 9)")

	// Stream / show-image flags
	fCapX      = flag.Int("cap-x", captureX, "Capture region left edge (stream)")
	fCapY      = flag.Int("cap-y", captureY, "Capture region top edge (stream)")
	fCapW      = flag.Int("cap-w", captureW, "Capture region width (stream)")
	fCapH      = flag.Int("cap-h", captureH, "Capture region height (stream)")
	fFPS       = flag.Int("fps", maxFPS, "Target FPS (stream)")
	fQuality   = flag.Int("quality", quality, "JPEG quality 1-100")
	fRotate    = flag.Bool("rotate", true, "Compensate for physical 90° panel rotation (required for correct display; disable with -rotate=false)")
	fStretch   = flag.Bool("stretch", false, "Stretch image to fill display (default: letterbox)")
	fHeadless    = flag.Bool("headless", true, "Run browser headlessly (use -headless=false to show the window)")
	fMaxFrameKB  = flag.Int("max-frame-kb", defaultMaxFrameKB, "Auto-reduce JPEG quality until frame fits this size (0 = disabled)")
)

// ---------------------------------------------------------------------------
// Protocol helpers
// ---------------------------------------------------------------------------

// buildFrame assembles a complete protocol frame.
func buildFrame(key byte, data []byte) []byte {
	total := 7 + len(data)
	f := make([]byte, 0, total)
	f = append(f, frameHdr0, frameHdr1)
	f = append(f, byte(total), byte(total>>8))
	f = append(f, key)
	f = append(f, data...)
	var sum uint32
	for _, b := range f {
		sum += uint32(b)
	}
	sum &= 0xFFFF
	f = append(f, byte(sum), byte(sum>>8))
	return f
}

// extractFrame finds a complete frame in buf.
// Returns (frame, rest) where rest is the unconsumed buffer.
func extractFrame(buf []byte) (frame, rest []byte) {
	for len(buf) >= 2 {
		i := bytes.Index(buf, []byte{frameHdr0, frameHdr1})
		if i < 0 {
			return nil, buf[max(len(buf)-1, 0):]
		}
		buf = buf[i:]
		if len(buf) < 4 {
			return nil, buf
		}
		frameLen := int(buf[2]) | int(buf[3])<<8
		if frameLen < 7 || frameLen > 65536 {
			buf = buf[2:] // skip bad header, keep searching
			continue
		}
		if len(buf) >= frameLen {
			return buf[:frameLen], buf[frameLen:]
		}
		return nil, buf // need more data
	}
	return nil, buf
}

// readFrame accumulates bytes until a complete frame is found or timeout.
func readFrame(port serial.Port, timeout time.Duration) []byte {
	if err := port.SetReadTimeout(50 * time.Millisecond); err != nil {
		log.Printf("SetReadTimeout: %v", err)
	}
	var acc []byte
	tmp := make([]byte, 512)
	deadline := time.Now().Add(timeout)
	for time.Now().Before(deadline) {
		n, _ := port.Read(tmp)
		if n > 0 {
			acc = append(acc, tmp[:n]...)
		}
		if frame, _ := extractFrame(acc); frame != nil {
			if *fVerbose {
				fmt.Fprintf(os.Stderr, "  RX: %s\n", hex.EncodeToString(frame))
			}
			return frame
		}
	}
	if *fVerbose && len(acc) > 0 {
		fmt.Fprintf(os.Stderr, "  RX (partial): %s\n", hex.EncodeToString(acc))
	}
	return acc
}

// framePayload extracts the JSON/data payload from a response frame.
// Layout: [hdr(2) len(2) key(1) PAYLOAD... chk(2)]
func framePayload(frame []byte) []byte {
	if len(frame) < 7 {
		return nil
	}
	return frame[5 : len(frame)-2]
}

func sendCmd(port serial.Port, key byte, data []byte) []byte {
	frame := buildFrame(key, data)
	if *fVerbose {
		fmt.Fprintf(os.Stderr, "  TX: %s\n", hex.EncodeToString(frame))
	}
	if _, err := port.Write(frame); err != nil {
		log.Fatalf("write key %d: %v", key, err)
	}
	return readFrame(port, *fTimeout)
}

func sendCmdNoReply(port serial.Port, key byte, data []byte) {
	frame := buildFrame(key, data)
	if *fVerbose {
		fmt.Fprintf(os.Stderr, "  TX (no-reply): %s\n", hex.EncodeToString(frame))
	}
	if _, err := port.Write(frame); err != nil {
		log.Fatalf("write key %d: %v", key, err)
	}
}

// ---------------------------------------------------------------------------
// Port helpers
// ---------------------------------------------------------------------------

// ensurePortAccess checks whether the serial device is readable/writable.
// If not, it runs "sudo chmod 666 <device>" — prompting for the user's
// password in the terminal — so the tool can be run without sudo.
func ensurePortAccess(device string) {
	f, err := os.OpenFile(device, os.O_RDWR, 0)
	if err == nil {
		f.Close()
		return // already accessible
	}
	fmt.Printf("%s is not accessible (%v).\nRequesting permission via sudo...\n", device, err)
	cmd := exec.Command("sudo", "chmod", "666", device)
	cmd.Stdin = os.Stdin
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	if err := cmd.Run(); err != nil {
		log.Fatalf("sudo chmod 666 %s failed: %v", device, err)
	}
}

func openPort() serial.Port {
	ensurePortAccess(*fDevice)
	mode := &serial.Mode{
		BaudRate: *fBaud,
		DataBits: 8,
		Parity:   serial.NoParity,
		StopBits: serial.OneStopBit,
	}
	p, err := serial.Open(*fDevice, mode)
	if err != nil {
		log.Fatalf("cannot open %s at %d baud: %v\n"+
			"Tips:\n"+
			"  sudo usermod -aG dialout $USER  (then re-login)\n"+
			"  Try -baud 115200 if 2000000 fails",
			*fDevice, *fBaud, err)
	}
	return p
}

// ---------------------------------------------------------------------------
// Commands
// ---------------------------------------------------------------------------

func cmdInfo() {
	port := openPort()
	defer port.Close()

	fmt.Printf("Querying device on %s at %d baud...\n", *fDevice, *fBaud)
	resp := sendCmd(port, keyGetInfo, nil)
	if len(resp) == 0 {
		log.Fatal("no response – check device and baud rate")
	}

	payload := framePayload(resp)
	if len(payload) == 0 {
		fmt.Printf("Raw response: %s\n", hex.EncodeToString(resp))
		return
	}

	// Pretty-print JSON
	var v interface{}
	if err := json.Unmarshal(payload, &v); err != nil {
		fmt.Printf("Response (raw text): %s\n", string(payload))
		fmt.Printf("Response (hex):      %s\n", hex.EncodeToString(resp))
		return
	}
	out, _ := json.MarshalIndent(v, "", "  ")
	fmt.Println(string(out))

	// Print helpful filesystem summary
	if m, ok := v.(map[string]interface{}); ok {
		if data, ok := m["data"].(map[string]interface{}); ok {
			printFSSummary(data)
		}
	}
}

func printFSSummary(data map[string]interface{}) {
	iBlocks, _ := data["i_blocks"].(float64)
	iBlockSize, _ := data["i_block_size"].(float64)
	iBlockFree, _ := data["i_block_free"].(float64)
	if iBlocks > 0 && iBlockSize > 0 {
		totalMB := iBlocks * iBlockSize / 1024 / 1024
		freeMB := iBlockFree * iBlockSize / 1024 / 1024
		usedMB := totalMB - freeMB
		iPath, _ := data["i_path"].(string)
		fmt.Printf("\nInternal FS (%s): %.1f MB total, %.1f MB used, %.1f MB free\n",
			iPath, totalMB, usedMB, freeMB)
	}

	ver, _ := data["version"].(string)
	if ver != "" {
		v, _ := strconv.ParseFloat(ver, 64)
		fmt.Printf("Firmware v%s notes:\n", ver)
		if v < 2.8 {
			fmt.Println("  - motion-timeout (key 21) requires v2.8+")
			fmt.Println("  - stop-live EOI signal requires v2.8+")
		}
		if v < 3.1 {
			fmt.Println("  - close-device (key 33) requires v3.1+")
		}
	}
}

func cmdBrightness(level int) {
	port := openPort()
	defer port.Close()
	fmt.Printf("Setting brightness to %d%%...\n", level)
	sendCmdNoReply(port, keyBrightness, []byte{byte(level)})
	time.Sleep(100 * time.Millisecond)
	fmt.Println("Done.")
}

func cmdRestart() {
	port := openPort()
	defer port.Close()
	fmt.Println("Restarting device...")
	sendCmdNoReply(port, keyRestart, nil)
	time.Sleep(100 * time.Millisecond)
	fmt.Println("Restart command sent.")
}

func cmdRegion(regionStr string) {
	port := openPort()
	defer port.Close()
	fmt.Printf("Setting region to %q...\n", regionStr)
	resp := sendCmd(port, keySetRegion, []byte(regionStr))
	if payload := framePayload(resp); len(payload) > 0 {
		fmt.Printf("Response: %s\n", string(payload))
	} else if len(resp) > 0 {
		fmt.Printf("Response (hex): %s\n", hex.EncodeToString(resp))
	} else {
		fmt.Println("No response.")
	}
}

func cmdClose() {
	port := openPort()
	defer port.Close()
	fmt.Println("Sending close command (requires firmware v3.1+)...")
	sendCmdNoReply(port, keyCloseDevice, nil)
	time.Sleep(100 * time.Millisecond)
	fmt.Println("Done.")
}

// cmdStopLive sends two JPEG EOI markers to terminate live streaming mode.
// According to device.js this is only needed on firmware v2.8+; on v2.2 the
// device stops when no more frames arrive.
func cmdStopLive() {
	port := openPort()
	defer port.Close()
	fmt.Println("Sending JPEG EOI stop signal...")
	eoi := []byte{0xFF, 0xD9, 0xFF, 0xD9}
	if _, err := port.Write(eoi); err != nil {
		log.Fatalf("write: %v", err)
	}
	fmt.Println("Done.")
}

// cmdProbeKey sends a single command key with optional raw payload and prints
// the response.  Useful for discovering undocumented commands.
func cmdProbeKey(key int, data []byte) {
	port := openPort()
	defer port.Close()

	frame := buildFrame(byte(key), data)
	fmt.Printf("Sending key %d (0x%02X), payload [%s]\n",
		key, key, hex.EncodeToString(data))
	fmt.Printf("TX: %s\n", hex.EncodeToString(frame))

	if _, err := port.Write(frame); err != nil {
		log.Fatalf("write: %v", err)
	}

	resp := readFrame(port, *fTimeout)
	if len(resp) == 0 {
		fmt.Println("RX: (no response)")
		return
	}
	fmt.Printf("RX: %s\n", hex.EncodeToString(resp))

	payload := framePayload(resp)
	if len(payload) > 0 {
		fmt.Printf("Payload (text): %q\n", string(payload))
		var v interface{}
		if err := json.Unmarshal(payload, &v); err == nil {
			out, _ := json.MarshalIndent(v, "  ", "  ")
			fmt.Printf("Payload (JSON):\n  %s\n", out)
		}
	}
}

// dangerousKeys are keys that should be skipped during probe-scan by default
// because they cause disruptive side-effects (restart, OTA init, etc.).
var dangerousKeys = map[int]string{
	1:  "restart – reboots device, breaks port",
	12: "OTA init – starts firmware flash sequence",
	33: "close device – disconnects (v3.1+)",
	35: "set serial number – persistent write",
	37: "set motor – hardware actuation",
}

// cmdProbeScan sends each key in [start, end] with no payload and reports
// which keys produce a response.  Helps identify undocumented commands such
// as file listing, file read/write, log export, etc.
//
// Known-dangerous keys (restart, OTA, etc.) are skipped unless -unsafe is set.
// The port is reopened automatically if the device disconnects mid-scan.
func cmdProbeScan(start, end int, unsafe bool) {
	scanTimeout := 500 * time.Millisecond

	fmt.Printf("Scanning keys %d–%d on %s at %d baud...\n", start, end, *fDevice, *fBaud)
	if !unsafe {
		fmt.Printf("Skipping dangerous keys (use -unsafe to include them): ")
		for k, desc := range dangerousKeys {
			if k >= start && k <= end {
				fmt.Printf("%d ", k)
			}
			_ = desc
		}
		fmt.Println()
	}
	fmt.Println()

	port := openPort()
	defer func() {
		if port != nil {
			port.Close()
		}
	}()

	responded := 0
	for key := start; key <= end; key++ {
		if !unsafe {
			if reason, skip := dangerousKeys[key]; skip {
				fmt.Printf("Key %3d (0x%02X): SKIPPED (%s)\n", key, key, reason)
				continue
			}
		}

		// Attempt write; on I/O error assume device disconnected and reconnect.
		frame := buildFrame(byte(key), nil)
		if *fVerbose {
			fmt.Fprintf(os.Stderr, "  TX[%d]: %s\n", key, hex.EncodeToString(frame))
		}
		if _, err := port.Write(frame); err != nil {
			fmt.Printf("Key %3d (0x%02X): write error (%v) – attempting reconnect...\n", key, key, err)
			port.Close()
			port = nil
			port = waitForPort(10 * time.Second)
			if port == nil {
				fmt.Println("Reconnect timed out – aborting scan.")
				break
			}
			fmt.Println("Reconnected. Continuing scan...")
			// Retry this key after reconnect
			if _, err := port.Write(frame); err != nil {
				fmt.Printf("Key %3d (0x%02X): still failing after reconnect: %v\n", key, key, err)
				continue
			}
		}

		resp := readFrame(port, scanTimeout)
		if len(resp) == 0 {
			fmt.Printf("Key %3d (0x%02X): no response\n", key, key)
			continue
		}
		responded++

		printKeyResponse(key, resp)
		time.Sleep(50 * time.Millisecond)
	}

	fmt.Printf("\n%d keys responded (of %d probed).\n", responded, end-start+1)
}

// waitForPort polls until the serial device appears and opens successfully.
func waitForPort(timeout time.Duration) serial.Port {
	deadline := time.Now().Add(timeout)
	for time.Now().Before(deadline) {
		time.Sleep(500 * time.Millisecond)
		if _, err := os.Stat(*fDevice); err != nil {
			continue
		}
		mode := &serial.Mode{
			BaudRate: *fBaud,
			DataBits: 8,
			Parity:   serial.NoParity,
			StopBits: serial.OneStopBit,
		}
		p, err := serial.Open(*fDevice, mode)
		if err == nil {
			return p
		}
	}
	return nil
}

func printKeyResponse(key int, resp []byte) {
	payload := framePayload(resp)
	if len(payload) == 0 {
		// Not a framed response – print raw bytes
		fmt.Printf("Key %3d (0x%02X): raw %d byte(s): %s\n",
			key, key, len(resp), hex.EncodeToString(resp))
		return
	}
	var v interface{}
	if err := json.Unmarshal(payload, &v); err == nil {
		out, _ := json.Marshal(v)
		fmt.Printf("Key %3d (0x%02X): JSON → %s\n", key, key, out)
	} else {
		fmt.Printf("Key %3d (0x%02X): payload %d bytes → %s  (text: %q)\n",
			key, key, len(payload), hex.EncodeToString(payload), string(payload))
	}
}

// cmdRawWrite writes arbitrary bytes to the port and prints any response.
// Useful for replaying captured USB traffic.
func cmdRawWrite(data []byte) {
	port := openPort()
	defer port.Close()
	fmt.Printf("Writing %d raw bytes: %s\n", len(data), hex.EncodeToString(data))
	if _, err := port.Write(data); err != nil {
		log.Fatalf("write: %v", err)
	}
	resp := readFrame(port, *fTimeout)
	if len(resp) > 0 {
		fmt.Printf("Response: %s\n", hex.EncodeToString(resp))
	} else {
		fmt.Println("No response.")
	}
}

// cmdUpload attempts to push a file to the device using the OTA firmware-
// update protocol (key 12).  The device stores firmware at /data/ and video
// at /data/video/ according to the app constants.
//
// WARNING: This mechanism is confirmed only for firmware (.bin) updates.
// Sending arbitrary files may have no effect or could disrupt device state.
// Run "info" first to confirm available storage.
func cmdUpload(localFile string) {
	data, err := os.ReadFile(localFile)
	if err != nil {
		log.Fatalf("read %s: %v", localFile, err)
	}

	fmt.Printf("File: %s (%d bytes)\n", localFile, len(data))
	fmt.Println("WARNING: Experimental – confirmed only for OTA firmware bins.")
	fmt.Println("Press Ctrl-C within 3 s to abort...")
	time.Sleep(3 * time.Second)

	port := openPort()
	defer port.Close()

	// Step 1: announce file size via key 12
	// The first two bytes [0xF2, 0xFF] are the OTA sub-command prefix seen in
	// the app source.  The size follows as 4-byte little-endian.
	sz := uint32(len(data))
	otaInit := []byte{
		0xF2, 0xFF,
		byte(sz), byte(sz >> 8), byte(sz >> 16), byte(sz >> 24),
		0, 0, 0, 0,
	}
	fmt.Printf("Sending OTA init (key 12) for %d bytes...\n", sz)
	resp := sendCmd(port, keyOTAInit, otaInit)
	if len(resp) > 0 {
		fmt.Printf("Init response: %s\n", hex.EncodeToString(resp))
	} else {
		fmt.Println("Init response: (none)")
	}

	// Step 2: send file data in 20 kB chunks (matches app source)
	chunkSize := 20480
	sent := 0
	start := time.Now()
	for sent < len(data) {
		end := sent + chunkSize
		if end > len(data) {
			end = len(data)
		}
		if _, err := port.Write(data[sent:end]); err != nil {
			log.Fatalf("write at offset %d: %v", sent, err)
		}
		sent = end
		pct := float64(sent) / float64(len(data)) * 100
		elapsed := time.Since(start).Seconds()
		kbps := float64(sent) / 1024 / elapsed
		fmt.Printf("\r  %d/%d bytes  %.1f%%  %.0f kB/s   ", sent, len(data), pct, kbps)
	}
	fmt.Println()

	// Step 3: wait for completion ACK
	fmt.Println("Waiting for completion ACK (up to 30 s)...")
	resp = readFrame(port, 30*time.Second)
	if len(resp) > 0 {
		fmt.Printf("Final response: %s\n", hex.EncodeToString(resp))
	} else {
		fmt.Println("No response – device may need a manual restart.")
	}
}

// ---------------------------------------------------------------------------
// Filesystem commands
// ---------------------------------------------------------------------------

// DirEntry is one entry from a key-7 directory listing response.
type DirEntry struct {
	Filename string `json:"filename"`
	Type     int    `json:"type"` // 0 = directory?, 1 = file? (TBD)
	Size     int    `json:"size"` // may or may not be present
}

// DirResponse is the parsed JSON from key 7.
type DirResponse struct {
	Cmd  string `json:"cmd"`
	Data struct {
		DirList []DirEntry `json:"dir_list"`
	} `json:"data"`
}

// cmdListDir lists a directory on the device using key 7.
// Pass an empty path to list the root.
func cmdListDir(path string) {
	port := openPort()
	defer port.Close()

	fmt.Printf("Listing %q...\n", path)
	resp := sendCmd(port, keyListDir, []byte(path))
	if len(resp) == 0 {
		fmt.Println("No response.")
		return
	}

	payload := framePayload(resp)
	if len(payload) == 0 {
		fmt.Printf("Raw response: %s\n", hex.EncodeToString(resp))
		return
	}

	var dir DirResponse
	if err := json.Unmarshal(payload, &dir); err != nil {
		fmt.Printf("Raw payload: %q\n", string(payload))
		return
	}

	fmt.Printf("%-40s  %s\n", "NAME", "TYPE")
	fmt.Println(string(make([]byte, 46)))
	for _, e := range dir.Data.DirList {
		kind := "file"
		if e.Type == 0 {
			kind = "dir "
		}
		if e.Size > 0 {
			fmt.Printf("%-40s  %s  %d bytes\n", e.Filename, kind, e.Size)
		} else {
			fmt.Printf("%-40s  %s\n", e.Filename, kind)
		}
	}
	fmt.Printf("\n%d entries\n", len(dir.Data.DirList))
}

// readRaw accumulates all bytes from the port until nothing arrives for
// idleTimeout, or the outer deadline is hit, or maxBytes is reached.
// It prints a progress indicator for large transfers.
func readRaw(port serial.Port, deadline time.Time, idleTimeout time.Duration, maxBytes int) []byte {
	if err := port.SetReadTimeout(50 * time.Millisecond); err != nil {
		log.Printf("SetReadTimeout: %v", err)
	}
	var all []byte
	tmp := make([]byte, 8192)
	lastRecv := time.Now()
	lastPrint := time.Now()
	for time.Now().Before(deadline) {
		n, _ := port.Read(tmp)
		if n > 0 {
			all = append(all, tmp[:n]...)
			lastRecv = time.Now()
			if time.Since(lastPrint) > time.Second {
				fmt.Printf("\r  received %d bytes...", len(all))
				lastPrint = time.Now()
			}
		} else if time.Since(lastRecv) > idleTimeout {
			break
		}
		if maxBytes > 0 && len(all) >= maxBytes {
			break
		}
	}
	if len(all) > 0 {
		fmt.Printf("\r  received %d bytes        \n", len(all))
	}
	return all
}

// cmdReadFile attempts to read a file from the device using key 8 (speculative).
// Uses -timeout for the outer deadline; idle detection is 2 s after last byte.
func cmdReadFile(devicePath, outputFile string) {
	port := openPort()
	defer port.Close()

	fmt.Printf("Reading %q (key %d, timeout %v)...\n", devicePath, keyReadFile, *fTimeout)
	fmt.Println("Tip: use -timeout 60s for large files")

	frame := buildFrame(keyReadFile, []byte(devicePath))
	if *fVerbose {
		fmt.Fprintf(os.Stderr, "  TX: %s\n", hex.EncodeToString(frame))
	}
	if _, err := port.Write(frame); err != nil {
		log.Fatalf("write: %v", err)
	}

	// Wait up to fTimeout total; declare idle after 2 s of silence.
	all := readRaw(port, time.Now().Add(*fTimeout), 2*time.Second, 0)

	if len(all) == 0 {
		fmt.Println("No response.")
		fmt.Printf("Suggestions:\n")
		fmt.Printf("  1. Try a longer timeout: sudo ./jl_tool -timeout 60s readfile %s %s\n", devicePath, outputFile)
		fmt.Printf("  2. Probe other keys with the path:\n")
		fmt.Printf("       sudo ./jl_tool probe-path %s\n", devicePath)
		return
	}

	if *fVerbose {
		preview := all
		if len(preview) > 64 {
			preview = preview[:64]
		}
		fmt.Fprintf(os.Stderr, "  RX preview: %s...\n", hex.EncodeToString(preview))
	}

	// Strip a leading framed header if present; remainder is file content.
	content := all
	if hdr, rest := extractFrame(all); hdr != nil && len(rest) > 0 {
		payload := framePayload(hdr)
		fmt.Printf("Header frame: %s  payload: %q\n", hex.EncodeToString(hdr), string(payload))
		content = rest
	} else if hdr != nil && len(rest) == 0 {
		if p := framePayload(hdr); len(p) > 0 {
			content = p
		}
	}

	if outputFile == "" || outputFile == "-" {
		os.Stdout.Write(content)
	} else {
		if err := os.WriteFile(outputFile, content, 0o644); err != nil {
			log.Fatalf("write %s: %v", outputFile, err)
		}
		fmt.Printf("Saved %d bytes → %s\n", len(content), outputFile)
	}
}

// cmdProbePath sends each key in 2–20 (minus scan-skip list) with the given
// path as payload, and prints the response.  Used to find file read/write keys.
func cmdProbePath(path string) {
	port := openPort()
	defer port.Close()

	pathHex := hex.EncodeToString([]byte(path))
	fmt.Printf("Probing keys 2–20 with path %q (hex: %s)\n\n", path, pathHex)

	// Skip serial-num/motor writes but include key 12 here – with a path payload
	// it should just respond (not start a destructive OTA if path != firmware path).
	skip := map[int]bool{keySetSerialNum: true, keySetMotor: true}

	for key := 2; key <= 20; key++ {
		if skip[key] {
			fmt.Printf("Key %2d: SKIPPED\n", key)
			continue
		}
		frame := buildFrame(byte(key), []byte(path))
		if *fVerbose {
			fmt.Fprintf(os.Stderr, "  TX[%d]: %s\n", key, hex.EncodeToString(frame))
		}
		if _, err := port.Write(frame); err != nil {
			fmt.Printf("Key %2d: write error: %v\n", key, err)
			continue
		}

		// Use a 1-second idle timeout; for keys that stream file data this
		// gives them time to start.  The outer deadline is 5 s.
		all := readRaw(port, time.Now().Add(5*time.Second), 1*time.Second, 32*1024)
		if len(all) == 0 {
			fmt.Printf("Key %2d: no response\n", key)
			continue
		}

		// Pretty-print
		hdr, rest := extractFrame(all)
		if hdr != nil && len(rest) == 0 {
			payload := framePayload(hdr)
			if len(payload) > 0 {
				var v interface{}
				if json.Unmarshal(payload, &v) == nil {
					out, _ := json.Marshal(v)
					fmt.Printf("Key %2d: JSON → %s\n", key, out)
				} else {
					fmt.Printf("Key %2d: payload %d bytes → %s\n", key, len(payload), hex.EncodeToString(payload))
				}
			} else {
				fmt.Printf("Key %2d: framed response, no payload: %s\n", key, hex.EncodeToString(hdr))
			}
		} else if hdr != nil && len(rest) > 0 {
			payload := framePayload(hdr)
			fmt.Printf("Key %2d: framed header (%q) + %d raw bytes (first 16: %s)\n",
				key, string(payload), len(rest), hex.EncodeToString(rest[:min16(rest)]))
		} else {
			fmt.Printf("Key %2d: raw %d bytes → %s\n", key, len(all), hex.EncodeToString(all[:min16(all)]))
		}

		time.Sleep(50 * time.Millisecond)
	}
}

func min16(b []byte) int {
	if len(b) < 16 {
		return len(b)
	}
	return 16
}

// writeFileData sends raw file data in 20 kB chunks and prints progress.
func writeFileData(port serial.Port, data []byte) {
	chunkSize := 20480
	sent := 0
	start := time.Now()
	for sent < len(data) {
		end := sent + chunkSize
		if end > len(data) {
			end = len(data)
		}
		if _, err := port.Write(data[sent:end]); err != nil {
			log.Fatalf("write chunk at offset %d: %v", sent, err)
		}
		sent = end
		elapsed := time.Since(start).Seconds()
		kbps := float64(sent) / 1024 / elapsed
		fmt.Printf("\r  %d/%d bytes  %.1f%%  %.0f kB/s   ",
			sent, len(data), float64(sent)/float64(len(data))*100, kbps)
	}
	fmt.Println()
}

// cmdWriteFile attempts to upload a local file to a specific path on the device.
// It tries three approaches in order and reports results for each:
//
//  1. Key 9 (speculative "write file"):   send key 9 with path payload, then raw data.
//  2. Key 12 path variant:                send key 12 with [path + NUL + size(4LE)], then raw data.
//  3. Key 12 OTA variant with path hint:  send key 12 with [0xF1, 0xFF, size(4LE), path(NUL-term)].
//
// Use -key N to force a specific key instead of trying all three.
func cmdWriteFile(devicePath, localFile string, keyOverride int) {
	data, err := os.ReadFile(localFile)
	if err != nil {
		log.Fatalf("read %s: %v", localFile, err)
	}
	sz := uint32(len(data))
	pathBytes := []byte(devicePath)

	fmt.Printf("File: %s (%d bytes)\n", localFile, len(data))
	fmt.Printf("Destination: %s\n", devicePath)
	fmt.Println("WARNING: Experimental – no confirmed write key yet.")
	fmt.Println("Press Ctrl-C within 3 s to abort...")
	time.Sleep(3 * time.Second)
	fmt.Println()

	type attempt struct {
		desc    string
		key     int
		payload []byte
	}

	var attempts []attempt

	if keyOverride != 0 {
		// User forced a specific key – try path-only, then path+NUL+size
		attempts = []attempt{
			{
				desc:    fmt.Sprintf("forced key %d: path only", keyOverride),
				key:     keyOverride,
				payload: pathBytes,
			},
			{
				desc:    fmt.Sprintf("forced key %d: path+NUL+size", keyOverride),
				key:     keyOverride,
				payload: append(append(pathBytes, 0x00), byte(sz), byte(sz>>8), byte(sz>>16), byte(sz>>24)),
			},
		}
	} else {
		// Attempt 1: key 10, path only.
		// Rationale: probe-path showed key 10 returns 0x07 ("file write failed")
		// when given a file path with no data.  Sending data after the ACK may succeed.
		attempts = append(attempts, attempt{
			desc:    "key 10 (MOST LIKELY): path only → then send data",
			key:     keyWriteFile2,
			payload: pathBytes,
		})
		// Attempt 2: key 10 with path+NUL+size
		attempts = append(attempts, attempt{
			desc:    "key 10: path+NUL+size → then send data",
			key:     keyWriteFile2,
			payload: append(append(pathBytes, 0x00), byte(sz), byte(sz>>8), byte(sz>>16), byte(sz>>24)),
		})
		// Attempt 3: key 12 with path only (path-addressed file receive)
		// Rationale: key 12 is the confirmed OTA receiver; maybe with a path it
		// writes to that path instead of the firmware location.
		attempts = append(attempts, attempt{
			desc:    "key 12: path only",
			key:     keyOTAInit,
			payload: pathBytes,
		})
		// Attempt 4: key 12 with path+NUL+size
		attempts = append(attempts, attempt{
			desc:    "key 12: path+NUL+size",
			key:     keyOTAInit,
			payload: append(append(pathBytes, 0x00), byte(sz), byte(sz>>8), byte(sz>>16), byte(sz>>24)),
		})
		// Attempt 5: key 12 with [0xF1, 0xFF, size(4LE), path(NUL-term)]
		// (mirrors confirmed OTA prefix but 0xF1 instead of 0xF2)
		hdr5 := []byte{0xF1, 0xFF, byte(sz), byte(sz >> 8), byte(sz >> 16), byte(sz >> 24), 0, 0, 0, 0}
		hdr5 = append(hdr5, append(pathBytes, 0x00)...)
		attempts = append(attempts, attempt{
			desc:    "key 12: [0xF1,0xFF,size,path]",
			key:     keyOTAInit,
			payload: hdr5,
		})
	}

	for i, a := range attempts {
		fmt.Printf("--- Attempt %d: %s ---\n", i+1, a.desc)

		port := openPort()

		frame := buildFrame(byte(a.key), a.payload)
		if *fVerbose {
			fmt.Fprintf(os.Stderr, "  TX: %s\n", hex.EncodeToString(frame))
		}
		if _, err := port.Write(frame); err != nil {
			fmt.Printf("  Write error: %v\n\n", err)
			port.Close()
			continue
		}

		resp := readFrame(port, 2*time.Second)
		if len(resp) == 0 {
			fmt.Println("  No response to init – this key/format was rejected.")
			port.Close()
			fmt.Println()
			time.Sleep(200 * time.Millisecond)
			continue
		}

		initPayload := framePayload(resp)
		initHex := ""
		if len(initPayload) > 0 {
			initHex = hex.EncodeToString(initPayload)
		}
		fmt.Printf("  Init response: %s  payload: %q\n", hex.EncodeToString(resp), string(initPayload))

		// Interpret known error codes from appConstant.js
		errMsgs := map[string]string{
			"01": "operation failed", "02": "out of memory",
			"03": "internal storage full", "04": "SD card full",
			"05": "file not found", "06": "file open failed", "07": "file write failed",
		}
		if msg, isErr := errMsgs[initHex]; isErr {
			// Error code returned immediately – but for key 10 with "07" this might
			// mean "write failed because no data yet".  Try sending data anyway.
			fmt.Printf("  Device returned error: %s (%s)\n", initHex, msg)
			if initHex != "07" {
				// Hard error – skip data send
				port.Close()
				fmt.Println()
				time.Sleep(200 * time.Millisecond)
				continue
			}
			fmt.Println("  Error 07 may mean 'ready but expects data' – attempting data send...")
		}

		// Send file data
		fmt.Printf("  Sending %d bytes...\n", len(data))
		writeFileData(port, data)

		// Wait for completion ACK
		fmt.Println("  Waiting for completion ACK (30 s)...")
		final := readFrame(port, 30*time.Second)
		if len(final) > 0 {
			fmt.Printf("  Final: %s", hex.EncodeToString(final))
			if fp := framePayload(final); len(fp) > 0 {
				fph := hex.EncodeToString(fp)
				fmt.Printf("  (%q)", string(fp))
				if msg, isErr := errMsgs[fph]; isErr {
					fmt.Printf(" [%s]", msg)
				} else if fph == "00" {
					fmt.Printf(" [success]")
				}
			}
			fmt.Println()
			// 0x00 payload or no error = success
			fp := framePayload(final)
			if len(fp) == 0 || hex.EncodeToString(fp) == "00" {
				fmt.Println("  → Looks like SUCCESS")
				port.Close()
				return
			}
		} else {
			fmt.Println("  No completion ACK.")
		}

		port.Close()
		fmt.Println()
		time.Sleep(500 * time.Millisecond) // brief pause before next attempt
	}

	fmt.Println("\nAll attempts completed.")
	fmt.Println("If none worked, run probe-path on the destination directory:")
	fmt.Printf("  sudo ./jl_tool probe-path %s\n", devicePath)
}

// cmdUploadMedia uploads a video/image file via key 12 using sub-command
// variants of the confirmed OTA pattern.
//
// Confirmed OTA (firmware):  key 12 + [0xF2, 0xFF, size(4LE), 0,0,0,0]
//                            then raw firmware data → device updates firmware
//
// Hypothesis for media:      key 12 + [0xF1, 0xFF, size(4LE), 0,0,0,0]
//                            writes to /data/video/tempvideo.mp4
//
// This mirrors the only confirmed file-upload mechanism in the firmware and
// should be the first thing to try for video replacement.
func cmdUploadMedia(localFile string) {
	data, err := os.ReadFile(localFile)
	if err != nil {
		log.Fatalf("read %s: %v", localFile, err)
	}
	sz := uint32(len(data))

	fmt.Printf("File: %s (%d bytes)\n", localFile, len(data))
	fmt.Println("Target: /data/video/tempvideo.mp4 (hardcoded in firmware)")
	fmt.Println("WARNING: Experimental. Press Ctrl-C within 3 s to abort...")
	time.Sleep(3 * time.Second)
	fmt.Println()

	// Sub-command variants to try for key 12.
	// 0xF2 = confirmed firmware OTA → try nearby values for media.
	subCmds := []struct {
		b0, b1 byte
		desc   string
	}{
		{0xF1, 0xFF, "0xF1 0xFF (video hypothesis – mirror of 0xF2 OTA)"},
		{0xF0, 0xFF, "0xF0 0xFF"},
		{0xF3, 0xFF, "0xF3 0xFF"},
		{0xF4, 0xFF, "0xF4 0xFF"},
		{0x01, 0xFF, "0x01 0xFF"},
		{0x00, 0xFF, "0x00 0xFF"},
	}

	for i, sc := range subCmds {
		fmt.Printf("--- Variant %d: key 12 + [0x%02X, 0x%02X, size…] (%s) ---\n",
			i+1, sc.b0, sc.b1, sc.desc)

		port := openPort()

		payload := []byte{sc.b0, sc.b1,
			byte(sz), byte(sz >> 8), byte(sz >> 16), byte(sz >> 24),
			0, 0, 0, 0}
		frame := buildFrame(keyOTAInit, payload)
		if *fVerbose {
			fmt.Fprintf(os.Stderr, "  TX: %s\n", hex.EncodeToString(frame))
		}
		if _, err := port.Write(frame); err != nil {
			fmt.Printf("  Write error: %v\n\n", err)
			port.Close()
			continue
		}

		resp := readFrame(port, 2*time.Second)
		if len(resp) == 0 {
			fmt.Println("  No response – rejected.")
			port.Close()
			fmt.Println()
			continue
		}
		respPayload := framePayload(resp)
		respHex := hex.EncodeToString(respPayload)
		fmt.Printf("  Init ACK: %s  payload byte: %s\n", hex.EncodeToString(resp), respHex)

		// 0x01 = operation failed → skip data send
		if respHex == "01" {
			fmt.Println("  Device returned 0x01 (operation failed) – skipping.")
			port.Close()
			fmt.Println()
			continue
		}

		// Any other response (0x00 = likely "ready") → send data
		fmt.Printf("  Sending %d bytes...\n", len(data))
		chunkSize := 20480
		sent := 0
		start := time.Now()
		for sent < len(data) {
			end := sent + chunkSize
			if end > len(data) {
				end = len(data)
			}
			if _, err := port.Write(data[sent:end]); err != nil {
				log.Fatalf("  Write chunk at %d: %v", sent, err)
			}
			sent = end
			elapsed := time.Since(start).Seconds()
			kbps := float64(sent) / 1024 / elapsed
			fmt.Printf("\r  %d/%d bytes  %.1f%%  %.0f kB/s   ",
				sent, len(data), float64(sent)/float64(len(data))*100, kbps)
		}
		fmt.Println()

		// Wait for completion ACK
		fmt.Println("  Waiting for ACK (10 s)...")
		final := readFrame(port, 10*time.Second)
		port.Close()

		if len(final) > 0 {
			fp := framePayload(final)
			fph := hex.EncodeToString(fp)
			fmt.Printf("  Final ACK: %s  payload: %q\n", hex.EncodeToString(final), string(fp))
			if fph == "00" || len(fp) == 0 {
				fmt.Println("  → Possible SUCCESS – check with: sudo ./jl_tool ls /data/video")
				return
			}
		} else {
			fmt.Println("  No completion ACK (data accepted but device silent – may have succeeded).")
			fmt.Println("  Check: sudo ./jl_tool ls /data/video")
		}
		fmt.Println()
	}
}

// ---------------------------------------------------------------------------
// Display protocol helpers
// ---------------------------------------------------------------------------

// streamHandshake performs the startup sequence before streaming or showing an image.
//
//  1. Query device info (key 6) – confirms connection.
//  2. Send zero-size stream-init packet (PoC empirical format).
//  3. Trigger live mode (key 17).
func streamHandshake(port serial.Port) error {
	fmt.Print("Handshaking... ")

	resp := sendCmd(port, keyGetInfo, nil)
	if len(resp) == 0 {
		return fmt.Errorf("no response to getInfo – check device and baud rate")
	}
	if payload := framePayload(resp); len(payload) > 0 {
		if info := shortDeviceInfo(payload); info != "" {
			fmt.Printf("%s ", info)
		}
	}

	// Trigger live mode. The JS source sends key 17 here with no preceding
	// zero-size packet (that was a PoC artifact not present in the official app).
	sendCmdNoReply(port, keyLiveTrigger, nil)
	time.Sleep(50 * time.Millisecond)

	fmt.Println("OK")
	return nil
}

// sendStreamFrame sends one JPEG frame to the display.
//
// Matches the JS source (device.js sendPic): flush output buffer first to
// discard any partially-sent previous frame, then write raw JPEG bytes
// directly — no size-announce packet (that was a PoC artifact).
func sendStreamFrame(port serial.Port, jpegBuf []byte) error {
	// Flush pending output so a stale partial frame never reaches the device.
	port.ResetOutputBuffer()
	if _, err := port.Write(jpegBuf); err != nil {
		return fmt.Errorf("jpeg write: %w", err)
	}
	return nil
}

func shortDeviceInfo(payload []byte) string {
	var v struct {
		Data struct {
			Model   string `json:"model"`
			Version string `json:"version"`
			Width   int    `json:"width"`
			Height  int    `json:"height"`
		} `json:"data"`
	}
	if err := json.Unmarshal(payload, &v); err != nil {
		return ""
	}
	return fmt.Sprintf("%s v%s %dx%d", v.Data.Model, v.Data.Version, v.Data.Width, v.Data.Height)
}

// ---------------------------------------------------------------------------
// Image rendering helpers
// ---------------------------------------------------------------------------

// fitImage scales src to dispW×dispH.
// -stretch: fills completely (may distort aspect ratio).
// default (letterbox): scales to fit with black bars.
func fitImage(src image.Image, stretch bool) *image.RGBA {
	dst := image.NewRGBA(image.Rect(0, 0, dispW, dispH))
	// fill black first (for letterbox bars)
	for i := range dst.Pix {
		dst.Pix[i] = 0
	}

	srcW := src.Bounds().Dx()
	srcH := src.Bounds().Dy()

	if stretch {
		xdraw.BiLinear.Scale(dst, dst.Bounds(), src, src.Bounds(), xdraw.Over, nil)
		return dst
	}

	// Letterbox: fit within dispW×dispH preserving aspect ratio
	scaleX := float64(dispW) / float64(srcW)
	scaleY := float64(dispH) / float64(srcH)
	scale := scaleX
	if scaleY < scale {
		scale = scaleY
	}
	fitW := int(float64(srcW) * scale)
	fitH := int(float64(srcH) * scale)
	offX := (dispW - fitW) / 2
	offY := (dispH - fitH) / 2
	dstRect := image.Rect(offX, offY, offX+fitW, offY+fitH)
	xdraw.BiLinear.Scale(dst, dstRect, src, src.Bounds(), xdraw.Over, nil)
	return dst
}

// rotateImage90CCW returns a 90° counter-clockwise rotation of src.
// The display panel is physically rotated 90° CW, so we pre-rotate CCW
// to compensate and render content upright.
func rotateImage90CCW(src *image.RGBA) *image.RGBA {
	b := src.Bounds()
	w, h := b.Dx(), b.Dy()
	dst := image.NewRGBA(image.Rect(0, 0, h, w))
	for y := 0; y < h; y++ {
		for x := 0; x < w; x++ {
			dst.Set(y, w-1-x, src.At(x+b.Min.X, y+b.Min.Y))
		}
	}
	return dst
}

// encodeJPEG encodes an image as JPEG at the given quality.
func encodeJPEG(img image.Image, q int) ([]byte, error) {
	var buf bytes.Buffer
	if err := jpeg.Encode(&buf, img, &jpeg.Options{Quality: q}); err != nil {
		return nil, err
	}
	return buf.Bytes(), nil
}

// encodeJPEGSized encodes img as JPEG, backing off quality by 5 each retry
// until the result fits within maxKB kilobytes (or quality reaches 20).
// Mirrors the JS getSizeBt() behaviour. Pass maxKB=0 to skip size limiting.
// Returns the encoded bytes and the quality actually used.
func encodeJPEGSized(img image.Image, startQ, maxKB int) ([]byte, int, error) {
	q := startQ
	for {
		buf, err := encodeJPEG(img, q)
		if err != nil {
			return nil, q, err
		}
		if maxKB == 0 || len(buf) <= maxKB*1024 {
			return buf, q, nil
		}
		if q <= 20 {
			return buf, q, nil // can't reduce further
		}
		q -= 5
	}
}

// ---------------------------------------------------------------------------
// show-image: display a JPEG/PNG file on the screen
// ---------------------------------------------------------------------------

// cmdShowImage loads an image file, resizes it to the display dimensions,
// sends it once, then holds the display by resending key 17 every second.
// The image stays visible until Ctrl-C.
func cmdShowImage(path string) {
	raw, err := os.ReadFile(path)
	if err != nil {
		log.Fatalf("read %s: %v", path, err)
	}
	src, fmt_, err := image.Decode(bytes.NewReader(raw))
	if err != nil {
		log.Fatalf("decode image: %v", err)
	}
	b := src.Bounds()
	fmt.Printf("Image: %s  %dx%d  format: %s\n", path, b.Dx(), b.Dy(), fmt_)

	// Scale to display resolution first (single clean BiLinear pass),
	// then rotate pixel-perfectly. Produces a 462×1920 JPEG for landscape
	// mode, or a direct 1920×462 for -rotate=false.
	var out image.Image
	if *fRotate {
		out = rotateImage90CCW(fitImage(src, *fStretch))
	} else {
		out = fitImage(src, *fStretch)
	}
	jpegBuf, _, err := encodeJPEGSized(out, *fQuality, *fMaxFrameKB)
	if err != nil {
		log.Fatalf("encode: %v", err)
	}
	fmt.Printf("Encoded: %d bytes  quality: %d  rotate: %v\n", len(jpegBuf), *fQuality, *fRotate)

	port := openPort()
	defer port.Close()

	if err := streamHandshake(port); err != nil {
		log.Fatalf("handshake: %v", err)
	}

	fmt.Println("Sending image...")
	if err := sendStreamFrame(port, jpegBuf); err != nil {
		log.Fatalf("send: %v", err)
	}
	fmt.Println("Displayed. Holding with keep-alive (Ctrl-C to stop)...")

	// Keep device in live mode; re-send the frame every 5 s in case the
	// device resets its buffer.
	tick17 := time.NewTicker(1500 * time.Millisecond)
	tickFrame := time.NewTicker(5 * time.Second)
	defer tick17.Stop()
	defer tickFrame.Stop()

	for {
		select {
		case <-tick17.C:
			sendCmdNoReply(port, keyLiveTrigger, nil)
		case <-tickFrame.C:
			sendStreamFrame(port, jpegBuf)
		}
	}
}

// ---------------------------------------------------------------------------
// stream: desktop mirror
// ---------------------------------------------------------------------------

// cmdStream mirrors the desktop to the display continuously.
func cmdStream() {
	port := openPort()
	defer port.Close()

	capX, capY, capW, capH := *fCapX, *fCapY, *fCapW, *fCapH
	fps := *fFPS
	qual := *fQuality
	rotate := *fRotate

	fmt.Printf("Streaming desktop → display %dx%d @ up to %d fps  quality %d\n",
		dispW, dispH, fps, qual)
	fmt.Printf("Capture region: %dx%d at (%d,%d)\n", capW, capH, capX, capY)
	if rotate {
		fmt.Println("Mode: 90° CW rotation (tall→wide)")
	} else {
		fmt.Println("Mode: direct scale (letterbox)")
	}

	if err := streamHandshake(port); err != nil {
		log.Fatalf("handshake: %v", err)
	}

	method := detectCapture()
	fmt.Printf("Capture: %s\nCtrl-C to stop\n", method)

	// Keep-alive: JS keepSending() fires key 17 every 1500 ms continuously.
	go func() {
		tick := time.NewTicker(1500 * time.Millisecond)
		defer tick.Stop()
		for range tick.C {
			sendCmdNoReply(port, keyLiveTrigger, nil)
		}
	}()

	frameDur := time.Second / time.Duration(fps)
	frameNum := 0
	curQual := qual
	maxKB := *fMaxFrameKB

	for {
		start := time.Now()

		raw, err := captureScreenRegion(capX, capY, capW, capH)
		if err != nil {
			fmt.Fprintf(os.Stderr, "\ncapture error: %v – retrying\n", err)
			time.Sleep(500 * time.Millisecond)
			continue
		}

		jpegBuf, err := processStreamFrame(raw, capW, capH, curQual, rotate, maxKB)
		if err != nil {
			fmt.Fprintf(os.Stderr, "\nframe error: %v – skipping\n", err)
			continue
		}

		// Track quality drift so future frames start from the last-used quality.
		curQual = int(float64(len(jpegBuf)) / float64(maxKB*1024) * float64(qual))
		if curQual < 20 {
			curQual = 20
		} else if curQual > qual {
			curQual = qual
		}

		if err := sendStreamFrame(port, jpegBuf); err != nil {
			log.Fatalf("send frame %d: %v", frameNum, err)
		}

		frameNum++
		elapsed := time.Since(start)
		actualFPS := float64(time.Second) / float64(elapsed)
		fmt.Printf("\rframe %-6d  %5d bytes  q%-3d  %4.1f fps   ", frameNum, len(jpegBuf), curQual, actualFPS)

		if sleep := frameDur - elapsed; sleep > 0 {
			time.Sleep(sleep)
		}
	}
}

// processStreamFrame converts a raw captured image to a JPEG suitable for the display.
// processStreamFrame converts a raw captured image to a JPEG for the display.
//
// rotate=true (landscape): fitImage → 1920×462 (one clean BiLinear pass)
//                           then rotateImage90CCW → 462×1920 JPEG (pixel-perfect).
// rotate=false (direct):   fitImage → 1920×462 JPEG sent as-is.
//
// Old pipeline scaled to the TRANSPOSED dims (462×1920) first, causing heavy
// distortion; this pipeline scales to the correct display dims first.
func processStreamFrame(raw []byte, capW, capH, qual int, rotate bool, maxKB int) ([]byte, error) {
	src, _, err := image.Decode(bytes.NewReader(raw))
	if err != nil {
		return nil, fmt.Errorf("decode: %w", err)
	}

	var out image.Image
	if rotate {
		out = rotateImage90CCW(fitImage(src, *fStretch))
	} else {
		out = fitImage(src, *fStretch)
	}

	buf, _, err := encodeJPEGSized(out, qual, maxKB)
	return buf, err
}

// ---------------------------------------------------------------------------
// test-pattern: verify the transformation pipeline visually
// ---------------------------------------------------------------------------

// cmdTestPattern generates a colour-quadrant test card, runs it through the
// same pipeline used by show-image / stream, and saves each stage as a PNG
// to /tmp so you can open them in any image viewer and check for mangling.
//
//	Stage 1 – source:   1920×462 with red TL, green TR, blue BL, yellow BR
//	Stage 2 – fitted:   after fitImage  (should be identical for a 1920×462 source)
//	Stage 3 – rotated:  after rotateImage90CCW → 462×1920
//	Stage 4 – final:    decoded back from the JPEG that would be sent to device
//
// Correct result: when the device rotates stage 3 by 90° CW it reproduces
// stage 1, so opening stage 3 and rotating it CW in any viewer shows stage 1.
func cmdTestPattern() {
	src := image.NewRGBA(image.Rect(0, 0, dispW, dispH))
	midX, midY := dispW/2, dispH/2

	// Draw labelled colour quadrants with an intensity gradient so orientation
	// within each quadrant is also clear (left→right gets brighter).
	for y := 0; y < dispH; y++ {
		for x := 0; x < dispW; x++ {
			grad := uint8(float64(x%midX) / float64(midX) * 80)
			switch {
			case x < midX && y < midY: // top-left: red
				src.SetRGBA(x, y, color.RGBA{160 + grad, 0, 0, 255})
			case x >= midX && y < midY: // top-right: green
				src.SetRGBA(x, y, color.RGBA{0, 160 + grad, 0, 255})
			case x < midX && y >= midY: // bottom-left: blue
				src.SetRGBA(x, y, color.RGBA{0, 0, 160 + grad, 255})
			default: // bottom-right: yellow
				src.SetRGBA(x, y, color.RGBA{160 + grad, 160 + grad, 0, 255})
			}
		}
	}
	// White centre cross so the exact midpoint is visible.
	for x := 0; x < dispW; x++ {
		src.SetRGBA(x, midY, color.RGBA{255, 255, 255, 255})
	}
	for y := 0; y < dispH; y++ {
		src.SetRGBA(midX, y, color.RGBA{255, 255, 255, 255})
	}

	save := func(path string, img image.Image) {
		f, err := os.Create(path)
		if err != nil {
			log.Fatalf("create %s: %v", path, err)
		}
		defer f.Close()
		if err := png.Encode(f, img); err != nil {
			log.Fatalf("encode %s: %v", path, err)
		}
	}

	save("/tmp/jl_test_1_source.png", src)
	fmt.Printf("1. source   %4dx%-4d  /tmp/jl_test_1_source.png\n", src.Bounds().Dx(), src.Bounds().Dy())

	fitted := fitImage(src, false)
	save("/tmp/jl_test_2_fitted.png", fitted)
	fmt.Printf("2. fitted   %4dx%-4d  /tmp/jl_test_2_fitted.png\n", fitted.Bounds().Dx(), fitted.Bounds().Dy())

	rotated := rotateImage90CCW(fitted)
	save("/tmp/jl_test_3_rotated.png", rotated)
	fmt.Printf("3. rotated  %4dx%-4d  /tmp/jl_test_3_rotated.png  ← this JPEG is sent to device\n",
		rotated.Bounds().Dx(), rotated.Bounds().Dy())

	// Round-trip through JPEG to show compression artefacts at current quality.
	jpegBuf, finalQ, _ := encodeJPEGSized(rotated, *fQuality, *fMaxFrameKB)
	rt, _, _ := image.Decode(bytes.NewReader(jpegBuf))
	save("/tmp/jl_test_4_jpeg_roundtrip.png", rt)
	fmt.Printf("4. roundtrip %4dx%-4d  /tmp/jl_test_4_jpeg_roundtrip.png  (%d bytes, quality %d)\n",
		rt.Bounds().Dx(), rt.Bounds().Dy(), len(jpegBuf), finalQ)

	fmt.Println()
	fmt.Println("Expected layout of stage 3 (sent to device):")
	fmt.Println("  The image is 462 wide × 1920 tall.")
	fmt.Println("  Rotate it 90° CW in any viewer — it should look identical to stage 1.")
	fmt.Println("  red=TL  green=TR  blue=BL  yellow=BR  white cross at centre")
}

// ---------------------------------------------------------------------------
// browser-stream: headless Chromium → display
// ---------------------------------------------------------------------------

// cmdBrowserStream launches a headless Chromium window sized to the display,
// navigates to startURL, and streams screenshots to the device at the
// configured FPS. Type a URL on stdin and press Enter to navigate live.
//
// Requires Chromium/Chrome installed:
//
//	sudo apt install chromium-browser   # Ubuntu
//	sudo apt install chromium           # Debian
func cmdBrowserStream(startURL string) {
	rotate := *fRotate

	// Viewport dimensions depend on orientation:
	//   rotate=true  (landscape): browser at dispW×dispH (1920×462), pipeline
	//                             compensates for the physical panel rotation.
	//   rotate=false (vertical):  browser at dispH×dispW (462×1920), screenshot
	//                             sent as-is so the panel's physical rotation
	//                             displays the portrait content naturally.
	viewW, viewH := dispW, dispH
	if !rotate {
		viewW, viewH = dispH, dispW
	}

	opts := append(chromedp.DefaultExecAllocatorOptions[:],
		chromedp.WindowSize(viewW, viewH),
		chromedp.Flag("headless", *fHeadless),
		chromedp.Flag("no-sandbox", true), // required when running as root
		chromedp.Flag("disable-gpu", *fHeadless),
		chromedp.Flag("disable-software-rasterizer", *fHeadless),
	)

	allocCtx, allocCancel := chromedp.NewExecAllocator(context.Background(), opts...)
	defer allocCancel()

	ctx, cancel := chromedp.NewContext(allocCtx)
	defer cancel()

	mode := "landscape"
	if !rotate {
		mode = "vertical"
	}
	fmt.Printf("Launching browser %dx%d initial (%s) → %s\n", viewW, viewH, mode, startURL)
	if err := chromedp.Run(ctx, chromedp.Navigate(startURL)); err != nil {
		log.Fatalf("browser init: %v", err)
	}

	port := openPort()
	defer port.Close()

	if err := streamHandshake(port); err != nil {
		log.Fatalf("handshake: %v", err)
	}

	fps := *fFPS
	qual := *fQuality
	maxKB := *fMaxFrameKB
	frameDur := time.Second / time.Duration(fps)
	frameNum := 0

	fmt.Printf("Streaming @ up to %d fps  quality %d\n", fps, qual)
	fmt.Println("Type a URL + Enter to navigate. Ctrl-C to stop.")

	// Keep-alive: mirrors JS keepSending() — key 17 every 1500 ms.
	go func() {
		tick := time.NewTicker(1500 * time.Millisecond)
		defer tick.Stop()
		for range tick.C {
			sendCmdNoReply(port, keyLiveTrigger, nil)
		}
	}()

	// Accept navigation URLs from stdin without blocking the capture loop.
	urlCh := make(chan string, 4)
	go func() {
		sc := bufio.NewScanner(os.Stdin)
		for sc.Scan() {
			if u := strings.TrimSpace(sc.Text()); u != "" {
				urlCh <- u
			}
		}
	}()

	for {
		start := time.Now()

		// Non-blocking URL navigation
		select {
		case newURL := <-urlCh:
			fmt.Printf("\nNavigating to %s…\n", newURL)
			if err := chromedp.Run(ctx, chromedp.Navigate(newURL)); err != nil {
				fmt.Fprintf(os.Stderr, "navigate error: %v\n", err)
			}
		default:
		}

		var pngBuf []byte
		if err := chromedp.Run(ctx, chromedp.CaptureScreenshot(&pngBuf)); err != nil {
			fmt.Fprintf(os.Stderr, "\nscreenshot error: %v – retrying\n", err)
			time.Sleep(500 * time.Millisecond)
			continue
		}

		var (
			jpegBuf []byte
			err     error
		)
		if rotate {
			// Landscape: apply panel-rotation compensation via processStreamFrame.
			jpegBuf, err = processStreamFrame(pngBuf, viewW, viewH, qual, true, maxKB)
		} else {
			// Vertical: screenshot is already 462×1920; encode directly and send.
			// The physical panel rotation displays it correctly without any transform.
			src, _, decErr := image.Decode(bytes.NewReader(pngBuf))
			if decErr != nil {
				fmt.Fprintf(os.Stderr, "\ndecode error: %v – skipping\n", decErr)
				continue
			}
			jpegBuf, _, err = encodeJPEGSized(src, qual, maxKB)
		}
		if err != nil {
			fmt.Fprintf(os.Stderr, "\nframe error: %v – skipping\n", err)
			continue
		}

		if err := sendStreamFrame(port, jpegBuf); err != nil {
			log.Fatalf("send frame %d: %v", frameNum, err)
		}

		frameNum++
		elapsed := time.Since(start)
		actualFPS := float64(time.Second) / float64(elapsed)
		fmt.Printf("\rframe %-6d  %5d bytes  %4.1f fps   ", frameNum, len(jpegBuf), actualFPS)

		if sleep := frameDur - elapsed; sleep > 0 {
			time.Sleep(sleep)
		}
	}
}

// ---------------------------------------------------------------------------
// Screen capture
// ---------------------------------------------------------------------------

func detectCapture() string {
	isWayland := os.Getenv("WAYLAND_DISPLAY") != ""
	hasX11 := os.Getenv("DISPLAY") != ""
	switch {
	case isWayland && lookPath("grim"):
		return "grim (Wayland)"
	case isWayland && lookPath("wayshot"):
		return "wayshot (Wayland)"
	case hasX11 && lookPath("ffmpeg"):
		return "ffmpeg x11grab → stdout pipe (X11)"
	case hasX11 && lookPath("import"):
		return "ImageMagick import (X11)"
	case hasX11 && lookPath("scrot"):
		return "scrot (X11) [rings bell – install ffmpeg to suppress]"
	default:
		if isWayland {
			return "NONE – install grim: sudo apt install grim"
		}
		if hasX11 {
			return "NONE – install ffmpeg: sudo apt install ffmpeg"
		}
		return "NONE – no display found (WAYLAND_DISPLAY and DISPLAY are both unset; try: sudo -E ./jl_tool stream)"
	}
}

// captureScreenRegion captures the specified region of the desktop and returns PNG bytes.
// ffmpeg streams directly to stdout (no temp file); other tools fall back to a temp file.
func captureScreenRegion(x, y, w, h int) ([]byte, error) {
	isWayland := os.Getenv("WAYLAND_DISPLAY") != ""
	hasX11 := os.Getenv("DISPLAY") != ""

	// ffmpeg: pipe PNG to stdout — no temp file needed.
	if hasX11 && lookPath("ffmpeg") {
		cmd := exec.Command("ffmpeg", "-y", "-f", "x11grab",
			"-video_size", fmt.Sprintf("%dx%d", w, h),
			"-i", fmt.Sprintf("%s+%d,%d", os.Getenv("DISPLAY"), x, y),
			"-vframes", "1", "-f", "image2pipe", "-vcodec", "png", "pipe:1")
		cmd.Env = os.Environ()
		var stderr bytes.Buffer
		cmd.Stderr = &stderr
		data, err := cmd.Output()
		if err != nil {
			return nil, fmt.Errorf("%v: %s", err, stderr.String())
		}
		return data, nil
	}

	// All other tools write to a temp file.
	f, err := os.CreateTemp("", "jl_cap_*.png")
	if err != nil {
		return nil, fmt.Errorf("create temp file: %w", err)
	}
	tmp := f.Name()
	f.Close()
	defer os.Remove(tmp)

	var cmd *exec.Cmd
	switch {
	case isWayland && lookPath("grim"):
		cmd = exec.Command("grim", "-g",
			fmt.Sprintf("%d,%d %dx%d", x, y, w, h), tmp)
	case isWayland && lookPath("wayshot"):
		cmd = exec.Command("wayshot", "-f", tmp)
	case hasX11 && lookPath("import"):
		cmd = exec.Command("import", "-window", "root",
			"-crop", fmt.Sprintf("%dx%d+%d+%d", w, h, x, y), "+repage", tmp)
	case hasX11 && lookPath("scrot"):
		cmd = exec.Command("scrot", "--overwrite", tmp)
	default:
		if isWayland {
			return nil, fmt.Errorf("no capture tool – install grim: sudo apt install grim")
		}
		if hasX11 {
			return nil, fmt.Errorf("no capture tool – install ffmpeg: sudo apt install ffmpeg")
		}
		return nil, fmt.Errorf("no display found – WAYLAND_DISPLAY and DISPLAY are both unset; try: sudo -E ./jl_tool stream")
	}
	cmd.Env = os.Environ()
	if out, err := cmd.CombinedOutput(); err != nil {
		return nil, fmt.Errorf("%v: %s", err, out)
	}
	data, err := os.ReadFile(tmp)
	if err != nil {
		return nil, err
	}
	// If the capture tool ignored region flags (wayshot, scrot), crop manually.
	if !isWayland || lookPath("wayshot") || lookPath("scrot") {
		if x != 0 || y != 0 || w == 0 || h == 0 {
			return data, nil // return full screenshot; processStreamFrame will scale
		}
	}
	return data, nil
}

func lookPath(bin string) bool {
	_, err := exec.LookPath(bin)
	return err == nil
}

// ---------------------------------------------------------------------------
// Usage / main
// ---------------------------------------------------------------------------

func usage() {
	fmt.Fprintln(os.Stderr, `jl_tool – Jungle Leopard Display control utility

Usage:
  jl_tool [flags] <command> [args]

General flags:
  -device <path>       Serial device (default: /dev/ttyACM0)
  -baud <rate>         Baud rate (default: 2000000; try 115200 if 2000000 fails)
  -timeout <duration>  Response timeout (default: 3s)
  -v                   Print TX/RX frames as hex

Image/stream flags:
  -fps <n>             Target frames per second (default: 10)
  -quality <1-100>     JPEG quality (default: 80)
  -rotate              Compensate for physical 90° panel rotation so content
                       appears upright/landscape (default: true)
                       Use -rotate=false to display content vertically
  -stretch             Stretch to fill instead of letterbox (default: false)

Browser flags:
  -headless            Run browser without a visible window (default: true)
                       Use -headless=false to show the browser on your desktop

Commands:
  info                        Query device info and filesystem stats
  brightness <0-100>          Set display brightness
  restart                     Restart the device
  region [string]             Set region/config string (empty to clear)
  stop-live                   Send JPEG EOI to stop streaming

  show-image <path>           Display a JPEG or PNG file on the screen
                                jl_tool show-image photo.jpg
                                jl_tool -rotate=false show-image portrait.jpg

  stream                      Mirror desktop to display (requires ffmpeg/grim)

  browser-stream [url]        Stream a headless browser to the display
                                jl_tool browser-stream https://example.com
                                jl_tool -headless=false browser-stream https://example.com
                                jl_tool -rotate=false browser-stream https://example.com
                              While running, type a URL + Enter to navigate live.

  ls [path]                   List directory on device
                                jl_tool ls /data/video
  readfile <path> [out]       Read file from device
  writefile <path> <file>     Write local file to device path (speculative)

  probe-key <n> [hex]         Send key n with optional hex payload; print response
  probe-scan [start] [end]    Probe keys start–end (default 2–64)
  raw-write <hex>             Write raw hex bytes; print response

  close                       Soft-close signal (firmware v3.1+ only)
  upload <file>               Experimental OTA file upload – FIRMWARE BINS ONLY

Examples:
  jl_tool info
  jl_tool brightness 75
  jl_tool show-image photo.jpg
  jl_tool -rotate=false show-image portrait.png   # display vertically
  jl_tool browser-stream https://example.com
  jl_tool -headless=false -fps 5 browser-stream https://clock.example.com
  jl_tool -rotate=false browser-stream https://example.com   # vertical layout
  jl_tool -v probe-key 6`)
}

func main() {
	flag.Usage = usage
	flag.Parse()

	args := flag.Args()
	if len(args) == 0 {
		usage()
		os.Exit(1)
	}

	cmd, rest := args[0], args[1:]

	switch cmd {
	case "info":
		cmdInfo()

	case "brightness":
		if len(rest) == 0 {
			log.Fatal("usage: brightness <0-100>")
		}
		n, err := strconv.Atoi(rest[0])
		if err != nil || n < 0 || n > 100 {
			log.Fatal("brightness must be an integer 0–100")
		}
		cmdBrightness(n)

	case "restart":
		cmdRestart()

	case "region":
		r := ""
		if len(rest) > 0 {
			r = rest[0]
		}
		cmdRegion(r)

	case "close":
		cmdClose()

	case "stop-live":
		cmdStopLive()

	case "stream":
		cmdStream()

	case "browser-stream", "browser":
		url := "about:blank"
		if len(rest) > 0 {
			url = rest[0]
		}
		cmdBrowserStream(url)

	case "test-pattern":
		cmdTestPattern()

	case "show-image":
		if len(rest) == 0 {
			log.Fatal("usage: show-image <path>")
		}
		cmdShowImage(rest[0])

	case "probe-key":
		if len(rest) == 0 {
			log.Fatal("usage: probe-key <key> [hex-data]")
		}
		key, err := strconv.Atoi(rest[0])
		if err != nil || key < 0 || key > 255 {
			log.Fatalf("key must be 0–255, got %q", rest[0])
		}
		var data []byte
		if len(rest) > 1 {
			data, err = hex.DecodeString(rest[1])
			if err != nil {
				log.Fatalf("invalid hex payload: %v", err)
			}
		}
		cmdProbeKey(key, data)

	case "probe-scan":
		start, end := 1, 64
		if len(rest) >= 1 {
			if n, err := strconv.Atoi(rest[0]); err == nil {
				start = n
			}
		}
		if len(rest) >= 2 {
			if n, err := strconv.Atoi(rest[1]); err == nil {
				end = n
			}
		}
		cmdProbeScan(start, end, *fUnsafe)

	case "raw-write":
		if len(rest) == 0 {
			log.Fatal("usage: raw-write <hex-bytes>")
		}
		data, err := hex.DecodeString(rest[0])
		if err != nil {
			log.Fatalf("invalid hex: %v", err)
		}
		cmdRawWrite(data)

	case "upload":
		if len(rest) == 0 {
			log.Fatal("usage: upload <local-file>")
		}
		cmdUpload(rest[0])

	case "ls", "listdir":
		path := ""
		if len(rest) > 0 {
			path = rest[0]
		}
		cmdListDir(path)

	case "readfile":
		if len(rest) == 0 {
			log.Fatal("usage: readfile <device-path> [output-file]")
		}
		out := ""
		if len(rest) > 1 {
			out = rest[1]
		}
		cmdReadFile(rest[0], out)

	case "writefile":
		if len(rest) < 2 {
			log.Fatal("usage: writefile <device-path> <local-file>")
		}
		cmdWriteFile(rest[0], rest[1], *fKey)

	case "probe-path":
		if len(rest) == 0 {
			log.Fatal("usage: probe-path <device-path>")
		}
		cmdProbePath(rest[0])

	case "upload-media":
		if len(rest) == 0 {
			log.Fatal("usage: upload-media <local-file>")
		}
		cmdUploadMedia(rest[0])

	default:
		fmt.Fprintf(os.Stderr, "unknown command: %q\n\n", cmd)
		usage()
		os.Exit(1)
	}
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}
