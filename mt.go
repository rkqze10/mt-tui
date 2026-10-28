package main

import (
	"bufio"
	"context"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"runtime/debug"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/charmbracelet/bubbles/textinput"
	"github.com/charmbracelet/bubbles/viewport"
	tea "github.com/charmbracelet/bubbletea"
	"github.com/charmbracelet/lipgloss"
)

// ============================================================================
// 1. GENİŞ KARAKTER (WIDE RUNE) & 2D VIRTUAL FRAMEBUFFER MOTORU
// ============================================================================

func isWideRune(r rune) bool {
	return r >= 0x1100 &&
		(r <= 0x115f || r == 0x2329 || r == 0x232a ||
			(r >= 0x2e80 && r <= 0xa4cf && r != 0x303f) ||
			(r >= 0xac00 && r <= 0xd7a3) ||
			(r >= 0xf900 && r <= 0xfaff) ||
			(r >= 0xfe10 && r <= 0xfe19) ||
			(r >= 0xfe30 && r <= 0xfe6f) ||
			(r >= 0xff00 && r <= 0xff60) ||
			(r >= 0xffe0 && r <= 0xffe6) ||
			(r >= 0x20000 && r <= 0x2fffd) ||
			(r >= 0x30000 && r <= 0x3fffd) ||
			(r >= 0x1f300 && r <= 0x1f9ff) ||
			(r >= 0x2600 && r <= 0x27bf))
}

func runeDisplayWidth(r rune) int {
	if r == 0 {
		return 0
	}
	if isWideRune(r) {
		return 2
	}
	return 1
}

type Cell struct {
	Char rune
	Fg   lipgloss.TerminalColor
	Bg   lipgloss.TerminalColor
	Bold bool
}

type VirtualFramebuffer struct {
	Width  int
	Height int
	grid   [][]Cell
}

func NewVirtualFramebuffer(w, h int) *VirtualFramebuffer {
	if w < 1 {
		w = 1
	}
	if h < 1 {
		h = 1
	}
	fb := &VirtualFramebuffer{
		Width:  w,
		Height: h,
		grid:   make([][]Cell, h),
	}
	for y := 0; y < h; y++ {
		fb.grid[y] = make([]Cell, w)
	}
	return fb
}

func (fb *VirtualFramebuffer) SetPixel(x, y int, ch rune, fg, bg lipgloss.TerminalColor, bold bool) {
	if x < 0 || x >= fb.Width || y < 0 || y >= fb.Height {
		return
	}
	fb.grid[y][x] = Cell{
		Char: ch,
		Fg:   fg,
		Bg:   bg,
		Bold: bold,
	}
}

func (fb *VirtualFramebuffer) DrawText(x, y int, text string, fg, bg lipgloss.TerminalColor, bold bool) {
	col := x
	for _, r := range text {
		if col >= fb.Width {
			break
		}
		fb.SetPixel(col, y, r, fg, bg, bold)
		col += runeDisplayWidth(r)
	}
}

func (fb *VirtualFramebuffer) DrawBox(x, y, w, h int, title string, borderFg lipgloss.TerminalColor, bold bool) {
	if w < 2 || h < 2 || x >= fb.Width || y >= fb.Height {
		return
	}
	maxX := x + w - 1
	maxY := y + h - 1

	if maxX >= fb.Width {
		maxX = fb.Width - 1
	}
	if maxY >= fb.Height {
		maxY = fb.Height - 1
	}

	fb.SetPixel(x, y, '╭', borderFg, nil, bold)
	fb.SetPixel(maxX, y, '╮', borderFg, nil, bold)
	fb.SetPixel(x, maxY, '╰', borderFg, nil, bold)
	fb.SetPixel(maxX, maxY, '╯', borderFg, nil, bold)

	for curX := x + 1; curX < maxX; curX++ {
		fb.SetPixel(curX, y, '─', borderFg, nil, bold)
		fb.SetPixel(curX, maxY, '─', borderFg, nil, bold)
	}
	for curY := y + 1; curY < maxY; curY++ {
		fb.SetPixel(x, curY, '│', borderFg, nil, bold)
		fb.SetPixel(maxX, curY, '│', borderFg, nil, bold)
	}

	if title != "" && x+2 < maxX {
		t := " " + title + " "
		fb.DrawText(x+2, y, t, borderFg, nil, true)
	}
}

func (fb *VirtualFramebuffer) CompositeOnANSI(rawScreen string) string {
	lines := strings.Split(rawScreen, "\n")
	var result strings.Builder

	for y := 0; y < fb.Height; y++ {
		var srcLine string
		if y < len(lines) {
			srcLine = lines[y]
		}

		rowHasPixels := false
		for x := 0; x < fb.Width; x++ {
			if fb.grid[y][x].Char != 0 && fb.grid[y][x].Char != ' ' {
				rowHasPixels = true
				break
			}
		}

		if !rowHasPixels {
			result.WriteString(srcLine)
			if y < fb.Height-1 {
				result.WriteRune('\n')
			}
			continue
		}

		var rowOut strings.Builder
		runes := []rune(srcLine)
		rLen := len(runes)
		col := 0
		i := 0

		for i < rLen {
			if runes[i] == 0x1b && i+1 < rLen && runes[i+1] == '[' {
				end := i + 2
				for end < rLen && (runes[end] < 0x40 || runes[end] > 0x7e) {
					end++
				}
				if end < rLen {
					end++
				}
				rowOut.WriteString(string(runes[i:end]))
				i = end
				continue
			}

			w := runeDisplayWidth(runes[i])
			if col < fb.Width && fb.grid[y][col].Char != 0 && fb.grid[y][col].Char != ' ' {
				c := fb.grid[y][col]
				st := lipgloss.NewStyle()
				if c.Fg != nil {
					st = st.Foreground(c.Fg)
				}
				if c.Bg != nil {
					st = st.Background(c.Bg)
				}
				if c.Bold {
					st = st.Bold(true)
				}
				rowOut.WriteString(st.Render(string(c.Char)))
				if w == 2 && runeDisplayWidth(c.Char) == 1 {
					rowOut.WriteRune(' ')
				}
			} else {
				rowOut.WriteRune(runes[i])
			}
			col += w
			i++
		}

		for col < fb.Width {
			if fb.grid[y][col].Char != 0 && fb.grid[y][col].Char != ' ' {
				c := fb.grid[y][col]
				st := lipgloss.NewStyle()
				if c.Fg != nil {
					st = st.Foreground(c.Fg)
				}
				if c.Bg != nil {
					st = st.Background(c.Bg)
				}
				if c.Bold {
					st = st.Bold(true)
				}
				rowOut.WriteString(st.Render(string(c.Char)))
				col += runeDisplayWidth(c.Char)
			} else {
				rowOut.WriteRune(' ')
				col++
			}
		}

		result.WriteString(rowOut.String())
		if y < fb.Height-1 {
			result.WriteRune('\n')
		}
	}

	return result.String()
}

// ============================================================================
// 2. TEMA MOTORU
// ============================================================================

type ThemePalette struct {
	Name        string         `json:"name"`
	Primary     lipgloss.Color `json:"primary"`
	Secondary   lipgloss.Color `json:"secondary"`
	BgDark      lipgloss.Color `json:"bg_dark"`
	BorderColor lipgloss.Color `json:"border_color"`
	TextMain    lipgloss.Color `json:"text_main"`
	TextMuted   lipgloss.Color `json:"text_muted"`
	BadgeBg     lipgloss.Color `json:"badge_bg"`
}

var (
	ThemeAmber = ThemePalette{
		Name:        "amber",
		Primary:     lipgloss.Color("#FF9E3B"),
		Secondary:   lipgloss.Color("#00FF88"),
		BgDark:      lipgloss.Color("#18181B"),
		BorderColor: lipgloss.Color("#FF9E3B"),
		TextMain:    lipgloss.Color("#F4F4F5"),
		TextMuted:   lipgloss.Color("#71717A"),
		BadgeBg:     lipgloss.Color("#27272A"),
	}
	ThemeEmerald = ThemePalette{
		Name:        "emerald",
		Primary:     lipgloss.Color("#00FF88"),
		Secondary:   lipgloss.Color("#05FFA1"),
		BgDark:      lipgloss.Color("#0A160F"),
		BorderColor: lipgloss.Color("#00FF88"),
		TextMain:    lipgloss.Color("#E8FFE8"),
		TextMuted:   lipgloss.Color("#3A6B4E"),
		BadgeBg:     lipgloss.Color("#12261A"),
	}
	ThemeCyber = ThemePalette{
		Name:        "cyber",
		Primary:     lipgloss.Color("#00F0FF"),
		Secondary:   lipgloss.Color("#FF007F"),
		BgDark:      lipgloss.Color("#0E0B16"),
		BorderColor: lipgloss.Color("#00F0FF"),
		TextMain:    lipgloss.Color("#FFFFFF"),
		TextMuted:   lipgloss.Color("#7B7291"),
		BadgeBg:     lipgloss.Color("#1F1A2E"),
	}
	ThemeMono = ThemePalette{
		Name:        "mono",
		Primary:     lipgloss.Color("#FFFFFF"),
		Secondary:   lipgloss.Color("#A1A1AA"),
		BgDark:      lipgloss.Color("#09090B"),
		BorderColor: lipgloss.Color("#71717A"),
		TextMain:    lipgloss.Color("#FAFAFA"),
		TextMuted:   lipgloss.Color("#52525B"),
		BadgeBg:     lipgloss.Color("#27272A"),
	}
)

func getThemeByName(name string) (ThemePalette, bool) {
	switch strings.ToLower(strings.TrimSpace(name)) {
	case "amber":
		return ThemeAmber, true
	case "emerald":
		return ThemeEmerald, true
	case "cyber":
		return ThemeCyber, true
	case "mono":
		return ThemeMono, true
	default:
		return ThemeAmber, false
	}
}

const defaultAsciiM = `
 ███╗   ███╗
 ████╗ ████║
 ██╔████╔██║
 ██║╚██╔╝██║
 ██║ ╚═╝ ██║
 ╚═╝     ╚═╝`

const defaultAsciiT = `
 ████████╗
 ╚══██╔══╝
    ██║   
    ██║   
    ██║   
    ╚═╝   `

// ============================================================================
// 3. SÜPER KULLANICI PİKSEL KANCA KATMANI
// ============================================================================

type DynamicPixelHook func(fb *VirtualFramebuffer, width, height int)

type SuperuserHookManager struct {
	mu         sync.RWMutex
	textHooks  map[string]string
	pixelHooks map[string]DynamicPixelHook
}

func NewSuperuserHookManager() *SuperuserHookManager {
	return &SuperuserHookManager{
		textHooks:  make(map[string]string),
		pixelHooks: make(map[string]DynamicPixelHook),
	}
}

func (shm *SuperuserHookManager) SetTextHook(target, content string) {
	shm.mu.Lock()
	defer shm.mu.Unlock()
	shm.textHooks[target] = content
}

func (shm *SuperuserHookManager) ClearTextHook(target string) {
	shm.mu.Lock()
	defer shm.mu.Unlock()
	delete(shm.textHooks, target)
}

func (shm *SuperuserHookManager) GetTextHook(target, fallback string) string {
	shm.mu.RLock()
	defer shm.mu.RUnlock()
	if c, ok := shm.textHooks[target]; ok && c != "" {
		return c
	}
	return fallback
}

func (shm *SuperuserHookManager) RegisterPixelHook(id string, hook DynamicPixelHook) {
	shm.mu.Lock()
	defer shm.mu.Unlock()
	shm.pixelHooks[id] = hook
}

func (shm *SuperuserHookManager) RemovePixelHook(id string) {
	shm.mu.Lock()
	defer shm.mu.Unlock()
	delete(shm.pixelHooks, id)
}

func (shm *SuperuserHookManager) HasPixelHooks() bool {
	shm.mu.RLock()
	defer shm.mu.RUnlock()
	return len(shm.pixelHooks) > 0
}

func (shm *SuperuserHookManager) ExecutePixelPipelines(fb *VirtualFramebuffer) {
	shm.mu.RLock()
	hooks := make([]DynamicPixelHook, 0, len(shm.pixelHooks))
	for _, h := range shm.pixelHooks {
		if h != nil {
			hooks = append(hooks, h)
		}
	}
	shm.mu.RUnlock()

	for _, hook := range hooks {
		hook(fb, fb.Width, fb.Height)
	}
}

// ============================================================================
// 4. KAPSAMLI DİZİN VE KALICI AYAR YÖNETİMİ
// ============================================================================

type PersistentConfig struct {
	Theme   string   `json:"theme"`
	History []string `json:"history"`
}

func getBaseDir() string {
	candidates := []string{"plugins", "./plugins"}

	if execPath, err := os.Executable(); err == nil {
		execDir := filepath.Dir(execPath)
		candidates = append(candidates, filepath.Join(execDir, "plugins"))
	}

	for _, c := range candidates {
		if info, err := os.Stat(c); err == nil && info.IsDir() {
			absP, _ := filepath.Abs(filepath.Dir(c))
			return absP
		}
	}

	userConfig, err := os.UserConfigDir()
	if err == nil {
		dir := filepath.Join(userConfig, "mt")
		_ = os.MkdirAll(filepath.Join(dir, "plugins"), 0755)
		return dir
	}

	_ = os.MkdirAll("plugins", 0755)
	absCur, _ := filepath.Abs(".")
	return absCur
}

func getPluginsDir() string {
	p := filepath.Join(getBaseDir(), "plugins")
	_ = os.MkdirAll(p, 0755)
	absP, _ := filepath.Abs(p)
	return absP
}

func getBinDir() string {
	b := filepath.Join(getBaseDir(), ".mt_bin")
	_ = os.MkdirAll(b, 0755)
	absB, _ := filepath.Abs(b)
	return absB
}

func getConfigPath() string {
	return filepath.Join(getBaseDir(), "config.json")
}

func loadConfig() PersistentConfig {
	cfg := PersistentConfig{Theme: "amber", History: []string{}}
	data, err := os.ReadFile(getConfigPath())
	if err == nil {
		_ = json.Unmarshal(data, &cfg)
	}
	if cfg.History == nil {
		cfg.History = []string{}
	}
	if _, ok := getThemeByName(cfg.Theme); !ok {
		cfg.Theme = "amber"
	}
	return cfg
}

func saveConfig(cfg PersistentConfig) {
	data, err := json.MarshalIndent(cfg, "", "  ")
	if err != nil {
		return
	}
	target := getConfigPath()
	tmp := target + ".tmp"
	if err := os.WriteFile(tmp, data, 0644); err == nil {
		if err := os.Rename(tmp, target); err != nil {
			_ = os.Remove(target)
			_ = os.Rename(tmp, target)
		}
	}
}

type SharedStateStore struct {
	mu       sync.RWMutex
	data     map[string]string
	filePath string
}

func NewSharedStateStore(filePath string) *SharedStateStore {
	store := &SharedStateStore{
		data:     make(map[string]string),
		filePath: filePath,
	}
	store.load()
	return store
}

func (s *SharedStateStore) load() {
	s.mu.Lock()
	defer s.mu.Unlock()
	bytes, err := os.ReadFile(s.filePath)
	if err == nil {
		_ = json.Unmarshal(bytes, &s.data)
	}
}

func (s *SharedStateStore) save() {
	bytes, err := json.MarshalIndent(s.data, "", "  ")
	if err != nil {
		return
	}
	tmp := s.filePath + ".tmp"
	if err := os.WriteFile(tmp, bytes, 0644); err == nil {
		if err := os.Rename(tmp, s.filePath); err != nil {
			_ = os.Remove(s.filePath)
			_ = os.Rename(tmp, s.filePath)
		}
	}
}

func (s *SharedStateStore) Set(key, val string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.data[key] = val
	s.save()
}

func (s *SharedStateStore) Get(key string) (string, bool) {
	s.mu.RLock()
	defer s.mu.RUnlock()
	val, ok := s.data[key]
	return val, ok
}

func (s *SharedStateStore) ExportEnv() []string {
	s.mu.RLock()
	defer s.mu.RUnlock()
	var envs []string
	for k, v := range s.data {
		var b strings.Builder
		for _, r := range k {
			if (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z') || (r >= '0' && r <= '9') {
				b.WriteRune(r)
			} else {
				b.WriteRune('_')
			}
		}
		cleanKey := strings.ToUpper(b.String())
		if cleanKey != "" {
			envs = append(envs, fmt.Sprintf("MT_KV_%s=%s", cleanKey, v))
		}
	}
	sort.Strings(envs)
	return envs
}

// ============================================================================
// 5. MODAL, TOAST, IPC VE TUI DEVİR SÖZLEŞMELERİ
// ============================================================================

type Capability uint32

const (
	CapUI          Capability = 1 << 0
	CapDaemon      Capability = 1 << 1
	CapInterceptor Capability = 1 << 2
	CapOSProcess   Capability = 1 << 3
	CapSuperuser   Capability = 1 << 4
)

type HotReloadMsg struct {
	Count int
}

type NotifyMsg struct {
	Text    string
	IsError bool
}

type ToastMsg struct {
	ID      int64
	Text    string
	IsError bool
}

type ToastTriggerMsg struct {
	ID      int64
	Text    string
	IsError bool
}

type ToastClearMsg struct {
	ID int64
}

type ExternalTUIFinishedMsg struct {
	Err error
}

type ModalDialog struct {
	Title        string
	Content      string
	IsPrompt     bool
	IsConfirm    bool
	PromptPrompt string
	InputModel   *textinput.Model
	Callback     func(result string)
	OnConfirm    func(confirmed bool)
}

type CellMutation struct {
	X    int                    `json:"x"`
	Y    int                    `json:"y"`
	Char rune                   `json:"char"`
	Fg   lipgloss.TerminalColor `json:"fg"`
	Bg   lipgloss.TerminalColor `json:"bg"`
	Bold bool                   `json:"bold"`
}

type PendingTUIRequest struct {
	Binary string
	Args   []string
	Name   string
}

type SuperuserHost interface {
	SendTUI(msg tea.Msg)
	ExecOS(name string, args ...string) (string, error)
	Notify(msg string, isError bool)
	Toast(text string, isError bool)
	OpenModal(title, content string)
	OpenPrompt(title, promptText string, onSubmit func(val string))
	OpenConfirm(title, message string, onConfirm func(confirmed bool))
	CloseModal()
	SetTheme(name string) bool
	SetCustomTheme(theme ThemePalette)
	CurrentTheme() ThemePalette
	ClipboardSet(text string)
	KV() *SharedStateStore

	MutatePixel(x, y int, ch rune, fg, bg lipgloss.TerminalColor, bold bool)
	MutatePixelBatch(pixels []CellMutation)
	DrawBox(x, y, w, h int, title string, borderFg lipgloss.TerminalColor, bold bool)
	ClearPixels()
	RegisterOverlay(id string, hook DynamicPixelHook)
	RemoveOverlay(id string)
	SetTextHook(target, content string)
	ClearTextHook(target string)
	SetPrompt(prefix, arrow string, fgPrefix, fgArrow lipgloss.TerminalColor)
	ResetPrompt()
	BindKey(key, command string)
	UnbindKey(key string)
	PatchCommand(targetCmd, rewriteCmd string)
	UnpatchCommand(targetCmd string)
	ForceCloseTab(tabIdx int) bool
	InjectTab(title, cmd, output string)
	UpdateTabOutput(tabIdx int, output string) bool
	SetRawScreenContent(rendered string)
	HijackInputFocus(active bool)
	GetTerminalDimensions() (width, height int)
	ExecuteIPCAction(actionJSON string) string

	// YENİ: Eklenti TUI Yönlendirmesi (Onaylı & Geri Dönüş Garantili)
	RequestExternalTUI(binary string, args []string, name string, confirmMsg string)
}

type Manifest struct {
	Command      string
	Title        string
	Category     string
	Description  string
	Capabilities Capability
}

type PluginContext struct {
	Width      int
	Height     int
	InvokedCmd string
	Args       []string
	RawArgs    string
	PipeInput  string
	Theme      ThemePalette
	Host       SuperuserHost
}

type LowLevelPlugin interface {
	Manifests() []Manifest
	Init(host SuperuserHost) error
	StartDaemon(ctx context.Context, host SuperuserHost)
	Intercept(rawCmd string) (proceed bool, modifiedCmd string)
	Update(msg tea.Msg, ctx *PluginContext) (consumed bool, cmd tea.Cmd)
	View(ctx *PluginContext) string
	Destroy() error
}

type TabRenderFunc func(theme ThemePalette, width, height int) string

type WorkspaceTab struct {
	ID       int
	Command  string
	Title    string
	Output   string
	Duration time.Duration
	Viewport viewport.Model
	RenderFn TabRenderFunc
}

func NewWorkspaceTab(id int, cmd, title, output string, renderFn TabRenderFunc, dur time.Duration, width, height int) WorkspaceTab {
	vpW := width
	vpH := height
	if vpW < 10 {
		vpW = 10
	}
	if vpH < 3 {
		vpH = 3
	}
	vp := viewport.New(vpW, vpH)
	vp.SetContent(strings.TrimRight(output, "\r\n"))
	vp.GotoTop()
	return WorkspaceTab{
		ID:       id,
		Command:  cmd,
		Title:    title,
		Output:   output,
		Duration: dur,
		Viewport: vp,
		RenderFn: renderFn,
	}
}

// ============================================================================
// 6. POLİGLOT (GO, PYTHON, SHELL, BINARY) & DAEMON EKLENTİ MOTORU
// ============================================================================

type PluginType int

const (
	PluginTypeGoSource PluginType = iota
	PluginTypePython
	PluginTypeShell
	PluginTypeBinary
)

type DynamicModule struct {
	mu           sync.Mutex
	pluginType   PluginType
	sourcePath   string
	execPath     string
	lastMod      time.Time
	manifests    []Manifest
	host         SuperuserHost
	isDaemon     bool
	daemonCtx    context.Context
	cancelDaemon context.CancelFunc
}

func ParseDynamicModule(filePath string) (*DynamicModule, error) {
	absPath, err := filepath.Abs(filePath)
	if err != nil {
		return nil, err
	}

	info, err := os.Stat(absPath)
	if err != nil {
		return nil, err
	}

	baseName := filepath.Base(absPath)
	var pType PluginType
	var cmdBaseName string

	switch {
	case strings.HasSuffix(baseName, ".go"):
		pType = PluginTypeGoSource
		cmdBaseName = strings.TrimSuffix(baseName, ".go")
	case strings.HasSuffix(baseName, ".py"):
		pType = PluginTypePython
		cmdBaseName = strings.TrimSuffix(baseName, ".py")
	case strings.HasSuffix(baseName, ".sh"):
		pType = PluginTypeShell
		cmdBaseName = strings.TrimSuffix(baseName, ".sh")
	default:
		pType = PluginTypeBinary
		cmdBaseName = strings.TrimSuffix(baseName, ".exe")
	}

	var manifests []Manifest
	manifestMap := make(map[string]bool)

	addManifest := func(m Manifest) {
		cmdClean := strings.ToLower(strings.TrimSpace(m.Command))
		if cmdClean == "" || manifestMap[cmdClean] {
			return
		}
		manifestMap[cmdClean] = true
		m.Command = cmdClean
		manifests = append(manifests, m)
	}

	var singleCmd, defaultTitle, defaultCategory, defaultDesc string
	isDaemon := false

	if pType != PluginTypeBinary {
		if file, err := os.Open(absPath); err == nil {
			scanner := bufio.NewScanner(file)
			lineCount := 0
			for scanner.Scan() && lineCount < 100 {
				line := strings.TrimSpace(scanner.Text())
				lineCount++

				cleanLine := ""
				if strings.HasPrefix(line, "//") {
					cleanLine = strings.TrimSpace(strings.TrimPrefix(line, "//"))
				} else if strings.HasPrefix(line, "#") {
					cleanLine = strings.TrimSpace(strings.TrimPrefix(line, "#"))
				}

				if strings.HasPrefix(cleanLine, "@cmd:") {
					raw := strings.TrimPrefix(cleanLine, "@cmd:")
					parts := strings.Split(raw, ":")
					if len(parts) >= 4 {
						addManifest(Manifest{
							Command:      parts[0],
							Title:        strings.TrimSpace(parts[1]),
							Category:     strings.ToUpper(strings.TrimSpace(parts[2])),
							Description:  strings.TrimSpace(parts[3]),
							Capabilities: CapUI | CapSuperuser,
						})
					}
				} else if strings.HasPrefix(cleanLine, "@command:") {
					singleCmd = strings.TrimSpace(strings.TrimPrefix(cleanLine, "@command:"))
				} else if strings.HasPrefix(cleanLine, "@title:") {
					defaultTitle = strings.TrimSpace(strings.TrimPrefix(cleanLine, "@title:"))
				} else if strings.HasPrefix(cleanLine, "@category:") {
					defaultCategory = strings.ToUpper(strings.TrimSpace(strings.TrimPrefix(cleanLine, "@category:")))
				} else if strings.HasPrefix(cleanLine, "@desc:") {
					defaultDesc = strings.TrimSpace(strings.TrimPrefix(cleanLine, "@desc:"))
				} else if strings.HasPrefix(cleanLine, "@daemon:") {
					val := strings.ToLower(strings.TrimSpace(strings.TrimPrefix(cleanLine, "@daemon:")))
					isDaemon = (val == "true" || val == "1")
				}
			}
			file.Close()
		}
	}

	if singleCmd != "" {
		if defaultTitle == "" {
			defaultTitle = strings.ToUpper(singleCmd)
		}
		if defaultCategory == "" {
			defaultCategory = "RING-0"
		}
		addManifest(Manifest{
			Command:      singleCmd,
			Title:        defaultTitle,
			Category:     defaultCategory,
			Description:  defaultDesc,
			Capabilities: CapUI | CapSuperuser,
		})
	}

	if len(manifests) == 0 {
		addManifest(Manifest{
			Command:      cmdBaseName,
			Title:        strings.ToUpper(cmdBaseName),
			Category:     "RING-0",
			Description:  fmt.Sprintf("Süper kullanıcı dinamik modülü (%s)", cmdBaseName),
			Capabilities: CapUI | CapSuperuser,
		})
	}

	execPath := absPath
	if pType == PluginTypeGoSource {
		binName := cmdBaseName
		if runtime.GOOS == "windows" {
			binName += ".exe"
		}
		execPath = filepath.Join(getBinDir(), binName)
	}

	return &DynamicModule{
		pluginType: pType,
		sourcePath: absPath,
		execPath:   execPath,
		lastMod:    info.ModTime(),
		manifests:  manifests,
		isDaemon:   isDaemon,
	}, nil
}

func (dm *DynamicModule) Manifests() []Manifest { return dm.manifests }
func (dm *DynamicModule) Init(h SuperuserHost) error {
	dm.host = h
	if dm.isDaemon {
		ctx, cancel := context.WithCancel(context.Background())
		dm.daemonCtx = ctx
		dm.cancelDaemon = cancel
		dm.StartDaemon(ctx, h)
	}
	return nil
}

func (dm *DynamicModule) StartDaemon(ctx context.Context, host SuperuserHost) {
	go func() {
		for {
			select {
			case <-ctx.Done():
				return
			default:
				if err := dm.ensureExecutable(); err != nil {
					time.Sleep(3 * time.Second)
					continue
				}

				var cmd *exec.Cmd
				switch dm.pluginType {
				case PluginTypePython:
					pyExec := "python3"
					if _, err := exec.LookPath(pyExec); err != nil {
						pyExec = "python"
					}
					cmd = exec.CommandContext(ctx, pyExec, dm.sourcePath, "--daemon")
				case PluginTypeShell:
					shExec := "bash"
					if _, err := exec.LookPath(shExec); err != nil {
						shExec = "sh"
					}
					cmd = exec.CommandContext(ctx, shExec, dm.sourcePath, "--daemon")
				default:
					cmd = exec.CommandContext(ctx, dm.execPath, "--daemon")
				}

				w, h := host.GetTerminalDimensions()
				cmd.Env = append(os.Environ(),
					"MT_DAEMON=1",
					"MT_SUPERUSER=1",
					fmt.Sprintf("MT_WIDTH=%d", w),
					fmt.Sprintf("MT_HEIGHT=%d", h),
					fmt.Sprintf("MT_THEME=%s", host.CurrentTheme().Name),
					fmt.Sprintf("MT_PLUGINS_DIR=%s", getPluginsDir()),
				)
				cmd.Env = append(cmd.Env, host.KV().ExportEnv()...)

				stdout, err := cmd.StdoutPipe()
				if err != nil {
					time.Sleep(2 * time.Second)
					continue
				}

				if err := cmd.Start(); err != nil {
					time.Sleep(2 * time.Second)
					continue
				}

				scanner := bufio.NewScanner(stdout)
				for scanner.Scan() {
					line := strings.TrimSpace(scanner.Text())
					if line != "" {
						host.ExecuteIPCAction(line)
					}
				}

				_ = cmd.Wait()
				time.Sleep(1 * time.Second)
			}
		}
	}()
}

func (dm *DynamicModule) Intercept(c string) (bool, string)                 { return true, c }
func (dm *DynamicModule) Update(msg tea.Msg, ctx *PluginContext) (bool, tea.Cmd) {
	return false, nil
}

func (dm *DynamicModule) Destroy() error {
	dm.mu.Lock()
	defer dm.mu.Unlock()
	if dm.cancelDaemon != nil {
		dm.cancelDaemon()
	}
	return nil
}

func (dm *DynamicModule) ensureExecutable() error {
	dm.mu.Lock()
	defer dm.mu.Unlock()

	srcInfo, err := os.Stat(dm.sourcePath)
	if err != nil {
		return fmt.Errorf("kaynak dosya okunamadı: %w", err)
	}

	switch dm.pluginType {
	case PluginTypeGoSource:
		binInfo, binErr := os.Stat(dm.execPath)
		needsBuild := binErr != nil || srcInfo.ModTime().After(binInfo.ModTime())

		if needsBuild {
			_ = os.MkdirAll(filepath.Dir(dm.execPath), 0755)
			cmd := exec.Command("go", "build", "-o", dm.execPath, dm.sourcePath)
			output, buildErr := cmd.CombinedOutput()
			if buildErr != nil {
				return fmt.Errorf("derleme hatası:\n%s", string(output))
			}
		}

	case PluginTypeShell, PluginTypeBinary:
		if runtime.GOOS != "windows" {
			if srcInfo.Mode().Perm()&0111 == 0 {
				_ = os.Chmod(dm.sourcePath, 0755)
			}
		}
	}

	return nil
}

func (dm *DynamicModule) View(ctx *PluginContext) (outView string) {
	defer func() {
		if r := recover(); r != nil {
			outView = fmt.Sprintf("⚠️ Eklenti yürütme hatası (Panic zırhı): %v", r)
		}
	}()

	if err := dm.ensureExecutable(); err != nil {
		return fmt.Sprintf("⚠️ SİSTEM ÇALIŞTIRMA HATASI:\n%v", err)
	}

	execCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	var cmd *exec.Cmd
	switch dm.pluginType {
	case PluginTypePython:
		pyExec := "python3"
		if _, err := exec.LookPath(pyExec); err != nil {
			pyExec = "python"
		}
		cmdArgs := append([]string{dm.sourcePath}, ctx.Args...)
		cmd = exec.CommandContext(execCtx, pyExec, cmdArgs...)
	case PluginTypeShell:
		shExec := "bash"
		if _, err := exec.LookPath(shExec); err != nil {
			shExec = "sh"
		}
		cmdArgs := append([]string{dm.sourcePath}, ctx.Args...)
		cmd = exec.CommandContext(execCtx, shExec, cmdArgs...)
	default:
		cmd = exec.CommandContext(execCtx, dm.execPath, ctx.Args...)
	}

	if ctx.PipeInput != "" {
		cmd.Stdin = strings.NewReader(ctx.PipeInput)
	}

	pipeSnippet := ctx.PipeInput
	if len(pipeSnippet) > 1024 {
		pipeSnippet = pipeSnippet[:1024]
	}

	w, h := ctx.Host.GetTerminalDimensions()

	cmd.Env = append(os.Environ(),
		fmt.Sprintf("MT_INVOKED_CMD=%s", ctx.InvokedCmd),
		fmt.Sprintf("MT_PIPE_INPUT=%s", pipeSnippet),
		fmt.Sprintf("MT_WIDTH=%d", w),
		fmt.Sprintf("MT_HEIGHT=%d", h),
		"MT_SUPERUSER=1",
		fmt.Sprintf("MT_THEME=%s", ctx.Theme.Name),
		fmt.Sprintf("MT_PLUGINS_DIR=%s", getPluginsDir()),
	)
	cmd.Env = append(cmd.Env, ctx.Host.KV().ExportEnv()...)

	output, err := cmd.CombinedOutput()
	if execCtx.Err() == context.DeadlineExceeded {
		return "⚠️ Hata: Eklenti zaman aşımına uğradı (10 saniye sınırı)."
	}
	if err != nil {
		return fmt.Sprintf("⚠️ Yürütme Hatası: %v\n\nÇıktı:\n%s", err, string(output))
	}

	// Güvenli Satır Satır IPC Ayrıştırıcı (Metin + JSON karışıklığını çözer)
	var textOutput strings.Builder
	var lastActionFeedback string
	scanner := bufio.NewScanner(strings.NewReader(string(output)))
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if strings.HasPrefix(line, "{") && strings.HasSuffix(line, "}") {
			res := ctx.Host.ExecuteIPCAction(line)
			if res != "" {
				lastActionFeedback = res
			}
		} else {
			textOutput.WriteString(line + "\n")
		}
	}

	plainText := strings.TrimSpace(textOutput.String())
	if plainText != "" {
		return plainText
	}
	if lastActionFeedback != "" {
		return lastActionFeedback
	}
	return strings.TrimSpace(string(output))
}

// ============================================================================
// 7. KERNEL ENGINE
// ============================================================================

type KernelEngine struct {
	mu           sync.RWMutex
	builtins     []LowLevelPlugin
	dynamicMods  map[string]*DynamicModule
	patchedCmds  map[string]string
	interceptors []LowLevelPlugin
	host         SuperuserHost
}

func NewKernelEngine(host SuperuserHost) *KernelEngine {
	return &KernelEngine{
		dynamicMods: make(map[string]*DynamicModule),
		patchedCmds: make(map[string]string),
		host:        host,
	}
}

func (ke *KernelEngine) RegisterBuiltin(p LowLevelPlugin) error {
	ke.mu.Lock()
	defer ke.mu.Unlock()

	if err := p.Init(ke.host); err != nil {
		return err
	}
	ke.builtins = append(ke.builtins, p)

	for _, m := range p.Manifests() {
		if m.Capabilities&CapInterceptor != 0 {
			ke.interceptors = append(ke.interceptors, p)
		}
	}
	return nil
}

func (ke *KernelEngine) PatchCommand(targetCmd, rewriteCmd string) {
	ke.mu.Lock()
	defer ke.mu.Unlock()
	ke.patchedCmds[strings.ToLower(strings.TrimSpace(targetCmd))] = rewriteCmd
}

func (ke *KernelEngine) UnpatchCommand(targetCmd string) {
	ke.mu.Lock()
	defer ke.mu.Unlock()
	delete(ke.patchedCmds, strings.ToLower(strings.TrimSpace(targetCmd)))
}

func (ke *KernelEngine) CheckAndReload(dirPath string) (bool, int) {
	absDir, err := filepath.Abs(dirPath)
	if err != nil {
		absDir = dirPath
	}

	_ = os.MkdirAll(absDir, 0755)
	entries, err := os.ReadDir(absDir)
	if err != nil {
		return false, 0
	}

	type candidateInfo struct {
		path    string
		modTime time.Time
	}
	var candidates []candidateInfo
	currentFiles := make(map[string]bool)

	for _, entry := range entries {
		if entry.IsDir() {
			continue
		}
		name := entry.Name()
		if strings.HasPrefix(name, ".") {
			continue
		}

		fullPath := filepath.Join(absDir, name)
		info, err := entry.Info()
		if err != nil {
			continue
		}

		// Sadece betik ve çalıştırılabilir dosyaları filtrele (md, txt gibi çöpleri ayıkla)
		isCandidate := strings.HasSuffix(name, ".go") ||
			strings.HasSuffix(name, ".py") ||
			strings.HasSuffix(name, ".sh") ||
			(info.Mode().Perm()&0111 != 0 && runtime.GOOS != "windows") ||
			(strings.HasSuffix(name, ".exe") && runtime.GOOS == "windows")

		if isCandidate {
			currentFiles[fullPath] = true
			candidates = append(candidates, candidateInfo{path: fullPath, modTime: info.ModTime()})
		}
	}

	var toUpdate []*DynamicModule
	for _, c := range candidates {
		ke.mu.RLock()
		existing, exists := ke.dynamicMods[c.path]
		needReload := !exists || c.modTime.After(existing.lastMod)
		ke.mu.RUnlock()

		if needReload {
			if mod, err := ParseDynamicModule(c.path); err == nil {
				_ = mod.Init(ke.host)
				toUpdate = append(toUpdate, mod)
			}
		}
	}

	ke.mu.Lock()
	defer ke.mu.Unlock()

	changed := false
	for _, mod := range toUpdate {
		if existing, exists := ke.dynamicMods[mod.sourcePath]; exists && existing != nil {
			_ = existing.Destroy()
		}
		ke.dynamicMods[mod.sourcePath] = mod
		changed = true
	}

	for path, mod := range ke.dynamicMods {
		if !currentFiles[path] {
			if mod != nil {
				_ = mod.Destroy()
			}
			delete(ke.dynamicMods, path)
			changed = true
		}
	}

	return changed, len(ke.dynamicMods)
}

func (ke *KernelEngine) FilterCommand(input string) (bool, string) {
	ke.mu.RLock()
	defer ke.mu.RUnlock()

	current := input
	cleanCmd := strings.ToLower(strings.TrimPrefix(strings.Split(strings.TrimSpace(current), " ")[0], "/"))
	if rewrite, ok := ke.patchedCmds[cleanCmd]; ok && rewrite != "" {
		parts := strings.SplitN(strings.TrimSpace(current), " ", 2)
		if len(parts) > 1 {
			current = "/" + rewrite + " " + parts[1]
		} else {
			current = "/" + rewrite
		}
	}

	for _, it := range ke.interceptors {
		proceed, modified := it.Intercept(current)
		if !proceed {
			return false, ""
		}
		current = modified
	}
	return true, current
}

func (ke *KernelEngine) Resolve(cmd string) (LowLevelPlugin, bool) {
	ke.mu.RLock()
	defer ke.mu.RUnlock()

	target := strings.ToLower(cmd)
	var paths []string
	for p := range ke.dynamicMods {
		paths = append(paths, p)
	}
	sort.Strings(paths)

	for _, p := range paths {
		dm := ke.dynamicMods[p]
		for _, m := range dm.Manifests() {
			if strings.ToLower(m.Command) == target {
				return dm, true
			}
		}
	}

	for _, b := range ke.builtins {
		for _, m := range b.Manifests() {
			if strings.ToLower(m.Command) == target {
				return b, true
			}
		}
	}

	return nil, false
}

func (ke *KernelEngine) Search(rawQuery string) []Manifest {
	ke.mu.RLock()
	defer ke.mu.RUnlock()

	clean := strings.TrimSpace(rawQuery)
	seen := make(map[string]bool)
	var res []Manifest

	q := strings.ToLower(strings.TrimPrefix(clean, "/"))

	addIfMatches := func(m Manifest) {
		cmdKey := strings.ToLower(m.Command)
		if seen[cmdKey] {
			return
		}
		if q == "" || strings.Contains(cmdKey, q) ||
			strings.Contains(strings.ToLower(m.Description), q) ||
			strings.Contains(strings.ToLower(m.Category), q) {
			seen[cmdKey] = true
			res = append(res, m)
		}
	}

	for _, b := range ke.builtins {
		for _, m := range b.Manifests() {
			addIfMatches(m)
		}
	}

	for _, dm := range ke.dynamicMods {
		for _, m := range dm.Manifests() {
			addIfMatches(m)
		}
	}

	sort.SliceStable(res, func(i, j int) bool {
		return res[i].Command < res[j].Command
	})

	return res
}

func (ke *KernelEngine) Shutdown() {
	ke.mu.Lock()
	defer ke.mu.Unlock()
	for _, b := range ke.builtins {
		_ = b.Destroy()
	}
	for _, dm := range ke.dynamicMods {
		_ = dm.Destroy()
	}
}

// ============================================================================
// 8. RING-0 DAHİLİ SİSTEMLER & HARİCİ TUI KÖPRÜSÜ
// ============================================================================

type TuiHandoverPlugin struct{}

func (t *TuiHandoverPlugin) Manifests() []Manifest {
	return []Manifest{
		{Command: "tui", Title: "HARİCİ TUI ÇALIŞTIRICI", Category: "RING-0", Description: "Harici interaktif TUI programını onay sorarak güvenle başlatır (/tui htop)", Capabilities: CapUI | CapSuperuser},
	}
}
func (t *TuiHandoverPlugin) Init(h SuperuserHost) error                        { return nil }
func (t *TuiHandoverPlugin) Destroy() error                                   { return nil }
func (t *TuiHandoverPlugin) StartDaemon(ctx context.Context, host SuperuserHost) {}
func (t *TuiHandoverPlugin) Intercept(c string) (bool, string)                 { return true, c }
func (t *TuiHandoverPlugin) Update(msg tea.Msg, ctx *PluginContext) (bool, tea.Cmd) {
	return false, nil
}
func (t *TuiHandoverPlugin) View(ctx *PluginContext) string {
	if len(ctx.Args) == 0 {
		return "Kullanım: /tui <program_veya_eklenti> [parametreler]\nÖrnek:\n  /tui htop\n  /tui nano dosya.txt\n  /tui python3 my_curses_app.py"
	}
	binary := ctx.Args[0]
	args := ctx.Args[1:]
	ctx.Host.RequestExternalTUI(binary, args, binary, "")
	return fmt.Sprintf("⏳ Harici TUI başlatma isteği gönderildi: [%s] (Onay bekleniyor)", binary)
}

type ShellPlugin struct{}

func (sp *ShellPlugin) Manifests() []Manifest {
	return []Manifest{
		{Command: "sh", Title: "KABUK SÜRÜCÜSÜ", Category: "OS", Description: "Doğrudan işletim sistemi komutu yürütür (/sh ls)", Capabilities: CapUI | CapOSProcess},
		{Command: "grep", Title: "METİN FİLTRESİ", Category: "TOOL", Description: "Girdiyi satır satır filtreler (Pipelining)", Capabilities: CapUI},
	}
}
func (sp *ShellPlugin) Init(h SuperuserHost) error                        { return nil }
func (sp *ShellPlugin) Destroy() error                                   { return nil }
func (sp *ShellPlugin) StartDaemon(ctx context.Context, host SuperuserHost) {}
func (sp *ShellPlugin) Intercept(c string) (bool, string)                 { return true, c }
func (sp *ShellPlugin) Update(msg tea.Msg, ctx *PluginContext) (bool, tea.Cmd) {
	return false, nil
}

// FIX: İnteraktif TUI komutlarını otomatik tespit edip terminal devir onayına yönlendirir
func (sp *ShellPlugin) View(ctx *PluginContext) (outStr string) {
	defer func() {
		if r := recover(); r != nil {
			outStr = fmt.Sprintf("⚠️ Kabuk yürütme hatası (Panic zırhı): %v", r)
		}
	}()

	if ctx.InvokedCmd == "grep" {
		if len(ctx.Args) == 0 {
			return "Kullanım: /cmd | grep [-i] <kelime>"
		}
		caseInsensitive := false
		target := ""
		for _, arg := range ctx.Args {
			if arg == "-i" {
				caseInsensitive = true
			} else if target == "" {
				target = arg
			}
		}
		if target == "" {
			return "Kullanım: /cmd | grep [-i] <kelime>"
		}
		var matched []string
		scanner := bufio.NewScanner(strings.NewReader(ctx.PipeInput))
		searchTarget := target
		if caseInsensitive {
			searchTarget = strings.ToLower(target)
		}
		for scanner.Scan() {
			line := scanner.Text()
			checkLine := line
			if caseInsensitive {
				checkLine = strings.ToLower(line)
			}
			if strings.Contains(checkLine, searchTarget) {
				matched = append(matched, line)
			}
		}
		if len(matched) == 0 {
			return fmt.Sprintf("'%s' ile eşleşen satır bulunamadı.", target)
		}
		return strings.Join(matched, "\n")
	}

	if len(ctx.Args) == 0 {
		return "Kullanım: /sh <komut> [parametreler]\nÖrnek: /sh uname -a veya /sh ls -la"
	}

	binary := ctx.Args[0]
	args := ctx.Args[1:]

	// İnteraktif TTY gerektiren komutlar için otomatik TUI koruması
	interactiveTools := map[string]bool{
		"htop": true, "top": true, "vim": true, "vi": true, "nano": true,
		"less": true, "more": true, "fzf": true, "lazygit": true, "tmux": true,
	}
	if interactiveTools[strings.ToLower(binary)] {
		ctx.Host.RequestExternalTUI(binary, args, binary, "")
		return fmt.Sprintf("⏳ İnteraktif araç algılandı: [%s]. Terminal devri için onay bekleniyor...", binary)
	}

	execCtx, cancel := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel()

	if _, err := exec.LookPath(binary); err != nil {
		if runtime.GOOS == "windows" {
			binary = "cmd.exe"
			args = append([]string{"/c", ctx.Args[0]}, ctx.Args[1:]...)
		} else {
			binary = "sh"
			fullCmd := strings.Join(ctx.Args, " ")
			args = []string{"-c", fullCmd}
		}
	}

	cmd := exec.CommandContext(execCtx, binary, args...)
	if ctx.PipeInput != "" {
		cmd.Stdin = strings.NewReader(ctx.PipeInput)
	}

	out, err := cmd.CombinedOutput()
	if execCtx.Err() == context.DeadlineExceeded {
		return "⚠️ Hata: Komut zaman aşımına uğradı (15 saniye sınırı)."
	}
	if err != nil {
		return fmt.Sprintf("⚠️ Komut Hatası: %v\n\nÇıktı:\n%s", err, string(out))
	}
	return strings.TrimSpace(string(out))
}

type SysDaemonPlugin struct{}

func (s *SysDaemonPlugin) Manifests() []Manifest {
	return []Manifest{
		{Command: "sys", Title: "SİSTEM TELEMETRİSİ", Category: "SYS", Description: "Canlı donanım durumu ve bellek ⚡", Capabilities: CapUI},
	}
}
func (s *SysDaemonPlugin) Init(h SuperuserHost) error             { return nil }
func (s *SysDaemonPlugin) Destroy() error                        { return nil }
func (s *SysDaemonPlugin) Intercept(c string) (bool, string)     { return true, c }
func (s *SysDaemonPlugin) StartDaemon(ctx context.Context, host SuperuserHost) {}
func (s *SysDaemonPlugin) Update(msg tea.Msg, ctx *PluginContext) (bool, tea.Cmd) {
	return false, nil
}
func (s *SysDaemonPlugin) View(ctx *PluginContext) string {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	if len(ctx.Args) > 0 {
		switch strings.ToLower(ctx.Args[0]) {
		case "cpu":
			return fmt.Sprintf("İşlemci: %d Threads | Mimari: %s/%s\nDurum: Nominal çalışma frekansı.", runtime.NumCPU(), runtime.GOOS, runtime.GOARCH)
		case "mem":
			return fmt.Sprintf("Tahsis Bellek: %.2f MB\nSistem Rezerv: %.2f MB\nGC Döngüsü   : %d kez tamamlandı", float64(m.Alloc)/1024/1024, float64(m.Sys)/1024/1024, m.NumGC)
		}
	}

	return fmt.Sprintf(
		"İşletim Sistemi  : %s / %s\n"+
			"CPU Thread       : %d Threads 🚀\n"+
			"Aktif Goroutines : %d Adet\n"+
			"Tahsis Bellek    : %.2f MB (Sistem: %.2f MB)\n"+
			"GC Frekansı      : %d döngü tamamlandı\n\n"+
			"● İpucu: /sys cpu veya /sys mem yazabilirsiniz.",
		runtime.GOOS, runtime.GOARCH, runtime.NumCPU(),
		runtime.NumGoroutine(), float64(m.Alloc)/1024/1024, float64(m.Sys)/1024/1024, m.NumGC,
	)
}

type ThemeSwitchPlugin struct{}

func (tp *ThemeSwitchPlugin) Manifests() []Manifest {
	return []Manifest{
		{Command: "theme", Title: "DİNAMİK RENK TEMASI", Category: "GUI", Description: "Temayı değiştirir (/theme cyber|emerald|amber|mono)", Capabilities: CapUI},
	}
}
func (tp *ThemeSwitchPlugin) Init(h SuperuserHost) error                        { return nil }
func (tp *ThemeSwitchPlugin) Destroy() error                                   { return nil }
func (tp *ThemeSwitchPlugin) StartDaemon(ctx context.Context, host SuperuserHost) {}
func (tp *ThemeSwitchPlugin) Intercept(c string) (bool, string)                 { return true, c }
func (tp *ThemeSwitchPlugin) Update(msg tea.Msg, ctx *PluginContext) (bool, tea.Cmd) {
	return false, nil
}
func (tp *ThemeSwitchPlugin) View(ctx *PluginContext) string {
	if len(ctx.Args) == 0 {
		return "Kullanım: /theme <amber | emerald | cyber | mono>\nÖrnek: /theme cyber"
	}
	target := strings.ToLower(ctx.Args[0])
	if ctx.Host.SetTheme(target) {
		ctx.Host.Toast(fmt.Sprintf("Tema '%s' yapıldı ve diske kaydedildi!", target), false)
		return fmt.Sprintf("Tema başarıyla '%s' olarak güncellendi.", target)
	}
	return fmt.Sprintf("Geçersiz tema: '%s'. Seçenekler: amber, emerald, cyber, mono", target)
}

type HelpCommand struct {
	kernel *KernelEngine
}

func (hc *HelpCommand) Manifests() []Manifest {
	return []Manifest{
		{Command: "help", Title: "SİSTEM KILAVUZU & KOMUT REHBERİ", Category: "CORE", Description: "Tüm sistem komutlarını ve modülleri listeler.", Capabilities: CapUI},
	}
}
func (hc *HelpCommand) Init(h SuperuserHost) error                        { return nil }
func (hc *HelpCommand) Destroy() error                                   { return nil }
func (hc *HelpCommand) StartDaemon(ctx context.Context, host SuperuserHost) {}
func (hc *HelpCommand) Intercept(c string) (bool, string)                 { return true, c }
func (hc *HelpCommand) Update(msg tea.Msg, ctx *PluginContext) (bool, tea.Cmd) {
	return false, nil
}
func (hc *HelpCommand) View(ctx *PluginContext) string {
	theme := ctx.Theme
	var b strings.Builder
	b.WriteString(lipgloss.NewStyle().Foreground(theme.Primary).Bold(true).Render("GELİŞMİŞ SİSTEM KOMUTLARI (ROOT / RING -1 AKTİF):\n\n"))

	for _, item := range hc.kernel.Search("") {
		catSpan := lipgloss.NewStyle().
			Width(8).
			Foreground(theme.TextMuted).
			Background(theme.BadgeBg).
			Padding(0, 1).
			Render(item.Category)

		nameSpan := lipgloss.NewStyle().
			Width(16).
			Foreground(theme.Secondary).
			Bold(true).
			Render("/" + item.Command)

		descSpan := lipgloss.NewStyle().
			Foreground(theme.TextMuted).
			Render(item.Description)

		row := lipgloss.JoinHorizontal(lipgloss.Left, catSpan, "  ", nameSpan, "  ", descSpan)
		b.WriteString(row + "\n")
	}

	b.WriteString("\n" + lipgloss.NewStyle().Foreground(theme.TextMuted).Render(
		fmt.Sprintf("Eklenti Dizini: %s\n", getPluginsDir())+
			"Klavye & Fare Yetenekleri:\n"+
			" • Alt+1 .. Alt+9    : Açık sekmeler arasında geçiş yapar.\n"+
			" • Alt+← / Alt+→     : Sekmeler arasında ileri/geri döner.\n"+
			" • Ctrl+W            : Aktif sekmeyi kapatır.\n"+
			" • Ctrl+Y            : Aktif sekme çıktısını panoya kopyalar.\n"+
			" • PgUp / PgDn / Çark: Çıktı alanını yukarı/aşağı kaydırır.\n"+
			" • /tui <cmd>        : Onaylı Harici TUI başlatıcı (Örn: /tui htop).",
	))
	return b.String()
}

type SimpleCmd struct {
	manifest Manifest
	viewFn   func() string
}

func (sc *SimpleCmd) Manifests() []Manifest { return []Manifest{sc.manifest} }
func (sc *SimpleCmd) Init(h SuperuserHost) error                        { return nil }
func (sc *SimpleCmd) Destroy() error                                   { return nil }
func (sc *SimpleCmd) StartDaemon(ctx context.Context, host SuperuserHost) {}
func (sc *SimpleCmd) Intercept(c string) (bool, string)                 { return true, c }
func (sc *SimpleCmd) Update(msg tea.Msg, ctx *PluginContext) (bool, tea.Cmd) {
	return false, nil
}
func (sc *SimpleCmd) View(ctx *PluginContext) string { return sc.viewFn() }

// ============================================================================
// 9. PIPELINE PARSER (BOŞ TIRNAK VE BOZULMA KORUMALI)
// ============================================================================

type PipelineStage struct {
	CmdName string
	Args    []string
	IsPiped bool
}

func tokenizeLine(line string) []string {
	var tokens []string
	var current strings.Builder
	inQuotes := false
	quoteChar := rune(0)
	escaped := false
	quoteEmitted := false

	runes := []rune(line)
	for i := 0; i < len(runes); i++ {
		r := runes[i]

		if escaped {
			current.WriteRune(r)
			escaped = false
			continue
		}

		if r == '\\' {
			escaped = true
			continue
		}

		if inQuotes {
			if r == quoteChar {
				inQuotes = false
				quoteChar = 0
				quoteEmitted = true
			} else {
				current.WriteRune(r)
			}
			continue
		}

		switch r {
		case '"', '\'':
			inQuotes = true
			quoteChar = r
		case '|':
			if current.Len() > 0 || quoteEmitted {
				tokens = append(tokens, current.String())
				current.Reset()
				quoteEmitted = false
			}
			tokens = append(tokens, "|")
		case ' ', '\t':
			if current.Len() > 0 || quoteEmitted {
				tokens = append(tokens, current.String())
				current.Reset()
				quoteEmitted = false
			}
		default:
			current.WriteRune(r)
		}
	}

	if current.Len() > 0 || quoteEmitted {
		tokens = append(tokens, current.String())
	}
	return tokens
}

func ParseExecutionLine(line string) []PipelineStage {
	tokens := tokenizeLine(strings.TrimSpace(line))
	if len(tokens) == 0 {
		return nil
	}

	var stages []PipelineStage
	var current *PipelineStage

	for _, token := range tokens {
		if token == "|" {
			if current != nil {
				stages = append(stages, *current)
				current = nil
			}
			continue
		}

		if current == nil {
			clean := strings.ToLower(strings.TrimPrefix(token, "/"))
			isPiped := len(stages) > 0
			current = &PipelineStage{
				CmdName: clean,
				Args:    []string{},
				IsPiped: isPiped,
			}
		} else {
			current.Args = append(current.Args, token)
		}
	}

	if current != nil {
		stages = append(stages, *current)
	}

	return stages
}

// ============================================================================
// 10. ÇEKİRDEK UYGULAMA MOTORU (SUPERUSER HOST / HYPERVISOR)
// ============================================================================

type PromptConfig struct {
	Prefix   string
	Arrow    string
	FgPrefix lipgloss.TerminalColor
	FgArrow  lipgloss.TerminalColor
}

type AppModel struct {
	input         textinput.Model
	kernel        *KernelEngine
	config        PersistentConfig
	program       *tea.Program
	theme         ThemePalette
	hookManager   *SuperuserHookManager
	store         *SharedStateStore
	tabs          []WorkspaceTab
	activeTab     int
	tabCounter    int
	hasWorkspace  bool
	width         int
	height        int
	statusMsg     string
	isError       bool
	selectedIndex int
	activeModal   *ModalDialog
	activeToast   *ToastMsg
	toastCounter  atomic.Int64
	historyIdx    int
	historyDraft  string
	lastInputVal  string
	watchCancel   context.CancelFunc

	promptCfg             PromptConfig
	keybindings           map[string]string
	keybindMu             sync.RWMutex
	overrideScreenContent string
	pixelMu               sync.RWMutex
	pixelOverrides        map[string]Cell
	inputHijacked         bool

	// YENİ: Harici TUI Devir Bekleme Nesnesi
	pendingTUI *PendingTUIRequest
}

func (m *AppModel) SendTUI(msg tea.Msg) {
	if m.program != nil {
		m.program.Send(msg)
	}
}

func (m *AppModel) ExecOS(name string, args ...string) (string, error) {
	cmd := exec.Command(name, args...)
	bytes, err := cmd.CombinedOutput()
	return string(bytes), err
}

func (m *AppModel) Notify(msg string, isError bool) {
	m.SendTUI(NotifyMsg{Text: msg, IsError: isError})
}

func (m *AppModel) Toast(text string, isError bool) {
	id := m.toastCounter.Add(1)
	m.SendTUI(ToastTriggerMsg{
		ID:      id,
		Text:    text,
		IsError: isError,
	})
}

func (m *AppModel) OpenModal(title, content string) {
	m.activeModal = &ModalDialog{
		Title:   title,
		Content: content,
	}
}

func (m *AppModel) OpenPrompt(title, promptText string, onSubmit func(val string)) {
	ti := textinput.New()
	ti.Placeholder = "metin girin..."
	ti.Focus()
	ti.CharLimit = 80
	ti.Width = 36
	m.activeModal = &ModalDialog{
		Title:        title,
		Content:      promptText,
		IsPrompt:     true,
		PromptPrompt: promptText,
		InputModel:   &ti,
		Callback:     onSubmit,
	}
}

func (m *AppModel) OpenConfirm(title, message string, onConfirm func(confirmed bool)) {
	m.activeModal = &ModalDialog{
		Title:     title,
		Content:   message,
		IsConfirm: true,
		OnConfirm: onConfirm,
	}
}

func (m *AppModel) CloseModal() {
	m.activeModal = nil
	m.input.Focus()
}

func (m *AppModel) SetTheme(name string) bool {
	t, ok := getThemeByName(name)
	if !ok {
		return false
	}
	m.theme = t
	m.config.Theme = t.Name
	saveConfig(m.config)

	for i := range m.tabs {
		if m.tabs[i].RenderFn != nil {
			m.tabs[i].Output = m.tabs[i].RenderFn(m.theme, m.tabs[i].Viewport.Width, m.tabs[i].Viewport.Height)
			m.tabs[i].Viewport.SetContent(m.tabs[i].Output)
			m.tabs[i].Viewport.GotoTop()
		}
	}
	return true
}

func (m *AppModel) SetCustomTheme(theme ThemePalette) {
	m.theme = theme
	for i := range m.tabs {
		if m.tabs[i].RenderFn != nil {
			m.tabs[i].Output = m.tabs[i].RenderFn(m.theme, m.tabs[i].Viewport.Width, m.tabs[i].Viewport.Height)
			m.tabs[i].Viewport.SetContent(m.tabs[i].Output)
			m.tabs[i].Viewport.GotoTop()
		}
	}
}

func (m *AppModel) CurrentTheme() ThemePalette {
	return m.theme
}

func (m *AppModel) KV() *SharedStateStore {
	return m.store
}

func (m *AppModel) ClipboardSet(text string) {
	encoded := base64.StdEncoding.EncodeToString([]byte(text))
	fmt.Fprintf(os.Stderr, "\x1b]52;c;%s\x07", encoded)

	go func() {
		switch runtime.GOOS {
		case "darwin":
			if p, err := exec.LookPath("pbcopy"); err == nil {
				cmd := exec.Command(p)
				cmd.Stdin = strings.NewReader(text)
				_ = cmd.Run()
			}
		case "linux":
			if p, err := exec.LookPath("wl-copy"); err == nil {
				cmd := exec.Command(p)
				cmd.Stdin = strings.NewReader(text)
				_ = cmd.Run()
			} else if p, err := exec.LookPath("xclip"); err == nil {
				cmd := exec.Command(p, "-selection", "clipboard")
				cmd.Stdin = strings.NewReader(text)
				_ = cmd.Run()
			} else if p, err := exec.LookPath("xsel"); err == nil {
				cmd := exec.Command(p, "-b", "-i")
				cmd.Stdin = strings.NewReader(text)
				_ = cmd.Run()
			}
		case "windows":
			if p, err := exec.LookPath("powershell"); err == nil {
				cmd := exec.Command(p, "-NoProfile", "-Command", "$input | Set-Clipboard")
				cmd.Stdin = strings.NewReader(text)
				_ = cmd.Run()
			}
		}
	}()
}

func (m *AppModel) MutatePixel(x, y int, ch rune, fg, bg lipgloss.TerminalColor, bold bool) {
	key := fmt.Sprintf("%d:%d", x, y)
	m.pixelMu.Lock()
	m.pixelOverrides[key] = Cell{
		Char: ch,
		Fg:   fg,
		Bg:   bg,
		Bold: bold,
	}
	m.pixelMu.Unlock()
}

func (m *AppModel) MutatePixelBatch(pixels []CellMutation) {
	m.pixelMu.Lock()
	for _, p := range pixels {
		key := fmt.Sprintf("%d:%d", p.X, p.Y)
		m.pixelOverrides[key] = Cell{
			Char: p.Char,
			Fg:   p.Fg,
			Bg:   p.Bg,
			Bold: p.Bold,
		}
	}
	m.pixelMu.Unlock()
}

func (m *AppModel) DrawBox(x, y, w, h int, title string, borderFg lipgloss.TerminalColor, bold bool) {
	fb := NewVirtualFramebuffer(w, h)
	fb.DrawBox(0, 0, w, h, title, borderFg, bold)
	m.pixelMu.Lock()
	for row := 0; row < h; row++ {
		for col := 0; col < w; col++ {
			c := fb.grid[row][col]
			if c.Char != 0 && c.Char != ' ' {
				key := fmt.Sprintf("%d:%d", x+col, y+row)
				m.pixelOverrides[key] = c
			}
		}
	}
	m.pixelMu.Unlock()
}

func (m *AppModel) ClearPixels() {
	m.pixelMu.Lock()
	m.pixelOverrides = make(map[string]Cell)
	m.pixelMu.Unlock()
}

func (m *AppModel) RegisterOverlay(id string, hook DynamicPixelHook) {
	m.hookManager.RegisterPixelHook(id, hook)
}

func (m *AppModel) RemoveOverlay(id string) {
	m.hookManager.RemovePixelHook(id)
}

func (m *AppModel) SetTextHook(target, content string) {
	m.hookManager.SetTextHook(target, content)
}

func (m *AppModel) ClearTextHook(target string) {
	m.hookManager.ClearTextHook(target)
}

func (m *AppModel) SetPrompt(prefix, arrow string, fgPrefix, fgArrow lipgloss.TerminalColor) {
	m.promptCfg = PromptConfig{
		Prefix:   prefix,
		Arrow:    arrow,
		FgPrefix: fgPrefix,
		FgArrow:  fgArrow,
	}
}

func (m *AppModel) ResetPrompt() {
	m.promptCfg = PromptConfig{
		Prefix:   "ROOT ",
		Arrow:    "❯ ",
		FgPrefix: m.theme.Secondary,
		FgArrow:  m.theme.Primary,
	}
}

func (m *AppModel) BindKey(key, command string) {
	m.keybindMu.Lock()
	defer m.keybindMu.Unlock()
	m.keybindings[strings.ToLower(strings.TrimSpace(key))] = command
}

func (m *AppModel) UnbindKey(key string) {
	m.keybindMu.Lock()
	defer m.keybindMu.Unlock()
	delete(m.keybindings, strings.ToLower(strings.TrimSpace(key)))
}

func (m *AppModel) PatchCommand(targetCmd, rewriteCmd string) {
	m.kernel.PatchCommand(targetCmd, rewriteCmd)
}

func (m *AppModel) UnpatchCommand(targetCmd string) {
	m.kernel.UnpatchCommand(targetCmd)
}

func (m *AppModel) ForceCloseTab(tabIdx int) bool {
	if tabIdx >= 0 && tabIdx < len(m.tabs) {
		m.tabs = append(m.tabs[:tabIdx], m.tabs[tabIdx+1:]...)
		if len(m.tabs) == 0 {
			m.hasWorkspace = false
			m.activeTab = 0
		} else if m.activeTab >= len(m.tabs) {
			m.activeTab = len(m.tabs) - 1
		}
		return true
	}
	return false
}

func (m *AppModel) InjectTab(title, cmd, output string) {
	boxWidth, vpHeight, _ := m.calculateLayout()
	safeBoxW := boxWidth - 6
	if safeBoxW < 10 {
		safeBoxW = 10
	}
	safeVpH := vpHeight
	if safeVpH < 3 {
		safeVpH = 3
	}

	m.tabCounter++
	newTab := NewWorkspaceTab(m.tabCounter, cmd, title, output, nil, 0, safeBoxW, safeVpH)
	m.tabs = append(m.tabs, newTab)
	m.activeTab = len(m.tabs) - 1
	m.hasWorkspace = true
}

func (m *AppModel) UpdateTabOutput(tabIdx int, output string) bool {
	if tabIdx >= 0 && tabIdx < len(m.tabs) {
		m.tabs[tabIdx].Output = output
		m.tabs[tabIdx].Viewport.SetContent(strings.TrimRight(output, "\r\n"))
		m.tabs[tabIdx].Viewport.GotoTop()
		return true
	}
	return false
}

func (m *AppModel) SetRawScreenContent(rendered string) {
	m.overrideScreenContent = rendered
}

func (m *AppModel) HijackInputFocus(active bool) {
	m.inputHijacked = active
}

func (m *AppModel) GetTerminalDimensions() (width, height int) {
	return m.width, m.height
}

// YENİ: Harici TUI Başlatma İsteği ve Güvenlik Onay Modalı
func (m *AppModel) RequestExternalTUI(binary string, args []string, name string, confirmMsg string) {
	if name == "" {
		name = binary
	}
	msg := confirmMsg
	if msg == "" {
		msg = fmt.Sprintf("⚠️ '%s' eklentisi terminali devralarak kendi tam ekran arayüzünü (TUI) başlatmak istiyor.\n\nKomut: %s %s\n\nAna sisteme dönmek için eklenti arayüzünden çıkmanız ('q' veya Ctrl+C) yeterlidir.\n\nDevam etmek istiyor musunuz?", name, binary, strings.Join(args, " "))
	}

	m.pendingTUI = &PendingTUIRequest{
		Binary: binary,
		Args:   args,
		Name:   name,
	}

	m.OpenConfirm("HARİCİ TUI YÖNLENDİRME ONAYI", msg, func(confirmed bool) {
		if !confirmed {
			m.pendingTUI = nil
			m.Toast("Harici TUI yönlendirmesi iptal edildi.", false)
		}
	})
}

func (m *AppModel) ExecuteIPCAction(actionJSON string) string {
	rawTrimmed := strings.TrimSpace(actionJSON)
	if !strings.HasPrefix(rawTrimmed, "{") || !strings.HasSuffix(rawTrimmed, "}") {
		return ""
	}

	var payload map[string]any
	if err := json.Unmarshal([]byte(rawTrimmed), &payload); err != nil {
		return ""
	}

	getString := func(key string) string {
		val, ok := payload[key]
		if !ok || val == nil {
			return ""
		}
		return fmt.Sprintf("%v", val)
	}

	getInt := func(key string, defaultVal int) int {
		val, ok := payload[key]
		if !ok || val == nil {
			return defaultVal
		}
		switch v := val.(type) {
		case float64:
			return int(v)
		case int:
			return v
		case string:
			if n, err := strconv.Atoi(v); err == nil {
				return n
			}
		}
		return defaultVal
	}

	action := strings.ToLower(getString("action"))
	if action == "" {
		action = strings.ToLower(getString("type"))
	}

	switch action {
	// YENİ: Eklenti üzerinden Harici TUI Talebi
	case "launch_tui", "handover_tui", "external_tui":
		bin := getString("command")
		if bin == "" {
			bin = getString("binary")
		}
		name := getString("name")
		prompt := getString("prompt")
		var args []string
		if rawArgs, ok := payload["args"].([]any); ok {
			for _, a := range rawArgs {
				args = append(args, fmt.Sprintf("%v", a))
			}
		}
		if bin != "" {
			m.RequestExternalTUI(bin, args, name, prompt)
			return fmt.Sprintf("⏳ Harici TUI devir isteği onay bekliyor: [%s]", bin)
		}

	case "pixel", "set_pixel":
		x := getInt("x", 0)
		y := getInt("y", 0)
		chStr := getString("char")
		r := '█'
		if len(chStr) > 0 {
			r = []rune(chStr)[0]
		}
		fgHex := getString("fg")
		bgHex := getString("bg")
		var fg, bg lipgloss.TerminalColor
		if fgHex != "" {
			fg = lipgloss.Color(fgHex)
		}
		if bgHex != "" {
			bg = lipgloss.Color(bgHex)
		}
		m.MutatePixel(x, y, r, fg, bg, true)
		return fmt.Sprintf("⚡ [ROOT] Tekil piksel manipüle edildi: (%d, %d)", x, y)

	case "pixels", "draw_batch":
		rawList, ok := payload["pixels"].([]any)
		if ok {
			var batch []CellMutation
			for _, item := range rawList {
				pMap, isMap := item.(map[string]any)
				if !isMap {
					continue
				}
				px := 0
				py := 0
				if val, ok := pMap["x"].(float64); ok {
					px = int(val)
				}
				if val, ok := pMap["y"].(float64); ok {
					py = int(val)
				}
				pr := '█'
				if cVal, ok := pMap["char"].(string); ok && len(cVal) > 0 {
					pr = []rune(cVal)[0]
				}
				var pFg, pBg lipgloss.TerminalColor
				if fVal, ok := pMap["fg"].(string); ok && fVal != "" {
					pFg = lipgloss.Color(fVal)
				}
				if bVal, ok := pMap["bg"].(string); ok && bVal != "" {
					pBg = lipgloss.Color(bVal)
				}
				batch = append(batch, CellMutation{
					X:    px,
					Y:    py,
					Char: pr,
					Fg:   pFg,
					Bg:   pBg,
					Bold: true,
				})
			}
			m.MutatePixelBatch(batch)
			return fmt.Sprintf("⚡ [ROOT] Toplu piksel matrisi işlendi: %d hücre", len(batch))
		}

	case "box", "rect":
		bx := getInt("x", 0)
		by := getInt("y", 0)
		bw := getInt("w", 20)
		bh := getInt("h", 6)
		title := getString("title")
		fgHex := getString("fg")
		var fg lipgloss.TerminalColor
		if fgHex != "" {
			fg = lipgloss.Color(fgHex)
		} else {
			fg = m.theme.Primary
		}
		m.DrawBox(bx, by, bw, bh, title, fg, true)
		return fmt.Sprintf("⚡ [ROOT] Geometrik kutu çizildi: (%d, %d) [%dx%d]", bx, by, bw, bh)

	case "clear_pixels", "wipe_screen":
		m.ClearPixels()
		return "⚡ [ROOT] Sanal piksel katmanı temizlendi."

	case "set_prompt":
		pfx := getString("prefix")
		arr := getString("arrow")
		fgP := lipgloss.Color(getString("fg_prefix"))
		fgA := lipgloss.Color(getString("fg_arrow"))
		m.SetPrompt(pfx, arr, fgP, fgA)
		return fmt.Sprintf("⚡ [ROOT] Kabuk prompt'u canlıda güncellendi: %s%s", pfx, arr)

	case "reset_prompt":
		m.ResetPrompt()
		return "✔ Prompt varsayılana döndü."

	case "bind_key":
		k := getString("key")
		cmd := getString("cmd")
		if k != "" && cmd != "" {
			m.BindKey(k, cmd)
			return fmt.Sprintf("⚡ [ROOT] Tuş kancalandı: [%s] -> %s", strings.ToUpper(k), cmd)
		}

	case "unbind_key":
		k := getString("key")
		m.UnbindKey(k)
		return fmt.Sprintf("✔ Tuş bağı kaldırıldı: [%s]", strings.ToUpper(k))

	case "patch_cmd":
		target := getString("target")
		rewrite := getString("rewrite")
		if target != "" && rewrite != "" {
			m.PatchCommand(target, rewrite)
			return fmt.Sprintf("⚡ [ROOT] Komut yamalandı: /%s -> /%s", target, rewrite)
		}

	case "unpatch_cmd":
		target := getString("target")
		m.UnpatchCommand(target)
		return fmt.Sprintf("✔ Komut yaması kaldırıldı: /%s", target)

	case "overlay", "matrix":
		id := getString("id")
		if id == "" {
			id = "plugin_overlay"
		}
		text := getString("text")
		posX := getInt("x", 0)
		posY := getInt("y", 0)
		fgHex := getString("fg")
		var fg lipgloss.TerminalColor
		if fgHex != "" {
			fg = lipgloss.Color(fgHex)
		}
		m.RegisterOverlay(id, func(fb *VirtualFramebuffer, width, height int) {
			fb.DrawText(posX, posY, text, fg, nil, true)
		})
		return fmt.Sprintf("⚡ [ROOT] Sanal kanca overlay enjekte edildi: [%s]", id)

	case "remove_overlay":
		id := getString("id")
		m.RemoveOverlay(id)
		return fmt.Sprintf("✔ Overlay kaldırıldı: [%s]", id)

	case "hook":
		target := getString("target")
		if target == "" {
			target = "banner"
		}
		content := getString("content")
		if content == "" {
			m.ClearTextHook(target)
			return fmt.Sprintf("✔ Kanca sıfırlandı: [%s]", target)
		}
		m.SetTextHook(target, content)
		return fmt.Sprintf("✔ Metin kancası güncellendi: [%s]", target)

	case "toast":
		msg := getString("message")
		isErr := false
		if b, ok := payload["is_error"].(bool); ok {
			isErr = b
		}
		m.Toast(msg, isErr)
		return fmt.Sprintf("✔ Bildirim gönderildi: %s", msg)

	case "theme_custom":
		palette := ThemePalette{
			Name:        getString("name"),
			Primary:     lipgloss.Color(getString("primary")),
			Secondary:   lipgloss.Color(getString("secondary")),
			BgDark:      lipgloss.Color(getString("bg_dark")),
			BorderColor: lipgloss.Color(getString("border_color")),
			TextMain:    lipgloss.Color(getString("text_main")),
			TextMuted:   lipgloss.Color(getString("text_muted")),
			BadgeBg:     lipgloss.Color(getString("badge_bg")),
		}
		if palette.Name == "" {
			palette.Name = "custom_root"
		}
		m.SetCustomTheme(palette)
		return fmt.Sprintf("⚡ [ROOT] Özel tema enjekte edildi: %s", palette.Name)

	case "kv_set":
		k := getString("key")
		v := getString("value")
		if k != "" {
			m.KV().Set(k, v)
			return fmt.Sprintf("✔ Shared State kaydedildi: %s=%s", k, v)
		}

	case "force_close_tab":
		idx := getInt("index", -1)
		if idx >= 0 && m.ForceCloseTab(idx) {
			return fmt.Sprintf("⚡ Sekme #%d çekirdek tarafından kapatıldı.", idx+1)
		}

	case "inject_tab":
		title := getString("title")
		cmd := getString("cmd")
		out := getString("output")
		m.InjectTab(title, cmd, out)
		return fmt.Sprintf("⚡ Doğrudan sekme oluşturuldu: [%s]", title)

	case "update_tab":
		idx := getInt("index", -1)
		out := getString("output")
		if idx >= 0 && m.UpdateTabOutput(idx, out) {
			return fmt.Sprintf("⚡ Sekme #%d güncellendi.", idx+1)
		}

	case "theme":
		name := getString("name")
		if m.SetTheme(name) {
			return fmt.Sprintf("✔ Tema güncellendi: %s", name)
		}

	case "modal":
		m.OpenModal(getString("title"), getString("content"))
		return "✔ Modal açıldı."
	}

	return ""
}

func (m *AppModel) calculateLayout() (boxWidth, vpHeight int, isCompact bool) {
	w := m.width
	if w < 20 {
		w = 80
	}
	h := m.height
	if h < 10 {
		h = 24
	}

	boxWidth = w - 4
	if boxWidth > 80 {
		boxWidth = 80
	}
	if boxWidth < 30 {
		boxWidth = 30
	}

	isCompact = h < 32 || (m.hasWorkspace && len(m.tabs) > 0)

	overhead := 14
	if isCompact {
		overhead = 10
	}
	if h < 22 {
		overhead = 7
	}

	vpHeight = h - overhead
	if vpHeight < 3 {
		vpHeight = 3
	}
	if vpHeight > 22 {
		vpHeight = 22
	}
	return boxWidth, vpHeight, isCompact
}

func (m *AppModel) StartWatchdog(ctx context.Context) {
	go func() {
		ticker := time.NewTicker(1200 * time.Millisecond)
		defer ticker.Stop()
		for {
			select {
			case <-ctx.Done():
				return
			case <-ticker.C:
				if changed, count := m.kernel.CheckAndReload(getPluginsDir()); changed {
					m.SendTUI(HotReloadMsg{Count: count})
				}
			}
		}
	}()
}

func NewAppModel() *AppModel {
	cfg := loadConfig()
	initialTheme, _ := getThemeByName(cfg.Theme)

	store := NewSharedStateStore(filepath.Join(getBaseDir(), ".mt_state.json"))

	ti := textinput.New()
	ti.Placeholder = "komut yazın (/help, /sys, /tui htop, /sh ls | grep main)..."
	ti.Focus()
	ti.CharLimit = 160
	ti.Prompt = ""
	ti.Width = 60

	m := &AppModel{
		input:          ti,
		config:         cfg,
		theme:          initialTheme,
		hookManager:    NewSuperuserHookManager(),
		store:          store,
		statusMsg:      "MT Core v11.5 (Crash-Proof TUI) devrede. Komut için '/' yazın.",
		historyIdx:     -1,
		lastInputVal:   "",
		pixelOverrides: make(map[string]Cell),
		keybindings:    make(map[string]string),
	}

	m.ResetPrompt()
	m.kernel = NewKernelEngine(m)

	_ = m.kernel.RegisterBuiltin(&HelpCommand{kernel: m.kernel})
	_ = m.kernel.RegisterBuiltin(&TuiHandoverPlugin{})
	_ = m.kernel.RegisterBuiltin(&SysDaemonPlugin{})
	_ = m.kernel.RegisterBuiltin(&ShellPlugin{})
	_ = m.kernel.RegisterBuiltin(&ThemeSwitchPlugin{})

	_ = m.kernel.RegisterBuiltin(&SimpleCmd{
		manifest: Manifest{Command: "clear", Title: "EKRANI TEMİZLE", Category: "CORE", Description: "Tüm çalışma sekmelerini kapatır", Capabilities: CapUI},
		viewFn:   func() string { return "" },
	})
	_ = m.kernel.RegisterBuiltin(&SimpleCmd{
		manifest: Manifest{Command: "exit", Title: "GÜVENLİ ÇIKIŞ", Category: "CORE", Description: "Terminal oturumunu sonlandırır", Capabilities: CapUI},
		viewFn:   func() string { return "" },
	})

	_, modCount := m.kernel.CheckAndReload(getPluginsDir())

	allCmds := m.kernel.Search("")
	m.statusMsg = fmt.Sprintf("MT Core v11.5 hazır. (%d komut [%d eklenti] | Tema: %s)", len(allCmds), modCount, m.theme.Name)

	return m
}

func (m *AppModel) Init() tea.Cmd {
	return textinput.Blink
}

// FIX: Komut yürütme motoru akıllı hale getirildi (Kullanıcı / koymasa bile kabuk veya komuta yönlendirir)
func (m *AppModel) executeCommandString(rawInput string) (tea.Model, tea.Cmd) {
	inputStr := strings.TrimSpace(rawInput)
	m.input.SetValue("")
	m.selectedIndex = 0
	m.historyIdx = -1
	m.historyDraft = ""
	m.lastInputVal = ""

	if inputStr == "" {
		return m, nil
	}

	// Kullanıcı '/' koymadıysa akıllı yönlendirme (Örn: 'sys' -> '/sys', 'ls -la' -> '/sh ls -la')
	if !strings.HasPrefix(inputStr, "/") {
		firstWord := strings.ToLower(strings.Split(inputStr, " ")[0])
		if _, ok := m.kernel.Resolve(firstWord); ok {
			inputStr = "/" + inputStr
		} else {
			inputStr = "/sh " + inputStr
		}
	}

	matches := m.kernel.Search(inputStr)
	if strings.HasPrefix(inputStr, "/") && !strings.Contains(inputStr, " ") && len(matches) > 0 {
		topCmd := "/" + matches[0].Command
		if inputStr != topCmd && strings.HasPrefix(topCmd, inputStr) {
			inputStr = topCmd
		}
	}

	proceed, filtered := m.kernel.FilterCommand(inputStr)
	if !proceed {
		m.statusMsg = "Komut güvenlik filtresi tarafından durduruldu."
		m.isError = true
		return m, nil
	}

	histLen := len(m.config.History)
	if histLen == 0 || m.config.History[histLen-1] != filtered {
		m.config.History = append(m.config.History, filtered)
		if len(m.config.History) > 100 {
			m.config.History = m.config.History[len(m.config.History)-100:]
		}
		saveConfig(m.config)
	}

	stages := ParseExecutionLine(filtered)
	if len(stages) == 0 {
		return m, nil
	}

	var lastOutput string
	boxWidth, vpHeight, _ := m.calculateLayout()
	safeBoxW := boxWidth - 6
	if safeBoxW < 10 {
		safeBoxW = 10
	}
	safeVpH := vpHeight
	if safeVpH < 3 {
		safeVpH = 3
	}

	for _, stage := range stages {
		if stage.CmdName == "" {
			continue
		}

		switch stage.CmdName {
		case "exit", "quit":
			if m.watchCancel != nil {
				m.watchCancel()
			}
			m.kernel.Shutdown()
			return m, tea.Quit
		case "clear":
			m.hasWorkspace = false
			m.tabs = nil
			m.activeTab = 0
			m.statusMsg = "Ekran temizlendi."
			m.isError = false
			return m, nil
		}

		if plugin, ok := m.kernel.Resolve(stage.CmdName); ok {
			pipeIn := ""
			if stage.IsPiped {
				pipeIn = lastOutput
			}

			cmdSnapshot := stage.CmdName
			argsSnapshot := stage.Args
			pipeSnapshot := pipeIn

			execFunc := func(th ThemePalette, w, h int) string {
				ctx := &PluginContext{
					Width:      w,
					Height:     h,
					InvokedCmd: cmdSnapshot,
					Args:       argsSnapshot,
					PipeInput:  pipeSnapshot,
					Theme:      th,
					Host:       m,
				}
				return plugin.View(ctx)
			}

			startT := time.Now()
			out := execFunc(m.theme, safeBoxW, safeVpH)
			dur := time.Since(startT)
			lastOutput = out

			cmdLabel := "/" + stage.CmdName
			if len(stage.Args) > 0 {
				cmdLabel += " " + strings.Join(stage.Args, " ")
			}
			if stage.IsPiped {
				cmdLabel = "| " + cmdLabel
			}
			if len(cmdLabel) > 20 {
				cmdLabel = cmdLabel[:17] + "..."
			}

			var tabRenderFn TabRenderFunc
			switch stage.CmdName {
			case "sys", "help":
				tabRenderFn = execFunc
			}

			m.tabCounter++
			newTab := NewWorkspaceTab(m.tabCounter, cmdLabel, stage.CmdName, out, tabRenderFn, dur, safeBoxW, safeVpH)
			m.tabs = append(m.tabs, newTab)
			m.activeTab = len(m.tabs) - 1
			m.hasWorkspace = true
		} else {
			m.statusMsg = fmt.Sprintf("Tanımlanamayan komut: '/%s'. Yardım için: /help", stage.CmdName)
			m.isError = true
			return m, nil
		}
	}

	m.statusMsg = fmt.Sprintf("Sekme #%d açıldı. (Alt+1..%d geçiş | Ctrl+Y kopyala)", len(m.tabs), len(m.tabs))
	m.isError = false
	return m, nil
}

func (m *AppModel) Update(msg tea.Msg) (retModel tea.Model, cmd tea.Cmd) {
	defer func() {
		if r := recover(); r != nil {
			stack := string(debug.Stack())
			_ = os.WriteFile("mt_panic.log", []byte(fmt.Sprintf("PANIC IN UPDATE: %v\n\n%s", r, stack)), 0644)
			m.statusMsg = fmt.Sprintf("⚠️ Çekirdek Hatası (mt_panic.log): %v", r)
			m.isError = true
			m.input.Focus()
			retModel = m
			cmd = nil
		}
	}()

	for _, it := range m.kernel.builtins {
		ctx := &PluginContext{Host: m, Width: m.width, Height: m.height, Theme: m.theme}
		if consumed, hijackedCmd := it.Update(msg, ctx); consumed {
			return m, hijackedCmd
		}
	}

	switch msg := msg.(type) {
	case tea.WindowSizeMsg:
		m.width = msg.Width
		m.height = msg.Height
		boxWidth, vpHeight, _ := m.calculateLayout()
		m.input.Width = boxWidth - 10

		safeBoxW := boxWidth - 6
		if safeBoxW < 10 {
			safeBoxW = 10
		}
		safeVpH := vpHeight
		if safeVpH < 3 {
			safeVpH = 3
		}

		for i := range m.tabs {
			m.tabs[i].Viewport.Width = safeBoxW
			m.tabs[i].Viewport.Height = safeVpH
			if m.tabs[i].RenderFn != nil {
				m.tabs[i].Output = m.tabs[i].RenderFn(m.theme, safeBoxW, safeVpH)
			}
			m.tabs[i].Viewport.SetContent(m.tabs[i].Output)
			m.tabs[i].Viewport.GotoTop()
		}
		return m, nil

	// YENİ: Harici TUI'den Çıkıldığında Çalışan Güvenli Geri Dönüş Olayı
	case ExternalTUIFinishedMsg:
		m.statusMsg = "✔ Harici TUI oturumundan ana sisteme dönüldü."
		m.isError = false
		if msg.Err != nil {
			m.Toast(fmt.Sprintf("Harici TUI sonlandı (Bilgi: %v)", msg.Err), false)
		} else {
			m.Toast("✔ Harici TUI oturumu başarıyla tamamlandı.", false)
		}
		return m, nil

	case NotifyMsg:
		m.statusMsg = msg.Text
		m.isError = msg.IsError
		return m, nil

	case HotReloadMsg:
		allCmds := m.kernel.Search("")
		m.statusMsg = fmt.Sprintf("Modüller güncellendi. (%d komut aktif [%d eklenti])", len(allCmds), msg.Count)
		return m, nil

	case ToastTriggerMsg:
		m.activeToast = &ToastMsg{ID: msg.ID, Text: msg.Text, IsError: msg.IsError}
		return m, tea.Tick(3*time.Second, func(t time.Time) tea.Msg {
			return ToastClearMsg{ID: msg.ID}
		})

	case ToastClearMsg:
		if m.activeToast != nil && m.activeToast.ID == msg.ID {
			m.activeToast = nil
		}
		return m, nil

	case tea.MouseMsg:
		if m.hasWorkspace && len(m.tabs) > 0 && m.activeTab >= 0 && m.activeTab < len(m.tabs) {
			switch msg.Button {
			case tea.MouseButtonWheelUp:
				m.tabs[m.activeTab].Viewport.LineUp(3)
				return m, nil
			case tea.MouseButtonWheelDown:
				m.tabs[m.activeTab].Viewport.LineDown(3)
				return m, nil
			}
		}

	case tea.KeyMsg:
		if msg.Type == tea.KeyCtrlC {
			if m.watchCancel != nil {
				m.watchCancel()
			}
			m.kernel.Shutdown()
			return m, tea.Quit
		}

		m.keybindMu.RLock()
		boundCmd, hasKeybind := m.keybindings[strings.ToLower(msg.String())]
		m.keybindMu.RUnlock()
		if hasKeybind && boundCmd != "" {
			return m.executeCommandString(boundCmd)
		}

		// Modal ve Harici TUI Onay Kutusu Tuş Dinleyicisi
		if m.activeModal != nil {
			if m.activeModal.IsConfirm {
				switch strings.ToLower(msg.String()) {
				case "y", "enter":
					cb := m.activeModal.OnConfirm
					m.CloseModal()
					if cb != nil {
						cb(true)
					}
					// Kullanıcı onay verdi: Bubble Tea terminali harici TUI'ye devreder!
					if m.pendingTUI != nil {
						req := m.pendingTUI
						m.pendingTUI = nil
						cmdExec := exec.Command(req.Binary, req.Args...)
						return m, tea.ExecProcess(cmdExec, func(err error) tea.Msg {
							return ExternalTUIFinishedMsg{Err: err}
						})
					}
					return m, nil

				case "n", "esc", "q":
					cb := m.activeModal.OnConfirm
					m.CloseModal()
					if cb != nil {
						cb(false)
					}
					m.pendingTUI = nil
					return m, nil
				}
				return m, nil
			}

			if msg.String() == "esc" || (!m.activeModal.IsPrompt && msg.String() == "q") {
				m.CloseModal()
				return m, nil
			}

			if m.activeModal.IsPrompt && m.activeModal.InputModel != nil {
				if msg.String() == "enter" {
					val := m.activeModal.InputModel.Value()
					cb := m.activeModal.Callback
					m.CloseModal()
					if cb != nil {
						cb(val)
					}
					return m, nil
				}
				updatedTi, tiCmd := m.activeModal.InputModel.Update(msg)
				*m.activeModal.InputModel = updatedTi
				return m, tiCmd
			}

			if msg.String() == "enter" {
				m.CloseModal()
				return m, nil
			}
			return m, nil
		}

		if msg.Type == tea.KeyCtrlY {
			if m.hasWorkspace && len(m.tabs) > 0 && m.activeTab >= 0 && m.activeTab < len(m.tabs) {
				m.ClipboardSet(m.tabs[m.activeTab].Output)
				m.Toast("📋 Sekme çıktısı panoya kopyalandı!", false)
				return m, nil
			}
		}

		if msg.Type == tea.KeyCtrlW {
			if m.hasWorkspace && len(m.tabs) > 0 {
				m.ForceCloseTab(m.activeTab)
				return m, nil
			}
		}

		switch msg.String() {
		case "alt+right", "alt+l":
			if len(m.tabs) > 0 {
				m.activeTab = (m.activeTab + 1) % len(m.tabs)
				m.hasWorkspace = true
				return m, nil
			}
		case "alt+left", "alt+h":
			if len(m.tabs) > 0 {
				m.activeTab = (m.activeTab - 1 + len(m.tabs)) % len(m.tabs)
				m.hasWorkspace = true
				return m, nil
			}
		}

		if strings.HasPrefix(msg.String(), "alt+") {
			keyNum := strings.TrimPrefix(msg.String(), "alt+")
			if idx, err := strconv.Atoi(keyNum); err == nil && idx >= 1 && idx <= len(m.tabs) {
				m.activeTab = idx - 1
				m.hasWorkspace = true
				return m, nil
			}
		}

		if m.hasWorkspace && len(m.tabs) > 0 && m.activeTab >= 0 && m.activeTab < len(m.tabs) {
			switch msg.Type {
			case tea.KeyPgUp:
				m.tabs[m.activeTab].Viewport.HalfViewUp()
				return m, nil
			case tea.KeyPgDown:
				m.tabs[m.activeTab].Viewport.HalfViewDown()
				return m, nil
			}
		}

		raw := m.input.Value()
		isSearching := strings.HasPrefix(raw, "/")
		matches := m.kernel.Search(raw)

		switch msg.String() {
		case "esc":
			if m.input.Value() != "" {
				m.input.SetValue("")
				m.selectedIndex = 0
				m.historyIdx = -1
				m.historyDraft = ""
				m.lastInputVal = ""
				return m, nil
			}
			if m.hasWorkspace {
				m.hasWorkspace = false
				m.tabs = nil
				m.activeTab = 0
				m.statusMsg = "Çalışma alanı kapatıldı."
				return m, nil
			}
			return m, nil

		case "up":
			if m.historyIdx == -1 && isSearching && len(matches) > 0 {
				m.selectedIndex--
				if m.selectedIndex < 0 {
					m.selectedIndex = len(matches) - 1
				}
				return m, nil
			}
			if len(m.config.History) > 0 {
				if m.historyIdx == -1 {
					m.historyDraft = m.input.Value()
				}
				if m.historyIdx < len(m.config.History)-1 {
					m.historyIdx++
					target := m.config.History[len(m.config.History)-1-m.historyIdx]
					m.input.SetValue(target)
					m.input.SetCursor(len(target))
					m.lastInputVal = target
				}
				return m, nil
			}

		case "down":
			if m.historyIdx == -1 && isSearching && len(matches) > 0 {
				m.selectedIndex++
				if m.selectedIndex >= len(matches) {
					m.selectedIndex = 0
				}
				return m, nil
			}
			if m.historyIdx >= 0 {
				m.historyIdx--
				if m.historyIdx < 0 {
					m.input.SetValue(m.historyDraft)
					m.input.SetCursor(len(m.historyDraft))
					m.lastInputVal = m.historyDraft
					m.historyDraft = ""
				} else {
					target := m.config.History[len(m.config.History)-1-m.historyIdx]
					m.input.SetValue(target)
					m.input.SetCursor(len(target))
					m.lastInputVal = target
				}
				return m, nil
			}

		case "tab":
			if isSearching && len(matches) > 0 {
				targetIdx := m.selectedIndex
				if targetIdx >= len(matches) || targetIdx < 0 {
					targetIdx = 0
				}
				selectedCmd := "/" + matches[targetIdx].Command + " "
				m.input.SetValue(selectedCmd)
				m.input.SetCursor(len(selectedCmd))
				m.lastInputVal = selectedCmd
				return m, nil
			}

		case "enter":
			return m.executeCommandString(m.input.Value())
		}
	}

	m.input, cmd = m.input.Update(msg)

	currVal := m.input.Value()
	if currVal != m.lastInputVal {
		m.selectedIndex = 0
		m.lastInputVal = currVal
	}

	return m, cmd
}

// ============================================================================
// 11. GÖRSEL RENDER VE SÜPER KULLANICI PİKSEL ÇIKIŞ MOTORU
// ============================================================================

func formatDuration(d time.Duration) string {
	if d < time.Millisecond {
		return fmt.Sprintf("%dµs", d.Microseconds())
	}
	if d < time.Second {
		return fmt.Sprintf("%.1fms", float64(d.Microseconds())/1000.0)
	}
	return fmt.Sprintf("%.2fs", d.Seconds())
}

func (m *AppModel) renderOpenCodeBox(boxWidth int) string {
	rawInput := m.input.Value()
	isCommandMode := strings.HasPrefix(rawInput, "/")

	var matches []Manifest
	if isCommandMode {
		matches = m.kernel.Search(rawInput)
	}

	fgPrefix := m.promptCfg.FgPrefix
	if fgPrefix == nil {
		fgPrefix = m.theme.Secondary
	}
	fgArrow := m.promptCfg.FgArrow
	if fgArrow == nil {
		fgArrow = m.theme.Primary
	}

	prompt := lipgloss.NewStyle().Foreground(fgPrefix).Bold(true).Render(m.promptCfg.Prefix)
	arrow := lipgloss.NewStyle().Foreground(fgArrow).Bold(true).Render(m.promptCfg.Arrow)
	inputLine := " " + prompt + arrow + m.input.View()

	if !isCommandMode {
		return lipgloss.NewStyle().
			Border(lipgloss.RoundedBorder()).
			BorderForeground(m.theme.BorderColor).
			Width(boxWidth).
			Padding(0, 1).
			Render(inputLine)
	}

	dropdownBorder := lipgloss.Border{
		Top: "─", Bottom: "─", Left: "│", Right: "│",
		TopLeft: "╭", TopRight: "╮", BottomLeft: "├", BottomRight: "┤",
	}

	dropdownStyle := lipgloss.NewStyle().
		Border(dropdownBorder).
		BorderForeground(m.theme.BorderColor).
		Width(boxWidth).
		Padding(0, 1)

	inputAttachedBorder := lipgloss.Border{
		Top: "", Bottom: "─", Left: "│", Right: "│",
		TopLeft: "", TopRight: "", BottomLeft: "╰", BottomRight: "╯",
	}

	inputAttachedStyle := lipgloss.NewStyle().
		Border(inputAttachedBorder).
		BorderTop(false).
		BorderForeground(m.theme.BorderColor).
		Width(boxWidth).
		Padding(0, 1)

	var listLines []string
	if len(matches) == 0 {
		listLines = append(listLines, lipgloss.NewStyle().Foreground(m.theme.TextMuted).Render("  Eşleşen komut bulunamadı"))
	} else {
		limit := 4
		if len(matches) < limit {
			limit = len(matches)
		}

		innerW := boxWidth - 6
		if innerW < 22 {
			innerW = 22
		}
		cursorW := 2
		cmdW := 14
		badgeW := 6
		if innerW > 50 {
			cmdW = 18
			badgeW = 8
		}
		availDescW := innerW - cursorW - cmdW - badgeW - 3
		if availDescW < 6 {
			availDescW = 6
		}

		for i := 0; i < limit; i++ {
			item := matches[i]
			isSelected := (i == m.selectedIndex)

			cursor := "  "
			if isSelected {
				cursor = "▸ "
			}
			cursorSpan := lipgloss.NewStyle().Width(cursorW).Foreground(m.theme.Primary).Bold(true).Render(cursor)

			cmdSt := lipgloss.NewStyle().Width(cmdW).Foreground(m.theme.Primary)
			if isSelected {
				cmdSt = lipgloss.NewStyle().Width(cmdW).Foreground(m.theme.Secondary).Bold(true)
			}
			cmdSpan := cmdSt.Render("/" + item.Command)

			badgeSpan := lipgloss.NewStyle().Width(badgeW).Foreground(m.theme.TextMuted).Render("[" + item.Category + "]")

			descColor := m.theme.TextMuted
			if isSelected {
				descColor = m.theme.TextMain
			}
			descSpan := lipgloss.NewStyle().
				MaxWidth(availDescW).
				Foreground(descColor).
				Render(item.Description)

			lineContent := lipgloss.JoinHorizontal(lipgloss.Left, cursorSpan, cmdSpan, badgeSpan, descSpan)
			rowStyle := lipgloss.NewStyle().MaxHeight(1)
			if isSelected {
				rowStyle = rowStyle.Background(m.theme.BadgeBg)
			}
			listLines = append(listLines, rowStyle.Render(lineContent))
		}
	}

	topDropdown := dropdownStyle.Render(strings.Join(listLines, "\n"))
	botInput := inputAttachedStyle.Render(inputLine)

	return lipgloss.JoinVertical(lipgloss.Left, topDropdown, botInput)
}

func (m *AppModel) renderWorkspace(boxWidth int) string {
	if !m.hasWorkspace || len(m.tabs) == 0 {
		m.hasWorkspace = false
		m.activeTab = 0
		return ""
	}

	if m.activeTab < 0 {
		m.activeTab = 0
	}
	if m.activeTab >= len(m.tabs) {
		m.activeTab = len(m.tabs) - 1
	}
	curIdx := m.activeTab

	maxVisibleTabs := 4
	startTab := 0
	if curIdx >= maxVisibleTabs {
		startTab = curIdx - maxVisibleTabs + 1
	}
	endTab := startTab + maxVisibleTabs
	if endTab > len(m.tabs) {
		endTab = len(m.tabs)
	}

	var tabHeaders []string
	if startTab > 0 {
		tabHeaders = append(tabHeaders, lipgloss.NewStyle().Foreground(m.theme.TextMuted).Render(fmt.Sprintf("+%d", startTab)))
	}

	for i := startTab; i < endTab; i++ {
		tab := m.tabs[i]
		title := fmt.Sprintf("[%d: %s]", i+1, tab.Command)
		if i == curIdx {
			tabHeaders = append(tabHeaders, lipgloss.NewStyle().
				Background(m.theme.Primary).
				Foreground(lipgloss.Color("#000000")).
				Bold(true).
				Padding(0, 1).
				Render(title))
		} else {
			tabHeaders = append(tabHeaders, lipgloss.NewStyle().
				Background(m.theme.BadgeBg).
				Foreground(m.theme.TextMuted).
				Padding(0, 1).
				Render(title))
		}
	}
	if len(m.tabs) > endTab {
		tabHeaders = append(tabHeaders, lipgloss.NewStyle().Foreground(m.theme.TextMuted).Render(fmt.Sprintf("+%d", len(m.tabs)-endTab)))
	}

	tabBar := lipgloss.JoinHorizontal(lipgloss.Center, tabHeaders...)

	curTab := m.tabs[curIdx]
	scrollInfo := " [Tamamı Görünür] "
	if curTab.Viewport.TotalLineCount() > curTab.Viewport.Height {
		pct := int(curTab.Viewport.ScrollPercent() * 100)
		scrollInfo = fmt.Sprintf(" [▲ %d%% ▼] ", pct)
	}

	durStr := ""
	if curTab.Duration > 0 {
		durStr = fmt.Sprintf(" [%s] ", formatDuration(curTab.Duration))
	}

	controlsHint := lipgloss.NewStyle().Foreground(m.theme.TextMuted).Render(
		fmt.Sprintf("%s%s[Ctrl+Y | Ctrl+W]", durStr, scrollInfo),
	)

	topBar := lipgloss.JoinHorizontal(lipgloss.Center, tabBar, "  ", controlsHint)
	vpView := curTab.Viewport.View()
	boxContent := fmt.Sprintf("%s\n\n%s", topBar, vpView)

	return lipgloss.NewStyle().
		Border(lipgloss.RoundedBorder()).
		BorderForeground(m.theme.BorderColor).
		Padding(1, 2).
		Width(boxWidth).
		Render(boxContent)
}

func (m *AppModel) renderModal() string {
	if m.activeModal == nil {
		return ""
	}

	modalW := 54
	if modalW > m.width-4 {
		modalW = m.width - 4
	}
	if modalW < 24 {
		modalW = 24
	}

	titleBar := lipgloss.NewStyle().
		Foreground(lipgloss.Color("#000000")).
		Background(m.theme.Primary).
		Bold(true).
		Padding(0, 1).
		Render(" " + m.activeModal.Title + " ")

	innerW := modalW - 6
	if innerW < 18 {
		innerW = 18
	}

	var contentB strings.Builder
	contentB.WriteString(titleBar + "\n\n")
	contentB.WriteString(lipgloss.NewStyle().
		Width(innerW).
		Foreground(m.theme.TextMain).
		Render(m.activeModal.Content) + "\n")

	// YENİ: TUI Devir Onay Modalı Görünümü
	if m.activeModal.IsConfirm {
		btnYes := lipgloss.NewStyle().Background(m.theme.Primary).Foreground(lipgloss.Color("#000000")).Bold(true).Padding(0, 1).Render("[Y] Evet (Arayüze Geç)")
		btnNo := lipgloss.NewStyle().Background(m.theme.BadgeBg).Foreground(m.theme.TextMuted).Padding(0, 1).Render("[N] Hayır (İptal)")
		buttonDeck := lipgloss.JoinHorizontal(lipgloss.Center, btnYes, "   ", btnNo)
		contentB.WriteString("\n" + buttonDeck + "\n")
	} else if m.activeModal.IsPrompt && m.activeModal.InputModel != nil {
		inputBox := lipgloss.NewStyle().
			Border(lipgloss.RoundedBorder()).
			BorderForeground(m.theme.Secondary).
			Padding(0, 1).
			Render(m.activeModal.InputModel.View())
		contentB.WriteString("\n" + inputBox + "\n")
		contentB.WriteString("\n" + lipgloss.NewStyle().Foreground(m.theme.TextMuted).Render("[ENTER] Onayla  |  [ESC] İptal"))
	} else {
		contentB.WriteString("\n" + lipgloss.NewStyle().Foreground(m.theme.TextMuted).Render("[ESC / ENTER] Kapat"))
	}

	modalBox := lipgloss.NewStyle().
		Border(lipgloss.RoundedBorder()).
		BorderForeground(m.theme.Primary).
		Background(m.theme.BgDark).
		Padding(1, 2).
		Width(modalW).
		Render(contentB.String())

	safeW := m.width
	if safeW < 10 {
		safeW = 80
	}
	safeH := m.height
	if safeH < 10 {
		safeH = 24
	}
	return lipgloss.Place(safeW, safeH, lipgloss.Center, lipgloss.Center, modalBox)
}

func (m *AppModel) applyPixelOverlays(rawScreen string, width, height int) string {
	hasOverlays := m.hookManager.HasPixelHooks()

	m.pixelMu.RLock()
	hasOverrides := len(m.pixelOverrides) > 0
	var overridesCopy map[string]Cell
	if hasOverrides {
		overridesCopy = make(map[string]Cell, len(m.pixelOverrides))
		for k, v := range m.pixelOverrides {
			overridesCopy[k] = v
		}
	}
	m.pixelMu.RUnlock()

	if !hasOverlays && !hasOverrides {
		return rawScreen
	}

	fb := NewVirtualFramebuffer(width, height)
	m.hookManager.ExecutePixelPipelines(fb)

	for k, cell := range overridesCopy {
		parts := strings.Split(k, ":")
		if len(parts) == 2 {
			x, _ := strconv.Atoi(parts[0])
			y, _ := strconv.Atoi(parts[1])
			fb.SetPixel(x, y, cell.Char, cell.Fg, cell.Bg, cell.Bold)
		}
	}

	return fb.CompositeOnANSI(rawScreen)
}

func (m *AppModel) View() (viewOut string) {
	defer func() {
		if r := recover(); r != nil {
			stack := string(debug.Stack())
			_ = os.WriteFile("mt_panic.log", []byte(fmt.Sprintf("PANIC IN VIEW: %v\n\n%s", r, stack)), 0644)
			safeW := m.width
			if safeW < 10 {
				safeW = 80
			}
			safeH := m.height
			if safeH < 10 {
				safeH = 24
			}
			viewOut = lipgloss.Place(safeW, safeH, lipgloss.Center, lipgloss.Center,
				fmt.Sprintf("⚠️ Arayüz Hatası (mt_panic.log): %v\n[ESC] ile temizleyin.", r),
			)
		}
	}()

	if m.width == 0 {
		return "Yükleniyor..."
	}

	if m.overrideScreenContent != "" {
		return m.overrideScreenContent
	}

	if m.activeModal != nil {
		return m.renderModal()
	}

	boxWidth, _, isCompact := m.calculateLayout()

	var defaultBanner string
	if isCompact {
		defaultBanner = lipgloss.NewStyle().
			Foreground(m.theme.Primary).
			Bold(true).
			Render(fmt.Sprintf("● MT CORE v11.5 // %s [RING -1 HYPERVISOR]", strings.ToUpper(m.theme.Name)))
	} else {
		mPart := lipgloss.NewStyle().Foreground(m.theme.Secondary).Bold(true).Render(defaultAsciiM)
		tPart := lipgloss.NewStyle().Foreground(m.theme.Primary).Bold(true).Render(defaultAsciiT)
		defaultBanner = lipgloss.JoinHorizontal(lipgloss.Top, mPart, tPart)
	}

	banner := m.hookManager.GetTextHook("banner", defaultBanner)
	if strings.Count(banner, "\n") > 16 {
		banner = defaultBanner
	}

	workspaceView := m.renderWorkspace(boxWidth)
	inputDeck := m.renderOpenCodeBox(boxWidth)

	var toastView string
	if m.activeToast != nil {
		toastColor := m.theme.Secondary
		if m.activeToast.IsError {
			toastColor = lipgloss.Color("#FF5555")
		}
		toastView = lipgloss.NewStyle().
			Border(lipgloss.RoundedBorder()).
			BorderForeground(toastColor).
			Foreground(m.theme.TextMain).
			Padding(0, 1).
			Render("⚡ " + m.activeToast.Text)
	}

	var statusColor lipgloss.Color
	if m.isError {
		statusColor = lipgloss.Color("#EF4444")
	} else {
		statusColor = m.theme.TextMuted
	}

	defaultStatus := lipgloss.NewStyle().Foreground(statusColor).Render(m.statusMsg)
	status := m.hookManager.GetTextHook("status", defaultStatus)

	keyPill := lipgloss.NewStyle().Foreground(m.theme.TextMuted)
	keyVal := lipgloss.NewStyle().Foreground(m.theme.TextMain).Bold(true)
	footerDeck := fmt.Sprintf("%s %s   %s %s   %s %s   %s %s   %s %s",
		keyVal.Render("Tab"), keyPill.Render("Tamamla"),
		keyVal.Render("↑/↓"), keyPill.Render("Geçmiş"),
		keyVal.Render("Alt+1..9"), keyPill.Render("Sekme"),
		keyVal.Render("Ctrl+Y"), keyPill.Render("Kopyala"),
		keyVal.Render("Esc"), keyPill.Render("Temizle"),
	)

	var components []string
	components = append(components, "", banner)
	if workspaceView != "" {
		components = append(components, "", workspaceView)
	}
	components = append(components, "", inputDeck)
	if toastView != "" {
		components = append(components, "", toastView)
	}
	components = append(components, "", status, footerDeck)

	console := lipgloss.JoinVertical(lipgloss.Center, components...)

	safeW := m.width
	if safeW < 10 {
		safeW = 80
	}
	safeH := m.height
	if safeH < 10 {
		safeH = 24
	}

	rawScreen := lipgloss.Place(safeW, safeH, lipgloss.Center, lipgloss.Center, console)

	return m.applyPixelOverlays(rawScreen, safeW, safeH)
}

func main() {
	model := NewAppModel()
	ctx, cancel := context.WithCancel(context.Background())
	model.watchCancel = cancel

	p := tea.NewProgram(model, tea.WithAltScreen(), tea.WithMouseCellMotion())
	model.program = p

	model.StartWatchdog(ctx)

	if _, err := p.Run(); err != nil {
		fmt.Printf("Hata: %v\n", err)
		os.Exit(1)
	}
}
