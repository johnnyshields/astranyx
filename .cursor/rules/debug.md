# Debug Modes

Astranyx has two debug modes for different use cases.

## Debug Mode Flags

| Flag | Purpose | Behavior |
|------|---------|----------|
| `DEBUG_MODE=1` | Human debugging | Debug controls enabled, game runs normally |
| `DEBUG_CLAUDE=1` | AI/Claude debugging | Starts **FROZEN** with overlay, frame-by-frame control |

### DEBUG_MODE=1 (Human)

```bash
DEBUG_MODE=1 cargo run
```

- Game starts running normally
- Debug controls enabled (Tab, F, O, R, etc.)
- Good for testing and development

### DEBUG_CLAUDE=1 (AI)

```bash
DEBUG_CLAUDE=1 cargo run
```

- Game starts **FROZEN** at Frame 0
- Debug overlay shown by default
- Designed for AI-assisted frame-by-frame analysis
- Use `F` to unfreeze, `N` to step frames

## Quick Start (AI Mode)

```bash
# Run with Claude mode from project root
DEBUG_CLAUDE=1 cargo run --release

# Use xdotool to send keys:
DISPLAY=:0 xdotool search --name "Astranyx" key <key>
```

## Debug Controls

| Key | Action | Description |
|-----|--------|-------------|
| **F** | Freeze/Unfreeze | Toggle time advancement |
| **N** | Frame Step | Advance exactly one simulation frame |
| **P** | Screenshot | Save to `/tmp/astranyx_screenshot.webp` |
| **O** | Debug Overlay | Log frame, position, hp, enemy/bullet counts |
| **K** | Auto-Screenshot | Toggle auto-capture every 90 frames (~3s) |
| **R** | Hot-Reload | Reload all Rhai scripts from `scripts/` |
| **Tab** | Skip Segment | Jump to next segment |
| **I** | Invincibility | Toggle player invincibility |
| **Esc** | Pause Menu | (Not implemented yet) |

## Screenshot Config

Screenshots are optimized for AI token efficiency:
- **Format**: WebP lossy (smallest)
- **Scale**: 25% (480x270 from 1920x1080)
- **Quality**: 60%
- **Size**: ~1-2KB per screenshot

Config in `crates/client/src/lib.rs`:
```rust
mod screenshot_config {
    pub const SCALE: f32 = 0.25;
    pub const QUALITY: f32 = 60.0;
    pub const FORMAT: Format = Format::WebP;
}
```

## Debug Overlay Output

When enabled (O key), logs every 30 frames:
```
[OVERLAY] Frame:1080 Seg:1_approach Mode:SideScroll { angle: 0.0 } | Player: pos=(200,540,4) hp=3 | Enemies:16 Bullets:13
```

## Hot-Reload Workflow

1. Edit Rhai scripts in `scripts/` (enemies, segments, waves)
2. Press **R** in game window
3. Scripts reload without recompiling
4. Current segment re-initializes with new config

## AI Playtest Loop

```bash
# 1. Start game (frozen)
cargo run --release &

# 2. Take initial screenshot
DISPLAY=:0 xdotool search --name "Astranyx" key p

# 3. View screenshot
# (Read /tmp/astranyx_screenshot.webp)

# 4. Step frames or unfreeze
DISPLAY=:0 xdotool search --name "Astranyx" key n  # Step 1 frame
DISPLAY=:0 xdotool search --name "Astranyx" key f  # Unfreeze

# 5. Iterate: modify scripts, hot-reload, screenshot, observe
```

## Game Controls (while unfrozen)

| Key | Action |
|-----|--------|
| W/Arrow Up | Move up |
| S/Arrow Down | Move down |
| A/Arrow Left | Move left |
| D/Arrow Right | Move right |
| Z/Space | Fire |
| X | Special weapon |
| C | Focus mode (slower, precise) |
