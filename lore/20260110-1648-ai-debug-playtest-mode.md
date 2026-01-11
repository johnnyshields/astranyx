# AI Debug/Playtest Mode Implementation

## Overview

Added comprehensive debug controls for AI-assisted game development. The game now starts in a "frozen" state where simulation time doesn't advance, giving AI full control over when and how the game progresses.

## Key Concepts

### Frozen vs Paused
- **Frozen**: Simulation time stopped, game still renders. For AI control.
- **Paused**: Player-facing pause menu (not yet implemented).

The distinction allows AI to observe and step through the game without triggering pause UI.

## Implementation Details

### DebugState Struct (`crates/client/src/lib.rs`)

```rust
struct DebugState {
    frozen: bool,              // Time doesn't advance
    step_frame: bool,          // Advance one frame then freeze
    speed: f32,                // Speed multiplier (future)
    invincible: bool,          // Player can't die
    auto_screenshot_interval: u32,  // Auto-capture frames
    frame_counter: u32,        // For auto-screenshot timing
    show_overlay: bool,        // Log debug info
}
```

Starts with `frozen: true` so AI has control from frame 0.

### Debug Controls

| Key | Field | Effect |
|-----|-------|--------|
| F | `frozen` | Toggle time advancement |
| N | `step_frame` | Set true, advances 1 frame, auto-freezes |
| O | `show_overlay` | Toggle periodic state logging |
| K | `auto_screenshot_interval` | Toggle 0 ↔ 90 frames |
| I | `invincible` | Toggle invincibility flag |

### Screenshot System

Optimized for AI token efficiency:
- **WebP lossy** at 60% quality
- **25% scale** (480x270)
- **~1-2KB** per screenshot

Uses the `webp` crate for lossy encoding (the `image` crate only supports lossless WebP).

### Hot-Reload System

Added `Simulation::hot_reload_scripts()`:
1. Finds `scripts/` directory (checks `./scripts` and `../../scripts`)
2. Calls `ScriptEngine::clear()` to reset all loaded scripts
3. Calls `load_scripts_from_dir()` to reload from disk
4. Calls `on_segment_enter()` to reinitialize current segment

Press **R** to reload - no recompilation needed for script changes.

### Debug Overlay

When enabled, logs every 30 frames:
```
[OVERLAY] Frame:1080 Seg:1_approach Mode:SideScroll | Player: pos=(200,540,4) hp=3 | Enemies:16 Bullets:13
```

## Files Modified

| File | Changes |
|------|---------|
| `crates/client/src/lib.rs` | Added DebugState, debug controls, screenshot config |
| `crates/core/src/simulation.rs` | Added `hot_reload_scripts()` |
| `crates/core/src/scripting/mod.rs` | Added `clear()` method |
| `crates/client/Cargo.toml` | Added `webp` crate for lossy compression |

## AI Playtest Workflow

1. Game starts frozen at Frame 0
2. AI takes screenshot to observe initial state
3. AI can:
   - Step frames with N (precise control)
   - Unfreeze with F (real-time observation)
   - Modify scripts and hot-reload with R
   - Take screenshots with P
4. Iterate on gameplay without recompiling

## Future Enhancements

- Speed control ([ and ] keys declared but not implemented)
- Actual pause menu (Esc key placeholder)
- Invincibility integration with damage system
- On-screen debug overlay (currently logs only)
- Input recording/playback for deterministic replays
