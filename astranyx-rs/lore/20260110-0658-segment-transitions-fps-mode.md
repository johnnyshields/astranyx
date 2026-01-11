# Segment Transitions and FPS Mode Fixes

## Summary

Fixed segment transition issues and implemented proper FPS mode support for the station world segments. Players can now smoothly transition between different game modes (SideScroll, OnRails, Turret, FirstPerson) with correct entity cleanup, player positioning, and camera behavior.

## Changes

### Segment Transition Fixes

**Problem**: When transitioning between segments, enemies were triggering death effects (debris particles) instead of being silently cleared.

**Solution** (`crates/client/src/lib.rs`):
- Track `segment_before` and `was_transitioning` state before each tick
- Skip death effect spawning if:
  - Currently transitioning (`transition.is_some()`)
  - Was transitioning before the tick
  - Segment just changed (`segment_id != segment_before`)

```rust
let segment_before = simulation.state.level.segment_id.clone();
let was_transitioning = simulation.state.level.transition.is_some();
// ... tick ...
let segment_changed = simulation.state.level.segment_id != segment_before;
if !is_transitioning && !was_transitioning && !segment_changed {
    // spawn death effects only here
}
```

### Mode-Aware Input System

**Problem**: Input handling was the same for all modes. FPS mode needs WASD for movement (FORWARD/BACKWARD) plus mouse delta, while shmup modes use UP/DOWN/LEFT/RIGHT.

**Solution** (`crates/client/src/lib.rs`):
- Added `mouse_dx`/`mouse_dy` fields to `InputState`
- Created separate input converters:
  - `to_player_input_shmup()` - Maps W/S to UP/DOWN
  - `to_player_input_fps()` - Maps W/S to FORWARD/BACKWARD, includes mouse delta
- Added mouse motion event handling
- Select converter based on `mode.is_first_person()`

```rust
let player_input = if mode.is_first_person() {
    input_state.to_player_input_fps(mouse_dx, mouse_dy)
} else {
    input_state.to_player_input_shmup()
};
```

### Player Position Reset

**Problem**: Player position wasn't being reset when entering a new segment, causing players to spawn at wrong locations.

**Solution** (`crates/core/src/simulation/mod.rs`):
- Added `on_segment_enter()` method called when transition completes
- Clears all entities (enemies, projectiles, power_ups)
- Resets player position to segment's `player_start` or mode-appropriate default
- Resets player velocity and look angles

### FPS Camera and Orientation

**Problem**: In FPS mode, player faced +Z direction but room geometry extended in -Z direction, making movement feel broken.

**Solution**:
- Set `look_yaw = PI` for FPS modes so player faces -Z (into the room)
- Camera follows player position with eye height offset
- Camera target calculated from player's `forward_3d()` direction

### Segment Config Extension

Added `player_start: Option<Vec3>` to `SegmentConfig` (`crates/core/src/level/segment.rs`) with extraction in scripting module.

## Files Modified

| File | Changes |
|------|---------|
| `crates/client/src/lib.rs` | Mode-aware input, mouse tracking, transition detection |
| `crates/core/src/simulation/mod.rs` | `on_segment_enter()`, player reset logic |
| `crates/core/src/level/segment.rs` | Added `player_start` field |
| `crates/core/src/scripting/mod.rs` | Extract `player_start` from scripts |

## Debug Features

- `DEBUG_MODE = true` enables Tab key to skip to next segment
- Useful for testing segment transitions without playing through each segment

## Testing

All 27 tests pass. Manual testing confirms:
- No death effects on segment transition
- WASD movement works in FirstPerson mode
- Mouse look works in FPS modes
- Camera follows player in FirstPerson mode
- Player faces correct direction when entering FPS segments
