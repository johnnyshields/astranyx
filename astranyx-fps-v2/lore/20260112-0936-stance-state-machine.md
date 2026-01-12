# Stance State Machine Design

## Overview

The stance system supports both **toggle** and **hold** behaviors for crouch and prone positions, similar to modern tactical shooters like Battlefield and Call of Duty.

## Core Concepts

### Stances (ordered by height)
1. **Standing** - Default, highest position
2. **Crouching** - Medium position
3. **Prone** - Lowest position

### Input Types
- **Toggle** (short press): Permanently changes base stance
- **Hold** (long press): Temporarily lowers stance, reverts on release

### State Variables
```rust
struct StanceState {
    /// The stance you'll return to after releasing a held key
    base_stance: Stance,

    /// Current actual stance (may differ from base if holding)
    current_stance: Stance,

    /// Whether crouch key is being held (for hold behavior)
    crouch_held: bool,

    /// Whether prone key is being held (for hold behavior)
    prone_held: bool,
}

enum Stance {
    Standing,
    Crouching,
    Prone,
}
```

## State Transition Rules

### Toggle Behavior (short press - key down then up quickly)

| Current Base | Key | New Base |
|--------------|-----|----------|
| Standing | C | Crouching |
| Crouching | C | Standing |
| Prone | C | Crouching |
| Standing | Z | Prone |
| Crouching | Z | Prone |
| Prone | Z | Crouching |

### Hold Behavior (key held down)

| Base Stance | Key Held | Current Stance |
|-------------|----------|----------------|
| Standing | C | Crouching |
| Standing | Z | Prone |
| Crouching | C | Crouching (no change) |
| Crouching | Z | Prone |
| Prone | C | Prone (no change) |
| Prone | Z | Prone (no change) |

### Release Behavior (key released after hold)

On release, current_stance returns to base_stance (if room permits).

## Detailed Test Cases

### Basic Toggle Tests

```
Test 1: Standing -> C tap -> Crouching
- Start: base=Standing, current=Standing
- Action: C down, C up (short press)
- End: base=Crouching, current=Crouching

Test 2: Crouching -> C tap -> Standing
- Start: base=Crouching, current=Crouching
- Action: C down, C up
- End: base=Standing, current=Standing

Test 3: Standing -> Z tap -> Prone
- Start: base=Standing, current=Standing
- Action: Z down, Z up
- End: base=Prone, current=Prone

Test 4: Prone -> Z tap -> Crouching
- Start: base=Prone, current=Prone
- Action: Z down, Z up
- End: base=Crouching, current=Crouching

Test 5: Crouching -> Z tap -> Prone
- Start: base=Crouching, current=Crouching
- Action: Z down, Z up
- End: base=Prone, current=Prone

Test 6: Prone -> C tap -> Crouching
- Start: base=Prone, current=Prone
- Action: C down, C up
- End: base=Crouching, current=Crouching
```

### Hold Tests

```
Test 7: Standing -> C hold -> Crouching -> C release -> Standing
- Start: base=Standing, current=Standing
- Action: C down (hold)
- During: base=Standing, current=Crouching
- Action: C up
- End: base=Standing, current=Standing

Test 8: Standing -> Z hold -> Prone -> Z release -> Standing
- Start: base=Standing, current=Standing
- Action: Z down (hold)
- During: base=Standing, current=Prone
- Action: Z up
- End: base=Standing, current=Standing

Test 9: Crouching -> Z hold -> Prone -> Z release -> Crouching
- Start: base=Crouching, current=Crouching
- Action: Z down (hold)
- During: base=Crouching, current=Prone
- Action: Z up
- End: base=Crouching, current=Crouching

Test 10: Crouching -> C hold -> no change (already at or below)
- Start: base=Crouching, current=Crouching
- Action: C down (hold)
- During: base=Crouching, current=Crouching (no change)
- Action: C up
- End: base=Crouching, current=Crouching
```

### Combined Toggle + Hold Tests

```
Test 11: C tap -> stay crouched -> Z hold -> prone -> Z release -> back to crouch
- Start: base=Standing, current=Standing
- Action: C tap
- After: base=Crouching, current=Crouching
- Action: Z down (hold)
- During: base=Crouching, current=Prone
- Action: Z up
- End: base=Crouching, current=Crouching

Test 12: Z tap -> stay prone -> C hold -> no change -> C release -> still prone
- Start: base=Standing, current=Standing
- Action: Z tap
- After: base=Prone, current=Prone
- Action: C down (hold)
- During: base=Prone, current=Prone (can't go lower)
- Action: C up
- End: base=Prone, current=Prone

Test 13: C tap -> crouch -> C hold -> no change -> C release -> C tap -> stand
- Start: base=Standing
- Action: C tap
- After: base=Crouching
- Action: C hold (no effect, already crouching)
- After: base=Crouching
- Action: C release (no change)
- After: base=Crouching
- Action: C tap
- End: base=Standing
```

### Space Key (Jump/Stand) Tests

```
Test 14: Crouching -> Space -> Standing (if room)
- Start: base=Crouching, current=Crouching
- Action: Space (jump input while grounded)
- End: base=Standing, current=Standing

Test 15: Prone -> Space -> Standing (if room)
- Start: base=Prone, current=Prone
- Action: Space
- End: base=Standing, current=Standing

Test 16: Holding Z + Space -> cancels hold, stands up
- Start: base=Standing, current=Prone (holding Z)
- Action: Space
- End: base=Standing, current=Standing, Z hold cancelled
```

### Edge Cases

```
Test 17: Rapid C tap while crouching from hold
- Start: base=Standing, current=Crouching (holding C)
- Action: C up + C tap quickly
- End: base=Crouching, current=Crouching (toggle took effect)

Test 18: Both C and Z held simultaneously (Z takes priority - lower stance)
- Start: base=Standing
- Action: C down, Z down (both held)
- During: current=Prone (lower wins)
- Action: Z up (still holding C)
- During: current=Crouching
- Action: C up
- End: base=Standing, current=Standing

Test 19: Collision prevents standing from crouch
- Start: base=Crouching, current=Crouching, ceiling above
- Action: C tap (wants to stand)
- End: base=Crouching, current=Crouching (blocked)

Test 20: Collision prevents exiting prone
- Start: base=Standing, current=Prone (holding Z), low ceiling
- Action: Z up (wants to return to standing)
- End: current=Crouching (if fits) or Prone (if blocked)
```

## Implementation Notes

### Toggle vs Hold Detection

Use a timer to distinguish short press (toggle) from hold:
- Key down: Start timer, immediately apply temporary stance change
- Key up before threshold (~150ms): It was a toggle, make it permanent
- Key up after threshold: It was a hold, revert to base stance

Alternative (simpler):
- Key down: Always temporarily enter lower stance
- Key up: If base stance matches current, it was toggle (do nothing); otherwise revert

### Priority

When multiple keys are held:
1. Prone (Z) takes priority over Crouch (C)
2. Jump/Space overrides everything and returns to Standing

### Smooth Transitions

Eye height interpolates smoothly between stances using `crouch_fraction` and `prone_fraction`, regardless of toggle vs hold behavior.
