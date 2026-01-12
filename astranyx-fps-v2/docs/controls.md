# Astranyx FPS Controls

## Movement

| Key | Action |
|-----|--------|
| W | Move forward |
| A | Move left |
| S | Move backward |
| D | Move right |
| Shift | Sprint (hold) |
| Space | Jump / Stand up |

## Stance System

The stance system supports both **tap** (toggle) and **hold** behaviors.

### Keys

| Key | Action |
|-----|--------|
| C | Crouch (tap to toggle, hold for temporary) |
| Z | Prone (tap to toggle, hold for temporary) |
| Space | Stand up from any stance |

### Stances

```
Standing (1.6m eye height)
    │
    C (tap or hold)
    ▼
Crouching (0.75m eye height)
    │
    Z (tap or hold)
    ▼
Prone (0.25m eye height)
```

### Toggle vs Hold Behavior

**Toggle (tap)**: Short press permanently changes your stance.
- Tap C while standing → stay crouched
- Tap C while crouched → stand up
- Tap Z from any stance → go prone
- Tap Z while prone → go to crouch

**Hold**: Holding the key temporarily lowers your stance. Release returns to your previous "base" stance.
- Hold C while standing → crouch while held → stand on release
- Hold Z while standing → prone while held → stand on release
- Hold Z while crouched → prone while held → crouch on release

### Examples

**Quick peek (hold crouch):**
1. Standing
2. Hold C → crouch
3. Release C → back to standing

**Stay crouched, quick prone peek:**
1. Standing
2. Tap C → crouch (stays crouched)
3. Hold Z → prone
4. Release Z → back to crouch

**Full prone with return:**
1. Standing
2. Tap Z → prone (stays prone)
3. Tap Z → crouch
4. Tap C → standing

**Cancel with Space:**
- From any stance, press Space to immediately stand up
- This also cancels any held stance

### Movement Speed by Stance

| Stance | Speed |
|--------|-------|
| Standing | 4.5 m/s |
| Standing + Sprint | 7.0 m/s |
| Crouching | 2.0 m/s |
| Prone | 0.8 m/s |

## Combat

| Key | Action |
|-----|--------|
| Left Mouse | Fire |
| Right Mouse | Aim (future) |
| R | Reload (future) |
| E | Use/Interact (future) |

## Camera

| Key | Action |
|-----|--------|
| Mouse | Look around |
| Escape | Toggle mouse capture |
| Q | Quit game |
