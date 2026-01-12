# Stance Control Scheme Design

## Research Summary

Analyzed control schemes from major FPS titles:

| Game | Crouch | Prone | Notes |
|------|--------|-------|-------|
| **Battlefield 6** | C (toggle) or Ctrl (hold) | Z | Both options available |
| **Call of Duty** | C (toggle) | Ctrl | Has Toggle/Hold/Go-To settings |
| **Metal Gear Solid V** | C tap (toggle) | C hold | Single key, duration determines stance |

## Common Patterns

1. **Toggle vs Hold** - Most games offer both as settings
   - Toggle: Press once to enter stance, press again to exit
   - Hold: Hold key to stay in stance, release to exit
   - Go-To: Press to enter stance, use different key (Space) to exit

2. **Crouch preferences** - Players split on toggle vs hold
   - Hold preferred for quick peeks
   - Toggle preferred for sustained crouching

3. **Prone preferences** - Toggle strongly preferred
   - Prone is usually a sustained position
   - Holding a key while prone is awkward

## Chosen Scheme: Option A (CoD/Battlefield Style)

### Default Keybindings

| Action | Key | Behavior |
|--------|-----|----------|
| Crouch | C | Toggle |
| Prone | Z | Toggle |
| Stand | Space | Exit any stance |

### Stance State Machine

```
Standing <---> Crouching <---> Prone
    ^                           |
    +---------------------------+
              (Space)
```

- **C** from Standing → Crouching
- **C** from Crouching → Standing
- **Z** from Standing → Prone
- **Z** from Crouching → Prone
- **Z** from Prone → Standing (or Crouching?)
- **Space** from any stance → Standing (if room)

### Future Configuration

Make these settings configurable:

```rust
pub struct StanceConfig {
    /// Crouch behavior: Toggle, Hold, or GoTo
    pub crouch_behavior: StanceBehavior,

    /// Prone behavior: Toggle, Hold, or GoTo
    pub prone_behavior: StanceBehavior,

    /// Key bindings
    pub crouch_key: Key,
    pub prone_key: Key,
    pub stand_key: Key,
}

pub enum StanceBehavior {
    /// Press to enter, press again to exit
    Toggle,
    /// Hold to stay, release to exit
    Hold,
    /// Press to enter, use stand key to exit
    GoTo,
}
```

## Implementation Notes

1. **Collision checks** - Must verify room to stand/crouch before transitioning
2. **Smooth transitions** - Interpolate eye height over ~100-200ms
3. **Movement speed** - Each stance has different max speed
4. **Jump from crouch** - Should work (crouch-jump)
5. **Jump from prone** - Typically not allowed, must stand first

## Sources

- [Battlefield 6 Prone Controls](https://allthings.how/battlefield-6-prone-controls-and-how-to-remap-them-pc-console/)
- [CoD Modern Warfare Controls](https://gameaccess.info/call-of-duty-modern-warfare-controls-walkthrough/)
- [CoD Black Ops Cold War Controls](https://www.callofduty.com/blog/2020/11/Black-Ops-Cold-War-Controls-and-Settings-PC)
- [MGSV PC Keyboard Commands](https://steamcommunity.com/sharedfiles/filedetails/?id=902543330)
