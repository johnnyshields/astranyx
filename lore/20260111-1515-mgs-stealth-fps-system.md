# MGS-Style Stealth FPS System Implementation

## Summary

Implemented a Metal Gear Solid-inspired stealth system for the FPS game mode. The system is isolated in `astranyx-rs/crates/core/src/simulation/fps/` to keep it separate from the shmup code.

## Module Structure

```
simulation/fps/
├── mod.rs      # Main module, public API, game loop integration
├── alert.rs    # Enemy alert state machine (MGS-style progression)
├── vision.rs   # Vision cone system with forward/peripheral detection
├── sound.rs    # Sound propagation for footsteps, gunfire, etc.
├── stealth.rs  # Player stealth mechanics (posture, cover, visibility)
└── movement.rs # FPS player movement with stealth modifiers
```

## Key Systems

### Alert State Machine (`alert.rs`)

MGS-style progression through alert levels:

```
UNAWARE → CURIOUS → ALERT → EVASION → COMBAT → SEARCH → UNAWARE
    ↑                                              │
    └──────────────────────────────────────────────┘
```

- **Unaware**: Normal patrol, slow movement
- **Curious**: Investigating a sound, "?" indicator
- **Alert**: Suspicious, "!?" indicator
- **Evasion**: Player spotted, raising alarm "!!"
- **Combat**: Actively engaging "!!!"
- **Search**: Lost sight, searching last known position "..."

Each level affects:
- Movement speed (0.5x patrol → 1.2x evasion)
- Accuracy (0.3x unaware → 1.0x combat)
- Whether global alert triggers
- Distraction vulnerability

### Vision Cone System (`vision.rs`)

Two-tier vision system:

1. **Forward Cone**: Narrow (30°), long range (200m) - full detection
2. **Peripheral Vision**: Wide (80°), short range (50m) - builds suspicion

Visibility affected by:
- Posture (prone: 0.3x, crouch: 0.6x, standing: 1.0x)
- Movement (running: 1.5x visibility)
- Light level (shadows reduce visibility)
- Cover state (in cover: 0.2x)

### Sound Propagation (`sound.rs`)

Sound types with different properties:

| Type | Base Radius | Loudness | Attracts Investigation |
|------|-------------|----------|----------------------|
| Gunfire | 500 | 1.0 | Yes |
| GlassBreak | 150 | 0.7 | Yes |
| Knockover | 100 | 0.5 | Yes |
| Footstep | 30 | 0.2 | No |

Footstep radius modified by:
- Running: 2.0x
- Crouching: 0.3x
- Surface type (metal: 1.5x, carpet: 0.4x)

### Player Stealth (`stealth.rs`)

**Postures:**
- Standing: Normal speed, normal visibility
- Crouching (FOCUS key): 0.5x speed, 0.6x visibility, 0.3x sound
- Prone: 0.2x speed, 0.3x visibility, 0.1x sound

**Cover States:**
- None: Normal
- WallLeft/WallRight: Pressed against wall, 0.3x visibility
- LowCover: Behind obstacle, 0.2x visibility
- Peeking: Temporarily exposed, 0.7x visibility

**Detection Meter:**
- Fills when spotted (rate × visibility)
- Drains when hidden
- Triggers combat when threshold reached

### Movement (`movement.rs`)

WASD movement with:
- Mouse look (same as before)
- Crouch toggle (FOCUS key)
- Sprint (SPECIAL key when standing)
- Height adjustment based on posture
- Footstep sound generation at intervals

## Integration Points

The FPS module integrates with the existing simulation:
- `update_players()` - Called from main simulation tick
- `update_enemies()` - Uses alert system for AI decisions
- `check_collisions()` - Same as before
- `spawn_enemies()` - Same as before

## Input Mapping

| Action | Input Flag |
|--------|------------|
| Move | WASD / FORWARD/BACKWARD/LEFT/RIGHT |
| Look | Mouse |
| Fire | FIRE |
| Crouch | FOCUS |
| Sprint | SPECIAL |

## Deterministic Math (`math.rs`)

Added a cross-platform deterministic math module to ensure P2P lockstep sync works across different architectures (x86 vs ARM vs WASM).

**Functions:**
- `atan2_det(y, x)` - Deterministic atan2 using Chebyshev polynomial (max error ~0.0005 rad)
- `sin_det(x)`, `cos_det(x)` - Bhaskara I's approximation
- `sqrt_det(x)` - Newton-Raphson iteration
- `length_det(x, y)` - Deterministic 2D vector length
- `normalize_angle_diff(angle)` - Normalize to [-PI, PI]

Vision system uses these instead of hardware trig functions for cross-platform consistency.

## Tests

19 unit tests (6 math + 13 FPS) covering:
- Vision cone calculations
- Alert state transitions
- Sound propagation
- Stealth visibility calculations
- Movement mechanics
- Detection meter behavior

## Future Work

1. **Raycasting**: Add actual level geometry for line-of-sight checks
2. **AI Behavior**: Integrate alert states with enemy movement/patrol
3. **FpsState**: Store per-enemy stealth state in simulation
4. **Cover Detection**: Automatic cover detection near walls
5. **Takedowns**: Silent melee attacks from behind
6. **Distractions**: Thrown items to lure enemies
7. **Radar/Soliton**: MGS-style radar showing enemy positions/facing
