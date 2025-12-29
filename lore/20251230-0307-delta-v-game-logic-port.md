# Delta-V Game Logic Ported to WebGL 2.5D

## Summary

Ported the complete game logic from `legacy/delta-v.html` (2D canvas) to the WebGL 2.5D client, maintaining deterministic simulation for P2P lockstep networking.

## Changes Made

### Simulation.ts (Complete Rewrite - ~2400 lines)

**Entity Systems Ported:**
- **Player System**: 5 ship levels, shields, lives, respawning, charge shots
- **Powerup System**: 11 types (SHIELD, UPGRADE, SPREAD, LASER, MISSILE, ORBIT, DRONE, SPEED, RAPID, PIERCE, LIFE)
- **Orb System**: Orbiting shield balls that absorb damage and destroy enemy bullets
- **Drone System**: 4 autonomous shooting drones that follow the player

**Enemy Types Ported (12 total):**
| Type | Behavior |
|------|----------|
| grunt | Basic sine wave movement |
| shooter | Aimed shots at player |
| swerver | Fast sine wave movement |
| tank | High HP, slow movement |
| speeder | Fast straight movement, occasional dodges |
| bomber | Slow descent, drops bombs |
| sniper | Stationary, fast aimed shots |
| carrier | Spawns mini-enemies |
| mine | Stationary explosive |
| spiral | Spiral movement, circular bullet patterns |
| shield | Protected by energy shield |
| splitter | Splits into grunts on death |

**Boss Types Ported (6 total):**
| Type | Name | Special Feature |
|------|------|-----------------|
| 0 | CLASSIC | Multiple attack patterns |
| 1 | TWIN | Two cores that move independently |
| 2 | CARRIER | Spawns enemy swarms |
| 3 | LASER | Charges and fires devastating beam |
| 4 | WALL | Multiple segments to destroy |
| 5 | FINAL | Multiple cannons, spiral patterns |

**Bullet Types:**
- `shot` - Basic player bullet
- `spread` - Angled spread shots
- `laser` - Fast penetrating laser
- `mega` - Large charged shot
- `missile` - Homing projectile
- `drone` - Drone-fired bullets
- `beam` - Full-screen charged laser
- `enemy`, `aimed`, `big`, `ring` - Enemy projectiles

**Wave Spawning System:**
- Progressive enemy unlocking based on wave number
- 6 spawn patterns: line, v, swarm, mixed, rush, surround
- Boss every 5 waves
- Heavy enemy spawns every 3 waves after wave 6

### Game.ts (Complete Rewrite - ~750 lines)

**Rendering Features:**
- Color-coded entities by type
- Health bars for enemies and bosses
- Shield effect for shield enemies
- Charge indicator for player
- Screen shake effect
- Particle explosions
- HUD with shield bar, lives, ship level, powerup indicators

**Visual Polish:**
- Glow effects on bullets and enemies
- Pulsing boss cores
- Invincibility flashing
- Orb and drone rendering
- Engine exhaust animation
- Boss-specific visual elements (twin cores, segments, laser barrel)

## Determinism Maintained

Critical for P2P lockstep networking:
- **SeededRandom (xorshift32)** - All randomness uses deterministic PRNG
- **Fixed-point math** - 16.16 format for positions
- **Frame-based timers** - No Date.now() or performance.now()
- **Array iteration** - Consistent ordering, no object/map iteration
- **No async** - Synchronous simulation only

## Key Design Decisions

### Coordinate System
- Play area: 1000x600 units centered at origin
- Positive Y is up (WebGL convention)
- Enemies spawn at right edge (+500), move left

### Timing
- 60 FPS fixed timestep
- Invincibility measured in frames (180 = 3 seconds)
- Shoot cooldown in frames
- Wave timer in seconds (converted to frames internally)

### Collision
- Simple AABB collision for all entities
- Size varies by enemy type
- Pierce mechanic tracks hit entities to prevent multi-hit

## Files Modified

| File | Lines | Change |
|------|-------|--------|
| `client/src/game/Simulation.ts` | ~2400 | Complete rewrite |
| `client/src/game/Game.ts` | ~750 | Complete rewrite |

## Running

```bash
cd client && bun run dev
# Open http://localhost:4100
# Controls: WASD move, Space shoot (hold to charge)
```

## What Works

- Player movement with ship levels
- All weapon types firing
- Enemy spawning with behaviors
- Boss spawning every 5 waves
- Powerup drops and collection
- Score multiplier system
- Screen shake and particles
- Health/shield system
- Lives and respawning
- Game over detection

## Next Steps

1. **Lobby UI** - Create/join rooms via Phoenix
2. **P2P Connection** - Full WebRTC handshake
3. **Multiplayer Testing** - Two browser windows
4. **Audio** - Web Audio API for sound effects
5. **Visual Polish** - Better 3D ship models
