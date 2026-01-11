# Astranyx FPS v2 - Clean Engine Rewrite

## Summary

Complete rewrite of the FPS engine based on Daemon/Quake 3 architecture, ported to Rust with clean naming conventions and modern tooling.

## Architecture

```
astranyx-fps-v2/
├── crates/
│   ├── physics/      # Collision & movement (Quake-style pmove)
│   ├── game/         # Entities, simulation, input
│   └── renderer/     # three-d PBR rendering
└── src/main.rs       # Main binary with game loop
```

### Crate Responsibilities

**astranyx-physics** (24 tests)
- `CollisionWorld` - parry3d-based collision detection
- `TraceResult` / `TraceShape` - Capsule/box traces with binary search
- `ContentFlags` / `SurfaceFlags` - Material classification (SOLID, WATER, CLIP, etc.)
- `PlayerController` - Quake-style movement physics
- `MovementState` - Position, velocity, view angles, flags
- `slide_move` / `step_slide_move` - Multi-plane collision response

**astranyx-game** (15 tests)
- `Simulation` - Deterministic game tick loop
- `Player` - Entity with health, movement state
- `Level` - Collision world + spawn points
- `PlayerInput` - Keyboard/mouse input per frame

**astranyx-renderer** (3 tests)
- `FirstPersonCamera` - FPS camera with glam vectors

## Key Design Decisions

### 1. Clean Naming Conventions
- Full words: `position` not `pos`, `velocity` not `vel`
- Descriptive names: `MovementState` not `pmove_t`
- Module structure follows Rust 2018+ conventions

### 2. parry3d for Collision
- `SharedShape::capsule_y()` for player collision
- `SharedShape::cuboid()` for boxes
- `SharedShape::convex_hull()` for complex geometry
- Binary search traces for accurate collision detection

### 3. Quake-Style Physics
- Ground vs air movement with different acceleration
- Friction model: `speed - (control * friction * dt)`
- Step climbing: 40cm max step height
- Multi-plane sliding: slide along up to 5 planes per frame
- Overbounce factor (1.001) to prevent sticking

### 4. Deterministic Simulation
- Fixed timestep (60Hz default)
- All physics use f32 with careful accumulation
- Same inputs produce same outputs (verified by test)

## Movement Parameters

```rust
MovementConfig {
    max_speed: 320.0,           // units/sec
    crouch_speed: 160.0,
    sprint_speed: 480.0,
    ground_acceleration: 10.0,
    air_acceleration: 1.0,
    air_control: 0.3,
    friction: 6.0,
    gravity: 800.0,
    jump_velocity: 270.0,
    step_height: 0.4,           // 40cm
    player_radius: 0.4,
    standing_height: 1.8,
    crouch_height: 1.2,
}
```

## Test Coverage

- **Gravity**: Free-fall velocity accumulation
- **Ground detection**: Standing on surfaces
- **Forward movement**: Acceleration and friction
- **Jump**: Velocity application, cooldown
- **Crouch**: State transitions, collision check for standing
- **Wall collision**: Sliding along surfaces
- **Slope handling**: Walking up/down slopes
- **Stair stepping**: Climbing 40cm steps
- **Determinism**: Same inputs = same outputs

## Main Binary Features

- three-d window with OpenGL context
- Simple test level (floor, 4 walls, central pillar)
- Mouse capture for FPS look
- WASD movement, Space jump, C crouch, Shift sprint
- Q to quit, Escape to toggle mouse capture

## Dependencies

- `parry3d` 0.18 - Collision detection
- `three-d` 0.18 - PBR rendering
- `glam` 0.30 - Math (Vec3, Mat4)
- `serde` 1.0 - Serialization (for netcode)

## Next Steps

- [ ] glTF level loading
- [ ] Rhai scripting for game logic
- [ ] Weapon system
- [ ] Projectile physics
- [ ] Lockstep netcode integration
