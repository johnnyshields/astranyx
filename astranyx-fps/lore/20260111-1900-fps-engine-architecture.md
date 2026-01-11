# FPS Engine Architecture

## Overview

The Astranyx FPS engine is built as an isolated development environment (`astranyx-fps`) for first-person shooter gameplay. It uses:

- **Quake-style movement physics** (`pmove.rs`) - deterministic for P2P lockstep
- **glTF level loading** with `_col` suffix collision meshes
- **parry3d** for collision queries (not physics simulation)
- **three-d** for rendering

## Key Components

### 1. Player Movement (pmove.rs)

Based on Quake 3's `bg_pmove.c`, adapted for Rust with deterministic math:

```
PM_* Functions:
├── pmove()              - Main entry point (66ms max timestep)
├── pm_walk_move()       - Ground movement + friction + acceleration
├── pm_air_move()        - Airborne movement + gravity
├── pm_step_slide_move() - Stair stepping (0.5m steps)
├── pm_slide_move()      - Multi-plane collision (up to 5 planes)
├── pm_clip_velocity()   - Velocity reflection off surfaces
└── pm_ground_trace()    - Ground detection (MIN_WALK_NORMAL = 0.7)
```

**Constants (Quake 3 style):**
```rust
STEP_SIZE = 0.5          // Stair step height
JUMP_VELOCITY = 6.0      // Jump speed (m/s)
GRAVITY = 20.0           // ~2g for snappy feel
PM_FRICTION = 6.0        // Ground friction
PM_ACCELERATE = 10.0     // Ground accel
PM_AIR_ACCELERATE = 1.0  // Air accel (limited)
PM_WALK_SPEED = 6.0      // Walking speed (m/s)
PM_RUN_SPEED = 10.0      // Sprint speed (m/s)
```

### 2. Collision System (collision.rs + mesh.rs)

Dual backend support:

```
CollisionBackend
├── Legacy(&[GeometryDef])  - Rhai script geometry
└── Modern(&CollisionWorld) - glTF/parry3d geometry
```

**Shape types:**
- **Box** - Fastest, AABB collision
- **ConvexHull** - For irregular shapes (≤256 verts)
- **Trimesh** - Complex geometry (slowest)

**Player collision:** Vertical capsule (0.4m radius, 1.8m height)

### 3. glTF Level Loading (gltf_loader.rs)

Naming convention:
```
level.glb
├── Wall_001        → RenderMesh (visual only)
├── Wall_001_col    → CollisionShape (physics only)
├── Pillar_002      → RenderMesh
└── Pillar_002_col  → ConvexHull collision
```

Features:
- KHR_lights_punctual extension for lights
- Material base color extraction
- Transform decomposition (position, rotation, scale)

### 4. Player Entity Fields

```rust
pub struct Player {
    // 3D physics state
    pub position_3d: Vec3,
    pub velocity_3d: Vec3,
    pub look_yaw: f32,
    pub look_pitch: f32,

    // Quake-style pmove flags
    pub pm_flags: u16,      // ON_GROUND, DUCKING, JUMPING, etc.
    pub pm_time: u16,       // Jump cooldown timer
    pub ground_entity: i32, // -1 if airborne
}
```

### 5. Input Mapping

```rust
UserCmd {
    forward_move: f32,  // -1.0 to 1.0 (W/S)
    right_move: f32,    // -1.0 to 1.0 (A/D)
    up_move: f32,       // -1.0 to 1.0 (jump/crouch)
    delta_angles: Vec3, // Mouse look (radians)
    buttons: u16,       // BTN_JUMP, BTN_CROUCH, BTN_SPRINT, etc.
}
```

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                        Client (three-d)                         │
├─────────────────────────────────────────────────────────────────┤
│  Input          │  Rendering       │  Audio                     │
│  - Keyboard     │  - RenderMesh    │  - Footsteps               │
│  - Mouse        │  - Lights        │  - Gunfire                 │
│  - Gamepad      │  - Effects       │  - Ambience                │
└────────┬────────┴────────┬─────────┴──────────────────────────────┘
         │                 │
         ▼                 │
┌─────────────────────────────────────────────────────────────────┐
│                     Core Simulation                              │
├─────────────────────────────────────────────────────────────────┤
│  pmove.rs              │  collision.rs        │  fps/mod.rs      │
│  - PlayerMoveState     │  - CollisionWorld    │  - update_players│
│  - UserCmd             │  - CollisionBackend  │  - update_enemies│
│  - pm_* functions      │  - raycast           │  - check_collisions│
│  - DETERMINISTIC       │  - resolve_capsule   │  - spawn_enemies │
└─────────────────────────────────────────────────────────────────┘
         │
         ▼
┌─────────────────────────────────────────────────────────────────┐
│                      Level Data                                  │
├─────────────────────────────────────────────────────────────────┤
│  glTF/GLB              │  Rhai Scripts        │  CollisionWorld  │
│  - Meshes              │  - config.rhai       │  - Box shapes    │
│  - Lights              │  - segment.rhai      │  - ConvexHulls   │
│  - Materials           │  - enemies/*.rhai    │  - Trimeshes     │
└─────────────────────────────────────────────────────────────────┘
```

## Reference Games Analyzed

| Game | Key Insight |
|------|-------------|
| **Daemon** (idTech 3 fork) | Capsule collision, kbutton_t input, trace_t results |
| **Dark Mod** (Thief) | Stealth visibility, sound propagation, AI alert states |
| **ioq3** (Quake 3) | PM_* movement, 66ms timestep, multi-plane sliding |
| **richter** (Quake 1 Rust) | Rust-idiomatic physics, MoveKind enum |

## Determinism Guarantees

1. **Fixed timestep** - Max 66ms per physics iteration
2. **No floating-point RNG** - Only SeededRandom for gameplay
3. **Deterministic collision** - parry3d queries only, no physics solver
4. **Consistent iteration** - Arrays, not HashMaps for entities
5. **Quantized input** - Mouse delta as i16 for network sync

## File Structure

```
astranyx-fps/
├── crates/
│   ├── core/src/
│   │   ├── simulation/fps/
│   │   │   ├── pmove.rs      # Quake-style movement
│   │   │   ├── collision.rs  # Collision backends
│   │   │   ├── movement.rs   # Legacy movement (deprecated)
│   │   │   ├── sound.rs      # Sound propagation
│   │   │   ├── stealth.rs    # Visibility system
│   │   │   └── vision.rs     # Enemy vision cones
│   │   ├── level/
│   │   │   └── mesh.rs       # CollisionWorld, LevelMesh
│   │   └── entities.rs       # Player with pmove fields
│   └── client/src/
│       └── renderer/
│           └── gltf_loader.rs # glTF loading with _col support
└── scripts/
    └── worlds/01_station/segments/4_base.rhai  # FPS level config
```

## Next Steps

1. Connect pmove to the main update loop
2. Create test level in Blender with _col meshes
3. Add proper stair detection with surface normals
4. Implement crouch ceiling detection
5. Add weapon system (hitscan + projectiles)
