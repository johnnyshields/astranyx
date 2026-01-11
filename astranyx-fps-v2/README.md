# Astranyx FPS v2

A clean rewrite of the Astranyx FPS engine, inspired by Daemon/Quake 3 but designed for modern Rust with deterministic lockstep multiplayer.

## Architecture

```
astranyx-fps-v2/
├── crates/
│   ├── physics/       # Collision & movement (Quake-style pmove)
│   ├── game/          # Game logic, entities, simulation
│   └── renderer/      # three-d PBR rendering (skeleton)
```

## Design Principles

1. **Determinism** - Same inputs produce same outputs across platforms
2. **Clean naming** - Full words, no abbreviations (position not pos)
3. **Documented** - Clear module-level and function documentation
4. **Testable** - Comprehensive unit tests for physics

## Physics System

Based on Quake 3/Daemon `bg_pmove.c`:

- **Capsule collision** using parry3d
- **Multi-plane sliding** for smooth wall navigation
- **Stair stepping** (40cm steps)
- **Ground/air physics** with friction and acceleration
- **Binary search traces** for accurate collision detection

### Key Types

```rust
// Collision
CollisionWorld    // Contains all geometry
TraceResult       // Output of collision queries
TraceShape        // Capsule, Box, or Point

// Movement
MovementState     // Position, velocity, view angles, flags
PlayerCommand     // Input for one frame
PlayerController  // Runs the physics
MovementConfig    // Tunable parameters
```

## Game System

```rust
// Core
Simulation        // Main game loop
Player            // Player entity with health, weapons
Level             // Collision + spawn points + triggers

// Input
PlayerInput       // Raw keyboard/mouse input
```

## Building

```bash
cargo build
cargo test
```

## Usage

```rust
use astranyx_physics::{CollisionWorld, PlayerController, MovementConfig};
use astranyx_game::{Simulation, PlayerInput};

// Create simulation
let mut sim = Simulation::test();
sim.add_player("Player1");

// Each frame
sim.tick(&[player_input]);
```

## Status

- [x] Collision system (parry3d-based)
- [x] Movement physics (Quake-style)
- [x] Game simulation framework
- [ ] three-d renderer integration
- [ ] glTF level loading
- [ ] Rhai scripting
- [ ] Netcode (lockstep)
