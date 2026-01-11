# Astranyx (Rust/Bevy)

2.5D multiplayer shoot-em-up game built with Bevy.

## Tech Stack

- **Engine**: Bevy 0.15 (ECS game engine)
- **Graphics**: wgpu via Bevy (WebGPU/Vulkan/Metal/DX12)
- **Scripting**: Rhai (enemy/wave definitions)
- **Networking**: Planned - lockstep P2P

## Project Structure

```
astranyx-rs/
├── src/
│   ├── main.rs         # App setup, startup systems
│   ├── components/     # Player, Enemy, Projectile, etc.
│   ├── resources/      # GameState, GameConfig, GameAssets
│   ├── systems/        # Input, movement, collision, spawning
│   └── scripting/      # Rhai script integration
├── scripts/            # Game content (enemies, waves, weapons)
│   ├── enemies/        # Enemy behavior scripts
│   ├── waves/          # Wave progression
│   ├── weapons/        # Weapon definitions
│   └── powerups/       # Powerup effects
└── lore/               # Implementation docs
```

## Quick Start

### Windows (from WSL)

```bash
cargo build --release --target x86_64-pc-windows-gnu
./target/x86_64-pc-windows-gnu/release/astranyx.exe
```

Or double-click `target/x86_64-pc-windows-gnu/release/astranyx.exe`

### Linux

```bash
cargo build --release
./target/release/astranyx
```

## Prerequisites

```bash
# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# For Windows cross-compile from Linux/WSL
sudo apt install mingw-w64
rustup target add x86_64-pc-windows-gnu
```

## Controls

| Key | Action |
|-----|--------|
| W / ↑ | Move up |
| S / ↓ | Move down |
| A / ← | Move left |
| D / → | Move right |
| Space / Z | Fire |
| Shift | Focus (slow movement) |

## Architecture

### Bevy ECS

The game uses Bevy's Entity Component System:

- **Components**: Data attached to entities (Player, Enemy, Velocity, Hitbox)
- **Systems**: Logic that runs on entities (movement, collision, spawning)
- **Resources**: Global state (GameState, GameConfig, ScriptEngine)

### Determinism

For future P2P lockstep networking:

1. **SeededRandom**: ChaCha8 PRNG with fixed seed
2. **FixedUpdate**: Simulation runs at fixed 30Hz timestep
3. **Ordered systems**: Explicit system ordering via `.chain()`

### Scripting

Rhai scripts define game content:

```rhai
// scripts/enemies/grunt.rhai
fn get_stats() {
    #{
        health: 20,
        speed: 80.0,
        fire_rate: 90,
        points: 100
    }
}
```

## License

GPL-3.0
