# Bevy Migration Decision

## Summary

After encountering GPU buffer race conditions in the custom wgpu renderer, decided to migrate Astranyx to the Bevy game engine.

## Context

### What Was Built

The Rust port of Astranyx had:

1. **Core Simulation** (`crates/core/`)
   - Deterministic game state with fixed timestep (30Hz)
   - Entity types: Player, Enemy, Projectile, PowerUp
   - 12 enemy types with cached stats from scripts
   - Seeded RNG for determinism
   - Bincode serialization for netcode

2. **Rhai Scripting** (`crates/core/src/scripting/`)
   - Script engine loading from `scripts/` directory
   - Enemy stats defined in `enemies/*.rhai`
   - Wave system in `waves/wave_system.rhai`
   - Weapons, powerups, bosses defined in scripts
   - Stats cached at spawn time (not per-frame calls)

3. **Custom wgpu Renderer** (`crates/client/src/renderer/`)
   - Phong shading pipeline
   - Camera system with projection/view matrices
   - Mesh registration and GPU buffer management
   - Per-instance uniform buffers

4. **Game Bridge** (`crates/client/src/game.rs`)
   - Maps simulation entities to meshes
   - Color definitions per entity type

### The Problem

The renderer had a GPU buffer race condition:
- Single instance buffer reused for all meshes
- Each `draw_mesh()` overwrote buffer then started new render pass
- GPU reads could race with CPU writes
- Result: Only last mesh rendered correctly ("ships appearing one at a time")

Attempted fix (staging buffers per draw) added complexity without guaranteeing correctness.

## Decision: Migrate to Bevy

### Why Bevy

| Benefit | Details |
|---------|---------|
| **Rendering solved** | No manual wgpu, buffers, render passes |
| **ECS architecture** | Natural fit for deterministic simulation |
| **WASM support** | First-class, well-tested WebGPU/WebGL2 |
| **Community** | Large ecosystem, active development |
| **Scalability** | Can handle complex games (FPS, open world) |

### What Transfers

- **Rhai scripting** - Content definitions stay the same
- **Game design** - Enemies, waves, weapons, bosses
- **Lockstep concepts** - ECS state is serializable

### What Gets Replaced

- ~1500 lines of custom wgpu rendering
- Manual mesh/buffer management
- Camera matrix calculations
- Depth buffer handling
- Window/input setup

## Architecture After Migration

```
┌─────────────────────────────────────────────────────────┐
│                    Rhai Scripts                         │
│  enemies/*.rhai  waves/*.rhai  bosses/*.rhai           │
└─────────────────────────┬───────────────────────────────┘
                          │ stats at spawn
┌─────────────────────────▼───────────────────────────────┐
│              Bevy ECS (Rust)                            │
│  - Components: Enemy, Player, Projectile, etc.         │
│  - Systems: movement, collision, spawning              │
│  - Resources: GameState, RNG, Scripts                  │
│  - Rendering: automatic via Transform + Mesh           │
└─────────────────────────────────────────────────────────┘
```

## Files to Archive/Remove

After Bevy migration:
- `crates/client/src/renderer/` - entire directory
- `crates/client/src/game.rs` - mesh mapping
- `crates/client/src/app.rs` - winit/wgpu setup

## Next Steps

1. Create Bevy branch
2. Set up Bevy app with window
3. Port entity types to Bevy components
4. Port simulation systems to Bevy systems
5. Add rendering (spawn meshes)
6. Integrate Rhai scripting
7. Test WASM build

## Alternatives Considered

| Option | Why Not |
|--------|---------|
| **Fix wgpu renderer** | More bugs likely; time better spent |
| **three-d** | Just rendering; still need other systems |
| **Macroquad** | 2D focused, less 3D support |
| **Fyrox** | Heavier than needed for 2.5D shooter |
