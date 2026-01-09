# Rust/WASM Rewrite Plan

**Date**: 2026-01-09
**Status**: Planning

## Overview

Rewriting the Astranyx TypeScript client in Rust, targeting WebAssembly for browser deployment with optional native builds. This enables shared simulation code between client and (potential future) server, better performance, and modern graphics via WebGPU.

## Technology Choices

### Graphics: wgpu
- WebGPU backend for browsers (falls back to WebGL2)
- Native builds use Vulkan/Metal/DX12
- Low-level control similar to current raw WebGL2 approach
- Paired with `winit` for cross-platform windowing

### Networking: WebTransport + WebSocket
- **WebTransport** (`wtransport`): UDP-like datagrams for game traffic
  - Lower latency than WebRTC
  - Simpler than full WebRTC stack
  - Unreliable datagrams perfect for lockstep inputs
- **WebSocket**: Signaling/lobby (keep Phoenix server initially)

### Math: glam
- SIMD-accelerated game math
- `f32` focused, perfect for games
- Integrates well with wgpu

## Project Structure

```
astranyx-rs/
├── crates/
│   ├── core/              # Shared deterministic simulation
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── simulation.rs
│   │   │   ├── entities.rs
│   │   │   ├── physics.rs
│   │   │   └── random.rs  # Seeded RNG
│   │   └── Cargo.toml
│   │
│   ├── client/            # WASM + Native client
│   │   ├── src/
│   │   │   ├── lib.rs     # WASM entry point
│   │   │   ├── main.rs    # Native entry point
│   │   │   ├── renderer/  # wgpu rendering
│   │   │   ├── input/     # Input handling
│   │   │   └── network/   # WebTransport/WebSocket
│   │   └── Cargo.toml
│   │
│   └── protocol/          # Shared network protocol
│       ├── src/
│       │   ├── lib.rs
│       │   ├── messages.rs
│       │   └── codec.rs   # Binary serialization
│       └── Cargo.toml
│
├── web/                   # Browser shell
│   ├── index.html
│   └── bootstrap.js       # WASM loader
│
├── Cargo.toml             # Workspace root
└── README.md
```

## Key Crates

| Purpose | Crate | Version |
|---------|-------|---------|
| Graphics | `wgpu` | 24.x |
| Windowing | `winit` | 0.30.x |
| Math | `glam` | 0.29.x |
| WASM bindings | `wasm-bindgen` | 0.2.x |
| Web APIs | `web-sys` | 0.3.x |
| Async (WASM) | `wasm-bindgen-futures` | 0.4.x |
| Serialization | `bincode` | 2.x |
| Logging | `tracing` | 0.1.x |
| RNG | `rand` + `rand_chacha` | 0.8.x |

## Migration Path

### Phase 1: Core Simulation
- Port deterministic simulation logic
- Seeded RNG, fixed-point math where needed
- Entity system (arrays, not hashmaps for determinism)
- Unit tests to verify determinism

### Phase 2: Renderer
- Basic wgpu setup (WebGPU + WebGL2 fallback)
- Port shaders to WGSL
- Sprite rendering, camera system
- Match current visual fidelity

### Phase 3: Input & Game Loop
- winit event loop integration
- Input mapping system
- Fixed timestep game loop (30Hz simulation)

### Phase 4: Networking
- WebSocket client for Phoenix signaling
- WebTransport for P2P game traffic
- Port binary protocol from TypeScript
- Lockstep synchronization

### Phase 5: Integration
- Connect all systems
- Browser testing
- Performance optimization
- Native build verification

## Determinism Strategy

Same rules as TypeScript version:
1. **No `rand::thread_rng()`** - Use `ChaCha8Rng` with fixed seed
2. **No system time in simulation** - Frame counter only
3. **Careful with floats** - Consider fixed-point for critical paths
4. **Ordered iteration** - `Vec` not `HashMap` for entities
5. **No async in simulation** - Pure synchronous logic

## WebTransport vs WebRTC

Switching from WebRTC to WebTransport because:
- Simpler protocol (no ICE/STUN/TURN complexity)
- Native unreliable datagrams (perfect for inputs)
- Lower latency in practice
- Server-relayed model (scales better than pure P2P)

Trade-off: Requires a relay server, but we already have Phoenix.

## Open Questions

1. Keep Phoenix/Elixir server or rewrite in Rust?
   - Recommendation: Keep Phoenix initially, evaluate later

2. ECS framework or manual entity management?
   - Recommendation: Start manual, add `hecs` if needed

3. Asset pipeline?
   - Recommendation: Simple for now, evaluate `bevy_asset` later

## Next Steps

1. Scaffold project structure
2. Set up wgpu "hello triangle"
3. Port `SeededRandom` and basic simulation types
4. Iterate from there
