# Rust/WASM Scaffold Complete

**Date**: 2026-01-09
**Status**: Milestone Complete

## Summary

Successfully scaffolded a complete Rust/WASM game client that compiles to both native Windows executables and WebAssembly for browsers. The same codebase produces both targets with feature flags.

## What Was Built

### Crate Structure

```
astranyx-rs/
├── crates/
│   ├── core/           # Deterministic simulation (13 tests)
│   ├── protocol/       # Network messages (3 tests)
│   └── client/         # Renderer + platform glue
├── pkg/                # WASM output (generated)
├── web/                # Browser shell
└── Cargo.toml          # Workspace
```

### Core Crate (`astranyx-core`)

Ported from TypeScript, 100% deterministic:

- **`SeededRandom`** - xorshift32 PRNG (identical to TS version)
- **`PlayerInput`** - Bitflag input state (u16)
- **`Simulation`** - Game state, tick loop, entity management
- **`Entities`** - Player, Enemy, Projectile, PowerUp with types
- **`Physics`** - Circle collision, bounds clamping, lerp utilities

All types derive both `serde` and `bincode` traits for serialization.

### Protocol Crate (`astranyx-protocol`)

Network message definitions:

- `GameMessage` enum - Input, InputBatch, Heartbeat, SyncRequest, etc.
- `SignalingMessage` enum - Room management, WebRTC signaling
- Binary codec with bincode for compact encoding

### Client Crate (`astranyx-client`)

Dual-target renderer:

- **wgpu** - WebGPU on browsers, Vulkan/DX12/Metal on native
- **winit** - Cross-platform windowing
- Feature flags: `native` (default) vs `wasm`
- Basic triangle render pipeline (scaffold)

## Build Targets

### Native Windows

```bash
cargo build --release --target x86_64-pc-windows-gnu
```

Output: `target/x86_64-pc-windows-gnu/release/astranyx.exe` (~9MB portable)

Static linking enabled via `.cargo/config.toml`:
```toml
[target.x86_64-pc-windows-gnu]
rustflags = ["-C", "target-feature=+crt-static"]
```

### WebAssembly

```bash
wasm-pack build crates/client --target web --out-dir ../../pkg --no-default-features --features wasm
```

Output: `pkg/astranyx_client.js` + `pkg/astranyx_client_bg.wasm`

Serve with: `python3 -m http.server 8080`, open `http://localhost:8080/web/`

## Key Decisions

### bincode 2.0 with serde

Used `#[bincode(with_serde)]` attribute for `glam::Vec2` fields since glam doesn't implement bincode's native `Encode`/`Decode` traits but does implement serde.

### Platform-Specific Limits

```rust
let limits = if cfg!(target_arch = "wasm32") {
    wgpu::Limits::downlevel_webgl2_defaults()  // 2048 max texture
} else {
    wgpu::Limits::default()  // 8192+ max texture
};
```

### Error Handling in WASM

wgpu's `RequestDeviceError` doesn't implement `Sync` on WASM, so can't use `?` directly with anyhow. Fixed with:
```rust
.map_err(|e| anyhow::anyhow!("Failed to request device: {e}"))?
```

## Test Results

```
astranyx-core: 13 tests passed
  - simulation_determinism
  - state_serialization_roundtrip
  - input_flags, axis_values
  - circle_collision, bounds_clamping, move_towards_value
  - deterministic_sequence, different_seeds_different_sequence
  - next_int_bounds, next_range_bounds, shuffle_preserves_elements
  - zero_seed_handled

astranyx-protocol: 3 tests passed
  - roundtrip_input
  - roundtrip_heartbeat
  - compact_encoding
```

## Dependencies

| Purpose | Crate | Version |
|---------|-------|---------|
| Graphics | wgpu | 24.x |
| Windowing | winit | 0.30.x |
| Math | glam | 0.29.x |
| Serialization | bincode | 2.0.0-rc.3 |
| WASM bindings | wasm-bindgen | 0.2.x |
| Logging | tracing | 0.1.x |

## Next Steps

1. **Sprite rendering** - Replace triangle with textured quads
2. **Camera/projection** - Orthographic 2D with scrolling
3. **Game loop** - Connect Simulation to renderer
4. **Input wiring** - Keyboard → PlayerInput
5. **Networking** - WebSocket for Phoenix, WebTransport for game

## Files Changed

- Created: `astranyx-rs/` entire directory structure
- Created: `lore/20260109-1003-rust-wasm-rewrite-plan.md` (planning doc)
