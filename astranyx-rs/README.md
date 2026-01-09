# Astranyx (Rust)

Rust/WASM rewrite of Astranyx - a 2.5D multiplayer shoot-em-up game.

## Tech Stack

- **Graphics**: wgpu (WebGPU/Vulkan/Metal/DX12)
- **Windowing**: winit
- **Math**: glam (SIMD)
- **Networking**: WebTransport (game) + WebSocket (signaling)
- **Serialization**: bincode

## Project Structure

```
astranyx-rs/
├── crates/
│   ├── core/       # Deterministic game simulation (13 tests)
│   ├── protocol/   # Network message types (3 tests)
│   └── client/     # Renderer, input, networking
├── pkg/            # WASM build output (generated)
├── web/            # Browser shell (HTML/JS)
├── .cargo/         # Build configuration
└── Cargo.toml      # Workspace root
```

## Quick Start

### Windows (Native)

```powershell
# From WSL
cargo build --release --target x86_64-pc-windows-gnu

# Run the exe
./target/x86_64-pc-windows-gnu/release/astranyx.exe
```

Or double-click `C:\workspace\astranyx\astranyx-rs\target\x86_64-pc-windows-gnu\release\astranyx.exe`

### Browser (WASM)

```bash
# Build WASM
wasm-pack build crates/client --target web --out-dir ../../pkg --no-default-features --features wasm

# Serve locally
python3 -m http.server 8080

# Open in browser
# http://localhost:8080/web/
```

## Prerequisites

### Rust Toolchain

```bash
# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Add targets
rustup target add wasm32-unknown-unknown
rustup target add x86_64-pc-windows-gnu  # For Windows cross-compile

# Install tools
cargo install wasm-pack
```

### Cross-Compile to Windows (from Linux/WSL)

```bash
sudo apt install mingw-w64
```

## Building

### Native Linux

```bash
cargo build --release
./target/release/astranyx
```

### Native Windows (cross-compile from WSL)

```bash
cargo build --release --target x86_64-pc-windows-gnu
```

Output: `target/x86_64-pc-windows-gnu/release/astranyx.exe` (portable, no DLLs)

### WASM (Browser)

```bash
wasm-pack build crates/client --target web --out-dir ../../pkg --no-default-features --features wasm
```

Output: `pkg/astranyx_client.js` + `pkg/astranyx_client_bg.wasm`

## Testing

```bash
# Run all tests (16 total)
cargo test

# Run specific crate tests
cargo test -p astranyx-core      # 13 tests
cargo test -p astranyx-protocol  # 3 tests
```

## Development

```bash
cargo check          # Type check
cargo clippy         # Lint
cargo doc --open     # Generate docs
```

## Controls

| Key | Action |
|-----|--------|
| W / ↑ | Move up |
| S / ↓ | Move down |
| A / ← | Move left |
| D / → | Move right |
| Space / Z | Fire |
| X / Ctrl | Special |
| Shift / C | Focus (slow/precise) |

## Browser Compatibility

WebGPU required:
- Chrome 113+
- Edge 113+
- Firefox Nightly (`dom.webgpu.enabled = true`)
- Safari 17+ (macOS Sonoma+)

## Architecture

### Dual Target

Same codebase compiles to both native and WASM via feature flags:

```toml
[features]
default = ["native"]
native = ["pollster", "tracing-subscriber"]
wasm = ["wasm-bindgen", "web-sys", "js-sys", "tracing-wasm"]
```

### Determinism

The simulation in `astranyx-core` is 100% deterministic for P2P lockstep:

1. **SeededRandom**: xorshift32 PRNG with fixed seed
2. **Frame-based timing**: No system time in simulation
3. **Ordered iteration**: `Vec` for entities, not `HashMap`
4. **Synchronous logic**: No async in simulation

### Crates

| Crate | Purpose |
|-------|---------|
| `astranyx-core` | Deterministic simulation, entities, physics, RNG |
| `astranyx-protocol` | Network messages, binary codec |
| `astranyx-client` | wgpu renderer, winit windowing, input handling |

### Networking (Planned)

- **WebTransport**: UDP-like datagrams for low-latency game inputs
- **WebSocket**: Phoenix server connection for lobby/signaling
- **Lockstep**: Frame-synchronized input exchange between peers

## License

GPL-3.0
