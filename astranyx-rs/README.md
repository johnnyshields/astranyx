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
│   ├── core/       # Deterministic game simulation
│   ├── protocol/   # Network message types
│   └── client/     # Renderer, input, networking
├── web/            # Browser shell (HTML/JS)
└── Cargo.toml      # Workspace root
```

## Prerequisites

### Rust Toolchain

```bash
# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Add WASM target
rustup target add wasm32-unknown-unknown

# Install wasm-pack (for WASM builds)
cargo install wasm-pack
```

### Optional: Native Build Dependencies

**Linux:**
```bash
sudo apt install libwayland-dev libxkbcommon-dev
```

**macOS:**
```bash
# Xcode command line tools
xcode-select --install
```

## Building

### Native (Vulkan/Metal/DX12)

```bash
cd astranyx-rs

# Debug build
cargo build

# Release build
cargo build --release

# Run
cargo run --release
```

### WASM (Browser)

```bash
cd astranyx-rs

# Build WASM package
wasm-pack build crates/client --target web --out-dir ../../pkg --features wasm --no-default-features

# Serve locally (requires a local server for WASM)
# Option 1: Python
python3 -m http.server 8080

# Option 2: Use any static file server
npx serve .
```

Then open http://localhost:8080/web/ in a WebGPU-capable browser.

## Testing

```bash
# Run all tests
cargo test

# Run specific crate tests
cargo test -p astranyx-core
cargo test -p astranyx-protocol
```

## Development

### Type Checking

```bash
cargo check
cargo clippy
```

### Documentation

```bash
cargo doc --open
```

## Controls

| Key | Action |
|-----|--------|
| W/↑ | Move up |
| S/↓ | Move down |
| A/← | Move left |
| D/→ | Move right |
| Space/Z | Fire |
| X/Ctrl | Special |
| Shift/C | Focus (slow/precise) |

## Browser Compatibility

WebGPU is required. Supported browsers:
- Chrome 113+
- Edge 113+
- Firefox Nightly (with `dom.webgpu.enabled = true`)
- Safari 17+ (macOS Sonoma+)

## Architecture

### Determinism

The simulation in `astranyx-core` is 100% deterministic for P2P lockstep:

1. **SeededRandom**: xorshift32 PRNG with fixed seed
2. **Frame-based timing**: No system time in simulation
3. **Ordered iteration**: `Vec` for entities, not `HashMap`
4. **Synchronous logic**: No async in simulation

### Networking

- **WebTransport**: UDP-like datagrams for low-latency game inputs
- **WebSocket**: Phoenix server connection for lobby/signaling
- **Lockstep**: Frame-synchronized input exchange between peers

## License

GPL-3.0
