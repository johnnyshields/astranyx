# Rust/WASM CI and Browser Fixes

**Date**: 2026-01-09
**Status**: Complete

## Summary

Added multi-platform CI build targets and fixed WASM browser rendering issues.

## GitHub Actions CI

Created `.github/workflows/rust.yml` with:

### Jobs
- **test**: Runs all 16 tests on ubuntu-latest
- **lint**: Checks formatting (rustfmt) and lints (clippy)
- **build**: Matrix builds for 6 native targets
- **build-wasm**: Builds WASM package
- **release**: Collects artifacts (on master push)

### Build Targets

| Platform | Architecture | Target | Runner |
|----------|--------------|--------|--------|
| Windows | x64 | `x86_64-pc-windows-msvc` | windows-latest |
| Windows | ARM64 | `aarch64-pc-windows-msvc` | windows-latest |
| Linux | x64 | `x86_64-unknown-linux-gnu` | ubuntu-latest |
| Linux | ARM64 | `aarch64-unknown-linux-gnu` | ubuntu-latest (cross) |
| macOS | x64 (Intel) | `x86_64-apple-darwin` | macos-latest |
| macOS | ARM64 (Apple Silicon) | `aarch64-apple-darwin` | macos-latest |
| WASM | - | `wasm32-unknown-unknown` | ubuntu-latest |

### Notes
- Intel Macs kept for compatibility (last sold ~2020-2022, still in use)
- Linux ARM64 uses cross-compilation with `gcc-aarch64-linux-gnu`
- Static linking enabled for portable Windows binaries
- Triggers only on `astranyx-rs/**` path changes

## WASM Browser Fixes

### Problem
Rainbow triangle only appeared after window resize - initial render showed solid crimson.

### Root Cause
On WASM, `window.inner_size()` returns 0x0 when the renderer initializes because the canvas sizing happens asynchronously.

### Solution
1. Set canvas dimensions from DOM rect before creating window:
```rust
let dpr = window.device_pixel_ratio();
let rect = canvas.get_bounding_client_rect();
canvas.set_width((rect.width() * dpr) as u32);
canvas.set_height((rect.height() * dpr) as u32);
```

2. Trigger resize when renderer attaches to app:
```rust
if let Some(mut renderer) = r.borrow_mut().take() {
    if let Some(window) = &self.window {
        let size = window.inner_size();
        if size.width > 0 && size.height > 0 {
            renderer.resize(size);
        }
    }
    self.renderer = Some(renderer);
}
```

### Files Changed
- `crates/client/src/wasm.rs` - Canvas sizing and initial resize
- `crates/client/Cargo.toml` - Added `DomRect` web-sys feature
- `.cargo/config.toml` - Cross-compile linker configs
- `rust-toolchain.toml` - All 7 build targets

## Configuration Files

### `.cargo/config.toml`
```toml
# Windows static linking
[target.x86_64-pc-windows-gnu]
rustflags = ["-C", "target-feature=+crt-static"]

[target.x86_64-pc-windows-msvc]
rustflags = ["-C", "target-feature=+crt-static"]

[target.aarch64-pc-windows-msvc]
rustflags = ["-C", "target-feature=+crt-static"]

# Linux ARM64 cross-compile
[target.aarch64-unknown-linux-gnu]
linker = "aarch64-linux-gnu-gcc"
```

### `rust-toolchain.toml`
```toml
[toolchain]
channel = "stable"
components = ["rustfmt", "clippy"]
targets = [
    "wasm32-unknown-unknown",
    "x86_64-pc-windows-gnu",
    "aarch64-pc-windows-msvc",
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "x86_64-apple-darwin",
    "aarch64-apple-darwin",
]
```

## Testing Status

- Native Windows: Working (rainbow triangle renders)
- WASM Chrome: Working after fixes (rainbow triangle renders)
- CI: Not yet tested (workflow created)
