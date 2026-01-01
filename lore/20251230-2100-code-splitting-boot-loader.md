# Code Splitting & Boot Loader Implementation

## Summary

Implemented progressive loading and code splitting for the Astranyx client using Vite's native dynamic imports. No framework needed - just vanilla TypeScript with ES modules.

## Bundle Structure

The build now produces three chunks:

| Chunk | Size (gzip) | Contents |
|-------|-------------|----------|
| `index.js` | 1.74 KB | Boot loader, entry point |
| `Engine.js` | 6.39 KB | Renderer, Input, Engine |
| `Game.js` | 16.22 KB | Game, Simulation, all game logic |

**Total: ~24 KB gzipped** (down from single bundle)

## Architecture

```
main.ts (entry)
    │
    ▼
Boot.ts ─────► Early WebGL2 check
    │          Font loading
    │          Progress tracking
    │
    ▼ (dynamic import)
Engine.ts ────► Renderer init
    │           Input setup
    │
    ▼ (dynamic import)
Game.ts ──────► Simulation
                All game entities
                Weapons, waves, etc.
```

## New Files

### `src/boot/Boot.ts`
- Minimal initial loader
- WebGL2 support check
- Font preloading
- Progress callback system
- Error handling with styled messages

### `src/boot/AssetLoader.ts`
- Image/audio loading utilities
- Global asset cache
- Parallel loading with concurrency limit
- Progress reporting

### `src/boot/index.ts`
- Barrel export for boot module

## Key Changes

### `src/main.ts`
- Now imports only `Boot` (minimal)
- Uses Boot to lazy-load Engine
- Displays loading messages per phase

### `src/core/Engine.ts`
- Added `onProgress()` callback
- Game module now lazy-loaded via `import()`
- Reports init phases: renderer → input → game → ready

## Loading Flow

1. **Boot Phase** (index.js - 1.7KB)
   - Show "INITIALIZING..."
   - Check WebGL2 support
   - Wait for fonts
   - Dynamic import Engine

2. **Engine Phase** (Engine.js - 6.4KB)
   - Show "INITIALIZING RENDERER..."
   - Init WebGL2 context
   - Show "CONFIGURING INPUT..."
   - Setup keyboard/mouse/gamepad
   - Dynamic import Game

3. **Game Phase** (Game.js - 16KB)
   - Show "LOADING GAME..."
   - Init Simulation
   - Setup entities, weapons, waves
   - Show "READY"

4. **Start**
   - Hide loading screen
   - Begin game loop

## Benefits

1. **Faster Initial Load**: Only 1.7KB needed to show loading screen
2. **Better UX**: Progressive loading messages
3. **Error Resilience**: WebGL2 check before heavy downloads
4. **Future Ready**: AssetLoader ready for images/audio when needed
5. **No Framework**: Zero dependencies, just ES modules

## Usage

```typescript
import { Boot } from './boot/Boot.ts'

const boot = new Boot()

boot.onProgress((state) => {
  console.log(`${state.phase}: ${state.progress}%`)
})

const { Engine } = await boot.run()
const engine = new Engine(canvas)
await engine.init()
engine.start()
```

## Vite Config: WSL2 HMR Fix

Hot Module Reloading doesn't work in WSL2 when the project is on the Windows filesystem (`/mnt/c/...`) because Linux's `inotify` doesn't receive file change events from Windows.

**Solution**: Use polling, but only on WSL:

```typescript
// vite.config.ts
import { readFileSync, existsSync } from 'fs'

const isWSL = existsSync('/proc/version') &&
  readFileSync('/proc/version', 'utf-8').toLowerCase().includes('microsoft')

export default defineConfig({
  server: {
    watch: isWSL ? {
      usePolling: true,
      interval: 300,
    } : undefined,
  },
})
```

This auto-detects WSL and enables polling only when needed. Native Linux/macOS uses efficient inotify/FSEvents.

## Verification

- TypeScript: `bun run typecheck` ✓
- Tests: 396 passing ✓
- Build: Produces 3 chunks ✓
- HMR: Working on WSL2 ✓
