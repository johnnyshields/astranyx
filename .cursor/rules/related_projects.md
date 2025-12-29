# Related Projects

All paths relative to parent workspace directory.
- WSL: `/mnt/c/workspace/`
- Windows: `c:\workspace\`

## Astranyx Components

### client/
TypeScript game client with WebGL2 rendering.
- `src/core/` - Engine, Renderer, Input
- `src/game/` - Game state, Simulation
- `src/graphics/` - Shaders
- `src/network/` - Phoenix client, P2P, Lockstep netcode

### server/
Elixir Phoenix server for lobby and signaling.
- `lib/astranyx/game/` - Lobby management
- `lib/astranyx_web/channels/` - WebSocket channels

### legacy/
Reference game implementations.
- `delta-v.html` - Single-file 2D shoot-em-up (canvas-based)

### lore/
Implementation documentation and summaries.
