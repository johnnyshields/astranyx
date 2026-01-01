@.cursor/rules/workflow.md
@.cursor/rules/commands.md
@.cursor/rules/project.md
@.cursor/rules/related_projects.md

## Project: Astranyx

2.5D multiplayer shoot-em-up game.

## Quick Start

```bash
# Terminal 1: Client
cd client && bun run dev

# Terminal 2: Server
cd server && mix phx.server
```

- Client: http://localhost:4100
- Server: http://localhost:4200

## Tech Stack

- **Client**: Bun + Vite + TypeScript + WebGL2
- **Server**: Elixir 1.19 + Phoenix 1.8
- **Networking**: P2P Lockstep (WebRTC) + Phoenix WebSocket (signaling)
