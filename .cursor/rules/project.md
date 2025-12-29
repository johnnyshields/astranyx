# Project: Astranyx

2.5D multiplayer shoot-em-up game inspired by R-Type, Einhänder, Gradius, Ikaruga, and Radiant Silvergun.

## Tech Stack

### Client (`/client`)
- **Runtime**: Bun (dev tooling only, browser runs vanilla JS)
- **Build**: Vite 7.x
- **Language**: TypeScript (strict mode)
- **Graphics**: Raw WebGL2 (no framework)
- **Networking**: Phoenix WebSocket (lobby) + WebRTC DataChannel (game)

### Server (`/server`)
- **Runtime**: Erlang/OTP 28
- **Language**: Elixir 1.19
- **Framework**: Phoenix 1.8
- **Purpose**: Lobby, matchmaking, WebRTC signaling (NO game simulation)

## Architecture

**P2P Lockstep Netcode** - Game simulation runs entirely on clients.

```
Client A ◄══════════════════════════════════════► Client B
         │       WebRTC DataChannel (P2P)        │
         │       (inputs only, 60Hz)             │
         │                                       │
         │       Deterministic Simulation        │
         │       (same on both clients)          │
         └────────────────┬──────────────────────┘
                          │
                          │ WebSocket (signaling)
                          ▼
                   Phoenix Server
                   (lobby only)
```

## Directory Structure

```
astranyx/
├── client/
│   ├── src/
│   │   ├── core/           # Engine, Renderer, Input
│   │   ├── game/           # Game, Simulation
│   │   ├── graphics/       # Shaders
│   │   └── network/        # Phoenix, P2P, Lockstep
│   ├── public/assets/      # Static assets
│   └── package.json
├── server/
│   ├── lib/
│   │   ├── astranyx/       # Core logic
│   │   │   └── game/       # Lobby
│   │   └── astranyx_web/   # Phoenix web
│   │       └── channels/   # Socket, signaling
│   └── mix.exs
├── legacy/                 # Reference game (delta-v.html)
└── lore/                   # Implementation docs
```

## Key Modules

### Client

- **`Simulation`** - Deterministic game simulation (fixed-point math, seeded RNG)
- **`LockstepNetcode`** - Frame synchronization, input exchange
- **`P2PManager`** - WebRTC peer connections
- **`PhoenixClient`** - Lobby/signaling via WebSocket

### Server

- **`Astranyx.Game.Lobby`** - Room management GenServer
- **`AstranyxWeb.RoomChannel`** - Room join/leave, game start
- **`AstranyxWeb.SignalingChannel`** - WebRTC SDP/ICE relay

## Commands

### Client
```bash
cd client
bun install           # Install dependencies
bun run dev           # Start dev server (port 4100)
bun run build         # Production build
bun run typecheck     # Type check
```

### Server
```bash
cd server
source ~/.asdf/asdf.sh
mix deps.get          # Install dependencies
mix phx.server        # Start server (port 4200)
mix test              # Run tests
```

## Ports

| Service | Port |
|---------|------|
| Vite (client) | 4100 |
| Phoenix (server) | 4200 |

## Design Influences

- **R-Type** - Force pod system, horizontal scrolling
- **Einhänder** - 2.5D aesthetic, weapon attachments
- **Gradius** - Option drones, power-up bar
- **Ikaruga** - Polarity system, chain combos
- **Radiant Silvergun** - Weapon chaining, scoring depth
- **Bruno Simon** - Polished WebGL aesthetic
