# Project: Astranyx

2.5D multiplayer shoot-em-up game.

## Inspirations

Inspired by popular arcade and console shooters:
- R-Type
- Gradius / Parodius
- Einhänder
- Ikaruga
- Radiant Silvergun
- Starfox
- Rogue Squadron

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
         │       Binary protocol (30Hz sim)      │
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

### Network Optimizations (SC2-inspired)

- **Binary Protocol**: 95% bandwidth reduction (6B vs 120B per input)
- **Input Batching**: Adaptive batching based on RTT (1-4 inputs per packet)
- **Dynamic Input Delay**: 2-6 ticks based on measured latency
- **RTT Measurement**: Via heartbeat timestamps for accurate latency tracking

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
- **`MessageCodec`** - Binary protocol encoder/decoder (95% bandwidth reduction)
- **`InputBatcher`** - Adaptive input batching based on RTT
- **`InputDelayController`** - Dynamic input delay from measured latency
- **`LeaderElection`** - Raft-inspired leader election with RTT measurement

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
mix deps.get          # Install dependencies
mix phx.server        # Start server (port 4200)
mix test              # Run tests
```

## Ports

| Service | Port |
|---------|------|
| Vite (client) | 4100 |
| Phoenix (server) | 4200 |
| Coturn TURN/STUN | 3478 |

## TURN Server (Coturn)

WebRTC requires a TURN server for NAT traversal. Uses ephemeral credentials (HMAC-SHA1).

**Docker (development):**
```bash
docker run -d --network=host coturn/coturn \
  -n --log-file=stdout \
  --realm=astranyx \
  --use-auth-secret \
  --static-auth-secret=dev-secret-123
```

**Environment variables (server):**
```bash
TURN_SECRET=dev-secret-123          # Must match Coturn static-auth-secret
TURN_URLS=turn:localhost:3478       # Comma-separated for multiple
```

Credentials are generated server-side and provided to clients only when a game starts.
See `/docs/deployment.md` for production setup.

## Design Influences

- **R-Type** - Force pod system, horizontal scrolling
- **Einhänder** - 2.5D aesthetic, weapon attachments
- **Gradius** - Option drones, power-up bar
- **Ikaruga** - Polarity system, chain combos
- **Radiant Silvergun** - Weapon chaining, scoring depth
- **Bruno Simon** - Polished WebGL aesthetic
