# Astranyx

2.5D multiplayer shoot-em-up game inspired by R-Type, Einhänder, Gradius, Ikaruga, and Radiant Silvergun.

## Tech Stack

- **Client**: Bun + Vite + TypeScript + WebGL2
- **Server**: Elixir 1.19 + Phoenix 1.8
- **Networking**: P2P Lockstep (WebRTC) + Phoenix WebSocket (signaling)

## Quick Start

### Prerequisites

- [Bun](https://bun.sh/) (latest)
- [Elixir](https://elixir-lang.org/) 1.15+ with Erlang/OTP 28

### Running the Project

**Terminal 1 - Client:**
```bash
cd client
bun install
bun run dev
```

**Terminal 2 - Server:**
```bash
cd server
mix deps.get
mix phx.server
```

### Access

| Service | URL |
|---------|-----|
| Client | http://localhost:4100 |
| Server | http://localhost:4200 |

## Development Commands

### Client

```bash
cd client
bun run dev           # Start Vite dev server
bun run build         # Production build
bun run typecheck     # TypeScript type check
bun run lint          # ESLint
bun run test          # Run tests
bun run test:coverage # Tests with coverage
```

### Server

```bash
cd server
mix deps.get          # Install dependencies
mix phx.server        # Start Phoenix server
mix format            # Format code
mix credo --strict    # Static analysis
mix test              # Run tests
iex -S mix phx.server # Interactive mode
```

### TLA+ Model Checking

```bash
cd tla
./run_tlc.sh          # Run TLC model checker
```

## Architecture

P2P Lockstep netcode - game simulation runs entirely on clients.

```
Client A <══════════════════════════════════════> Client B
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

## Project Structure

```
astranyx/
├── client/           # TypeScript game client
│   └── src/
│       ├── core/     # Engine, Renderer, Input
│       ├── game/     # Game state, Simulation
│       ├── graphics/ # Shaders
│       └── network/  # Phoenix client, P2P, Lockstep
├── server/           # Elixir Phoenix server
│   └── lib/
│       ├── astranyx/         # Lobby management
│       └── astranyx_web/     # WebSocket channels
├── tla/              # TLA+ specifications
├── legacy/           # Reference implementations
└── lore/             # Implementation docs
```

## CI

GitHub Actions runs on every PR and push to main:

| Job | Description |
|-----|-------------|
| `client_lint` | ESLint + TypeScript type check |
| `client_test` | Vitest with coverage |
| `client_build` | Production build |
| `server_lint` | `mix format --check-formatted` + Credo |
| `server_test` | `mix test` |
| `tla_check` | TLC model checker for LockstepNetcode.tla |

## TURN Server (Development)

For WebRTC NAT traversal:

```bash
docker run -d --network=host coturn/coturn \
  -n --log-file=stdout \
  --realm=astranyx \
  --use-auth-secret \
  --static-auth-secret=dev-secret-123
```

Set server environment variables:
```bash
TURN_SECRET=dev-secret-123
TURN_URLS=turn:localhost:3478
```
