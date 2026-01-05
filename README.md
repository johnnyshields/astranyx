# Astranyx

Multiplayer shoot-em-up game, inspired by popular arcade and console space shooters.

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

## Sponsorship

Astranyx is a free-to-play game and a non-commercial project. My goal is to have fun,
learn, and build the open--**not** to make money. I don't intend to enshittify the
game with ads, micro-transactions, paywalls, spam, etc.

If you'd like to give me a [Github Sponsorship ❤️](https://github.com/sponsors/johnnyshields),
I'll invest it back 100% into improving and running the game.

## License

Astranyx is libre software licensed under the GPL (code), CC-BY-SA (assets), and OFL (fonts).
Refer to [LICENSE](LICENSE) for details.

## Contributing

You're welcome to raise a pull request for any part of the project you'd like to improve!
By submitting a pull request, you agree to our [Contributor License Agreement (CLA)](CONTRIBUTOR_AGREEMENT).
Under the CLA, you confirm that the work is your own and grant permission for its use in Astranyx.

Reporting an issue does **not** invoke or require the Contributor License Agreement.
