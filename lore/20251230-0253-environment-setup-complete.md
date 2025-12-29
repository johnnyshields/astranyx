# Astranyx Environment Setup Complete

## Summary

Full development environment established for Astranyx, a 2.5D multiplayer shoot-em-up game.

## Architecture

```
┌─────────────────┐                    ┌─────────────────┐
│    Client A     │                    │    Client B     │
│  ┌───────────┐  │                    │  ┌───────────┐  │
│  │Game Engine│  │◄══ WebRTC P2P ════►│  │Game Engine│  │
│  │ (TS/WebGL)│  │   (inputs only)    │  │ (TS/WebGL)│  │
│  └───────────┘  │                    │  └───────────┘  │
└────────┬────────┘                    └────────┬────────┘
         │                                      │
         │ WebSocket (signaling only)           │
         └──────────────┬───────────────────────┘
                        ▼
              ┌─────────────────┐
              │  Phoenix Server │
              │  - Lobby        │
              │  - Matchmaking  │
              │  - WebRTC SDP   │
              └─────────────────┘
```

## Tech Stack

| Layer | Technology | Version |
|-------|------------|---------|
| Client Runtime | Bun | 1.2.20 |
| Client Build | Vite | 7.x |
| Client Language | TypeScript | 5.9 |
| Client Graphics | WebGL2 | - |
| Server Runtime | Erlang/OTP | 28.3 |
| Server Language | Elixir | 1.19.4 |
| Server Framework | Phoenix | 1.8.3 |
| Version Manager | asdf | 0.15.0 |

## Ports

| Service | Port |
|---------|------|
| Vite (client) | 4100 |
| Phoenix (server) | 4200 |

## Client Structure

```
client/
├── src/
│   ├── main.ts                 # Entry point
│   ├── core/
│   │   ├── Engine.ts           # Game loop (60Hz fixed timestep)
│   │   ├── Renderer.ts         # WebGL2 with orthographic projection
│   │   └── Input.ts            # Keyboard + gamepad
│   ├── game/
│   │   ├── Game.ts             # State machine, rendering
│   │   └── Simulation.ts       # Deterministic simulation (P2P sync)
│   ├── graphics/
│   │   ├── shaderUtils.ts      # Shader compilation
│   │   └── shaders/
│   │       └── basic.ts        # Vertex + fragment shaders
│   └── network/
│       ├── PhoenixClient.ts    # WebSocket for lobby
│       ├── P2PManager.ts       # WebRTC peer connections
│       ├── LockstepNetcode.ts  # Frame synchronization
│       └── NetworkManager.ts   # High-level networking (unused)
│       └── WebRTCClient.ts     # Low-level WebRTC (unused)
├── public/assets/              # Static assets
├── index.html
├── package.json
├── tsconfig.json
└── vite.config.ts
```

## Server Structure

```
server/
├── lib/
│   ├── astranyx/
│   │   ├── application.ex      # OTP supervisor
│   │   └── game/
│   │       └── lobby.ex        # Room management GenServer
│   └── astranyx_web/
│       ├── endpoint.ex         # Phoenix endpoint
│       ├── router.ex
│       └── channels/
│           ├── game_socket.ex       # Main socket
│           ├── room_channel.ex      # Lobby coordination
│           └── signaling_channel.ex # WebRTC SDP/ICE relay
├── config/
│   ├── config.exs
│   ├── dev.exs                 # Port 4200
│   └── prod.exs
└── mix.exs
```

## Key Design Decisions

### P2P Lockstep (not Server-Authoritative)
- Game simulation runs entirely on clients
- Clients exchange inputs via WebRTC DataChannels
- Server only handles lobby/matchmaking/signaling
- Reduces server costs, enables low-latency gameplay

### Deterministic Simulation
- Fixed-point math (16.16 format) for positions
- Seeded PRNG (xorshift32) for randomness
- Consistent iteration order (arrays, not maps)
- No async operations in simulation

### Input Delay
- 3-frame input delay hides network latency
- Inputs tagged for future frame, sent immediately
- Simulation waits for all peer inputs before advancing

## Configuration Files Updated

- `.cursor/rules/project.md` - Project overview
- `.cursor/rules/workflow.md` - Determinism rules
- `.cursor/rules/commands.md` - Dev commands
- `.cursor/rules/related_projects.md` - Components
- `.claude/commands/*` - Updated for TS/Elixir
- `CLAUDE.md` - Quick start
- `.tool-versions` - asdf versions

## Running the Project

```bash
# Terminal 1: Client
cd client && bun run dev

# Terminal 2: Server
cd server && source ~/.asdf/asdf.sh && mix phx.server
```

Open http://localhost:4100 - starts in single-player mode.

## What Works

- WebGL2 rendering with shaders
- Player movement (WASD/Arrows)
- Shooting (Space)
- Enemy spawning
- Collision detection
- Health/damage system
- Starfield background
- Fixed timestep game loop

## Next Steps

1. **Lobby UI** - Create/join rooms
2. **Connection flow** - Full P2P handshake
3. **Multiplayer testing** - Two browser windows
4. **More enemy types** - Patterns, bosses
5. **Power-ups** - Weapons, shields
6. **Audio** - Web Audio API
7. **3D models** - Procedural ship geometry

## Design Influences

- **R-Type** - Force pod, horizontal scrolling
- **Einhänder** - 2.5D aesthetic, weapon pickups
- **Gradius** - Option drones, power-up bar
- **Ikaruga** - Polarity system, chain combos
- **Radiant Silvergun** - Weapon chaining, scoring
- **Bruno Simon** - Polished WebGL aesthetic
