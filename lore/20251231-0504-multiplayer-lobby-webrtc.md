# Multiplayer Lobby & WebRTC Integration

## Summary

Implemented the complete multiplayer flow connecting the client to the Phoenix server for lobby management and WebRTC peer-to-peer connections.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                         CLIENT                                   │
│                                                                  │
│  ┌──────────┐    ┌───────────────────┐    ┌───────────────────┐ │
│  │ LobbyUI  │◄───│ MultiplayerManager │───►│   PhoenixClient   │ │
│  │ (DOM)    │    │  (orchestrator)    │    │   (WebSocket)     │ │
│  └──────────┘    └─────────┬─────────┘    └─────────┬─────────┘ │
│                            │                        │            │
│                   ┌────────▼────────┐              │            │
│                   │   P2PManager    │◄─────────────┘            │
│                   │   (WebRTC)      │    signaling              │
│                   └────────┬────────┘                           │
│                            │                                     │
│                   ┌────────▼────────┐                           │
│                   │ LockstepNetcode │                           │
│                   │  (P2P sync)     │                           │
│                   └─────────────────┘                           │
└─────────────────────────────────────────────────────────────────┘
                             │
                    WebSocket (signaling)
                             │
┌─────────────────────────────────────────────────────────────────┐
│                         SERVER                                   │
│                                                                  │
│  ┌─────────────┐    ┌──────────────┐    ┌───────────────────┐  │
│  │ GameSocket  │───►│ RoomChannel  │───►│   Lobby GenServer │  │
│  └─────────────┘    └──────────────┘    └───────────────────┘  │
│         │                                                        │
│         └──────────►┌──────────────────┐                        │
│                     │ SignalingChannel │ (SDP/ICE relay)        │
│                     └──────────────────┘                        │
└─────────────────────────────────────────────────────────────────┘
```

## New Files

### Client

- `src/network/MultiplayerManager.ts` - Orchestrates the full multiplayer flow
  - State machine: disconnected → connecting → connected → joining_room → in_lobby → starting → connecting_peers → ready → playing
  - Coordinates PhoenixClient, P2PManager, and LockstepNetcode
  - Handles quickmatch (auto-create/join rooms)

- `src/ui/LobbyUI.ts` - DOM management for lobby screen
  - Room list view with quickmatch, create, join
  - Room waiting view with player list and start button
  - Connecting view with peer status

### HTML/CSS

- Added lobby screen to `index.html`
  - Quickmatch button
  - Room list with join on click
  - Room name input + create button
  - Player list with host indicator
  - Start game button (host only)
  - Peer connection status during setup

## Modified Files

### Server

- `lib/astranyx_web/channels/room_channel.ex`
  - Added `seed` to `game_starting` broadcast for deterministic simulation
  - Added `list_rooms` message handler for querying available rooms

### Client

- `src/network/PhoenixClient.ts`
  - Added `RoomInfo`, `RoomData`, `GameStartingData` interfaces
  - Added `listRooms()`, `startGame()`, `getCurrentRoom()`, `getSignalingChannel()`
  - Added event handlers: `onPlayerJoined`, `onPlayerLeft`, `onGameStarting`
  - Modified `joinRoom()` to accept `asHost` parameter

- `src/game/Game.ts`
  - Modified `startMultiplayer()` to accept `seed` parameter (was hardcoded 12345)
  - Hides title screen when starting multiplayer

- `src/core/Engine.ts`
  - Added `getGame()` method to expose game instance for wiring

- `src/main.ts`
  - Added multiplayer initialization after engine ready
  - Configurable server URL (via env var or auto-detect for production)
  - Wires LobbyUI callbacks to MultiplayerManager
  - Starts multiplayer game when all peers connected

## Flow

1. User clicks "ONLINE" button on title screen
2. Client connects to Phoenix server WebSocket
3. Lobby screen shows with quickmatch or manual room options
4. User creates or joins a room
5. Room waiting view shows connected players
6. Host clicks "START GAME"
7. Server broadcasts `game_starting` with player_order and seed
8. Clients establish WebRTC peer connections via signaling
9. When all peers connected, game starts with deterministic simulation

## Server URL Configuration

```typescript
// Checks in order:
// 1. VITE_SERVER_URL env variable
// 2. Production: same host as client (wss://host/socket)
// 3. Development: ws://localhost:4200/socket
```

## Dependencies Added

- `phoenix` (1.8.3) - Phoenix WebSocket client library

## Test Status

- Server tests: 2/2 passing
- Client typecheck: passing
