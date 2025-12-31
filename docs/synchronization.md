# Multiplayer Synchronization

This document describes how Astranyx maintains synchronized game state across P2P multiplayer sessions.

## Overview

Astranyx uses a hybrid synchronization approach:

1. **Lockstep Input Sync**: All players exchange inputs every frame
2. **Owner-Authoritative Events**: Collision events are detected by the owning player
3. **Periodic State Sync**: Host broadcasts authoritative state to correct drift

## Lockstep Netcode

The core synchronization is deterministic lockstep:

```
Frame N:
  1. Capture local input
  2. Send input to all peers (targeting frame N + inputDelay)
  3. Wait for all peer inputs for frame N
  4. Simulate frame N with all inputs
  5. Advance to frame N+1
```

**Input Delay**: Default 3 frames. Hides network latency by scheduling inputs for future frames.

**Determinism Requirements**:
- No `Math.random()` - use `SeededRandom` class
- No `Date.now()` - use frame counter
- Fixed-point math for positions
- Arrays only (no object iteration order issues)

## Owner-Authoritative Events

Some game events are detected only by the "owning" player and broadcast to others:

| Event Type | Owner | Description |
|------------|-------|-------------|
| `damage` | Player being hit | Collision with enemy/bullet |
| `death` | Player dying | Lost all shields |
| `respawn` | Player respawning | After death timer |
| `pickup` | Player collecting | Powerup collision |
| `weapon_pickup` | Player collecting | Weapon drop collision |
| `enemy_damage` | Projectile owner | Bullet/beam/missile/orb hit enemy |

This prevents double-detection of the same collision on different clients.

### Enemy Damage Flow

When a player's projectile hits an enemy:
1. Only the projectile owner detects the collision
2. Owner emits `enemy_damage` event with new health and killed flag
3. Remote players receive event and apply the damage
4. This ensures consistent enemy health across all clients

## State Synchronization

### Why State Sync?

Even with deterministic simulation, desync can occur:
- Network packet timing differences
- Event application timing (input delay affects when events arrive)
- Floating-point edge cases
- Bug in determinism

### How It Works

1. **Host Selection**: Player with index 0 is the host
2. **Checksum Comparison**: Every 30 frames, players compare state checksums
3. **Sync Triggers**:
   - Checksum mismatch (immediate)
   - Periodic interval (every 300 frames / 5 seconds)

### Sync Flow

```
Host                              Non-Host
  |                                   |
  | [Detects sync needed]             |
  |                                   |
  |--- StateSyncMessage ------------->|
  |    {                              |
  |      type: 'state_sync',          |
  |      frame: 1234,                 | [1. Apply state]
  |      state: {...},                | [2. Re-apply pending events]
  |      checksum: 12345              |
  |    }                              |
  |                                   |
```

### Pending Events Buffer

Non-host players buffer their local events. When state sync arrives:

1. Save pending events
2. Apply authoritative state from host
3. Re-apply pending events

This preserves the local player's recent actions (pickups, etc.) that may not yet be reflected in the host's state.

## Checksum Algorithm

```typescript
getChecksum(): number {
  let hash = 0
  hash = (hash * 31 + frame) >>> 0
  hash = (hash * 31 + rngSeed) >>> 0

  for (player of players) {
    hash = (hash * 31 + player.x) >>> 0
    hash = (hash * 31 + player.y) >>> 0
    hash = (hash * 31 + player.shields) >>> 0
    hash = (hash * 31 + player.dead) >>> 0
    hash = (hash * 31 + player.lives) >>> 0
  }

  hash = (hash * 31 + enemies.length) >>> 0
  // First 5 enemy positions

  hash = (hash * 31 + bullets.length) >>> 0
  hash = (hash * 31 + powerups.length) >>> 0
  hash = (hash * 31 + weaponDrops.length) >>> 0
  hash = (hash * 31 + score) >>> 0

  return hash
}
```

## Configuration

### LockstepConfig

```typescript
interface LockstepConfig {
  inputDelay: number           // Frames of input delay (default: 3)
  playerCount: number          // Total players in game
  localPlayerId: string        // This client's player ID
  playerOrder: Map<string, number>  // Player ID -> index mapping
  stateSyncInterval?: number   // Frames between syncs (default: 300)
}
```

### Tuning

| Parameter | Default | Description |
|-----------|---------|-------------|
| `inputDelay` | 3 | Higher = more lag tolerance, lower = more responsive |
| `stateSyncInterval` | 300 | Lower = faster correction, higher = less bandwidth |
| Checksum frequency | 30 | How often to compare state |

## Debugging Desync

When desync is detected, detailed state is logged:

```typescript
getDebugState(): {
  frame: number
  rngSeed: number
  playerCount: number
  players: Array<{ id, x, y, shields, dead }>
  enemyCount: number
  bulletCount: number
  powerupCount: number
  weaponDropCount: number
  score: number
}
```

Compare this output between clients to identify what diverged.

## Message Types

### FrameInput
```typescript
interface FrameInput {
  frame: number
  playerId: string
  input: PlayerInput
  events?: GameEvent[]  // Owner-authoritative events
  checksum?: number     // For desync detection
}
```

### StateSyncMessage
```typescript
interface StateSyncMessage {
  type: 'state_sync'
  frame: number
  state: SerializedState  // Full game state
  checksum: number
}
```

## Best Practices

1. **Keep Simulation Deterministic**: Any non-determinism will cause desync
2. **Test with High Latency**: Use network simulation to test sync under poor conditions
3. **Log Desync Details**: When checksums mismatch, log full state for comparison
4. **Adjust Sync Interval**: Lower for action-heavy games, higher for turn-based
5. **Handle Visual Jumps**: State sync may cause brief visual discontinuity - consider interpolation
