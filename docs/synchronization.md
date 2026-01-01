# Multiplayer Synchronization

This document describes how Astranyx maintains synchronized game state across P2P multiplayer sessions.

## Overview

Astranyx uses a hybrid synchronization approach:

1. **Lockstep Input Sync**: All players exchange inputs every frame
2. **Owner-Authoritative Events**: Collision events are detected by the owning player
3. **Leader Election**: Raft-inspired consensus for leader selection
4. **Periodic State Sync**: Leader broadcasts authoritative state to correct drift

## Formal Verification (TLA+)

The lockstep netcode is formally verified using TLA+ model checking. The model is in `tla/LockstepNetcode.tla`.

### Verified Properties

| Property | Description |
|----------|-------------|
| `NoTwoLeadersInSameTerm` | At most one leader per election term (election safety) |
| `FrameBoundedDrift` | All peers stay within 1 frame of each other (lockstep safety) |
| `LeaderUpToDate` | Leader is at least as current as any other peer |
| `EventuallyLeader` | System always elects a leader (liveness) |

### TLA+ Actions → Implementation

| TLA+ Action | TypeScript Method | File |
|-------------|-------------------|------|
| `SubmitInput(p)` | `tick()` → `storeInput()` | `LockstepNetcode.ts` |
| `AdvanceFrame(p)` | `tryAdvanceFrame()` | `LockstepNetcode.ts` |
| `BroadcastHeartbeat(leader)` | `broadcastHeartbeat()` | `LeaderElection.ts` |
| `StartElection(p)` | `startElection()` | `LeaderElection.ts` |
| `Vote(voter, candidate)` | `handleVoteRequest()` | `LeaderElection.ts` |
| `BecomeLeader(p)` | `becomeLeader()` | `LeaderElection.ts` |
| `StepDown(p)` | `stepDown()` | `LeaderElection.ts` |

### Running the Model Checker

```bash
cd tla
./run_tlc.sh
```

The script uses hash-based caching - it skips if the spec hasn't changed since last successful run.

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

## Leader Election

Leader election uses a Raft-inspired consensus protocol.

### States

Each peer is in one of three states:

| State | Description |
|-------|-------------|
| `follower` | Follows the current leader, resets election timer on heartbeat |
| `candidate` | Requesting votes after election timeout |
| `leader` | Elected with majority, sends heartbeats, coordinates state sync |

### Election Flow

```
1. Initial: Peer with lowest index starts as leader
2. Timeout: If follower doesn't receive heartbeat, becomes candidate
3. Vote Request: Candidate increments term, votes for self, requests votes
4. Vote Grant: Peers grant vote if:
   - Candidate term >= peer term
   - Peer hasn't voted in this term (or voted for this candidate)
   - Candidate frame >= peer frame (log comparison)
5. Win: Candidate with majority becomes leader
6. Heartbeat: Leader sends periodic heartbeats to maintain authority
```

### Term

The `term` is a monotonically increasing election epoch. Higher terms have priority:
- Leader steps down if it sees a higher term
- Peers update their term when receiving messages with higher terms
- Ensures only one leader per term

### Configuration

| Parameter | Default | Description |
|-----------|---------|-------------|
| `electionTimeout` | 1500ms | Time before follower starts election |
| `heartbeatInterval` | 500ms | Leader heartbeat frequency |

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

1. **Leader Selection**: Via Raft-inspired election (player with lowest index initially)
2. **Checksum Comparison**: Every 30 frames, players compare state checksums
3. **Sync Triggers**:
   - Checksum mismatch (immediate)
   - Periodic interval (every 300 frames / 5 seconds)

### Sync Flow

```
Leader                            Follower
  |                                   |
  | [Detects sync needed]             |
  |                                   |
  |--- StateSyncMessage ------------->|
  |    {                              |
  |      type: 'state_sync',          |
  |      frame: 1234,                 | [1. Apply state]
  |      state: {...},                | [2. Re-apply pending events]
  |      checksum: 12345,             |
  |      term: 5                      | [3. Verify term authority]
  |    }                              |
  |                                   |
```

### Term Authority

State sync messages include the leader's term. Followers only accept syncs from the current term's leader, preventing stale leaders from overwriting state.

### Pending Events Buffer

Non-leader players buffer their local events. When state sync arrives:

1. Save pending events
2. Apply authoritative state from leader
3. Re-apply pending events

This preserves the local player's recent actions (pickups, etc.) that may not yet be reflected in the leader's state.

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
  electionTimeout?: number     // Ms before election timeout (default: 1500)
  heartbeatInterval?: number   // Ms between heartbeats (default: 500)
}
```

### Tuning

| Parameter | Default | Description |
|-----------|---------|-------------|
| `inputDelay` | 3 | Higher = more lag tolerance, lower = more responsive |
| `stateSyncInterval` | 300 | Lower = faster correction, higher = less bandwidth |
| `electionTimeout` | 1500ms | Lower = faster failover, higher = less false elections |
| `heartbeatInterval` | 500ms | Lower = faster detection, higher = less overhead |
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
  term: number           // Election term for authority
}
```

### Election Messages
```typescript
interface RequestVoteMessage {
  type: 'request_vote'
  term: number
  candidateId: string
  lastFrame: number      // For log comparison
}

interface VoteResponseMessage {
  type: 'vote_response'
  term: number
  voteGranted: boolean
  voterId: string
}

interface HeartbeatMessage {
  type: 'heartbeat'
  term: number
  leaderId: string
  frame: number
}
```

## Best Practices

1. **Keep Simulation Deterministic**: Any non-determinism will cause desync
2. **Test with High Latency**: Use network simulation to test sync under poor conditions
3. **Log Desync Details**: When checksums mismatch, log full state for comparison
4. **Adjust Sync Interval**: Lower for action-heavy games, higher for turn-based
5. **Handle Visual Jumps**: State sync may cause brief visual discontinuity - consider interpolation
6. **Run TLA+ Model**: After changing sync logic, verify with `./run_tlc.sh`
