# Lockstep Netcode Refactoring - Complete Implementation

## Overview

Refactored the monolithic `LockstepNetcode` class into modular, testable components with Raft-inspired leader election, Jepsen-style failure tests, and TLA+ formal verification.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                  LockstepNetcode (Orchestrator)                 │
├─────────────────────────────────────────────────────────────────┤
│  ┌──────────────┐  ┌──────────────┐  ┌────────────────────┐    │
│  │ LocalEvent   │  │ LeaderElec-  │  │ StateSyncManager  │    │
│  │ Queue        │  │ tion         │  │                    │    │
│  ├──────────────┤  ├──────────────┤  ├────────────────────┤    │
│  │ 900-frame    │  │ Raft terms   │  │ 300-frame interval │    │
│  │ buffer       │  │ Voting       │  │ Desync detection   │    │
│  │ Re-apply     │  │ Heartbeats   │  │ Term validation    │    │
│  └──────────────┘  └──────────────┘  └────────────────────┘    │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                      InputBuffer                          │  │
│  │  Frame inputs • Checksum comparison • Ordered retrieval   │  │
│  └──────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

## New Files

### Core Components

| File | Lines | Purpose |
|------|-------|---------|
| `types.ts` | ~200 | Shared types: GameEvent, PlayerInput, NetMessage, election messages |
| `InputBuffer.ts` | ~180 | Frame input storage, checksum desync detection, deterministic ordering |
| `LocalEventQueue.ts` | ~200 | Event buffering (900 frames), re-application after sync |
| `StateSyncManager.ts` | ~150 | Periodic sync (300 frames), immediate sync on desync |
| `LeaderElection.ts` | ~570 | Raft-inspired: terms, voting, heartbeats, failover |

### Testing Infrastructure

| File | Lines | Purpose |
|------|-------|---------|
| `FaultInjection.ts` | ~300 | MockDataChannel, FaultInjector, partition/loss/delay simulation |
| `LockstepNetcode.jepsen.test.ts` | ~800 | 29 Jepsen-style tests for failure scenarios |

### Formal Verification

| File | Lines | Purpose |
|------|-------|---------|
| `LockstepNetcode.tla` | ~330 | TLA+ specification with safety/liveness properties |
| `MCLockstepNetcode.cfg` | ~25 | Model checker configuration |
| `run_tlc.sh` | ~30 | Script to run TLC |

## Key Design Decisions

### Leader Election (Raft-inspired)

```typescript
// Term-based voting prevents split-brain
private currentTerm = 0
private votedFor: string | null = null
private votesReceived: Set<string> = new Set()

// Majority required: floor(n/2) + 1
private getMajority(): number {
  return Math.floor(this.config.playerOrder.size / 2) + 1
}
```

- Initial leader: player with index 0
- Election triggered on leader disconnect or heartbeat timeout (1500ms)
- Heartbeat interval: 500ms (3 heartbeats before timeout)
- Higher term always wins; stale leaders step down

### Event Buffering

```typescript
// 900 frames = 15 seconds at 60fps
// Preserves local events across state sync for re-application
private pendingEvents: BufferedEvent[] = []

onStateSync(syncFrame: number): GameEvent[] {
  const eventsToReapply = this.getEventsForReapply()
  this.pendingEvents = []
  return eventsToReapply
}
```

### State Sync

- Periodic: every 300 frames (5 seconds)
- Immediate: on checksum mismatch (desync detected)
- Only leader sends sync; followers apply and re-apply local events

## Test Coverage

### Unit Tests
- InputBuffer: store, retrieve, ordered inputs, checksum detection, cleanup
- LocalEventQueue: buffering, filtering local/remote, re-apply after sync
- StateSyncManager: timing, desync flag, term validation
- LeaderElection: initial state, vote granting, vote rejection, term updates

### Jepsen-style Failure Scenarios
- **Network Partitions**: Asymmetric (one-way loss), symmetric (split-brain prevention)
- **Minority Partition**: Cannot elect leader without majority
- **Message Loss**: Random packet loss, burst loss
- **Leader Failures**: Disconnect triggers election, partition with term advance
- **State Sync Under Failure**: Lost sync recovered by retry, immediate sync on desync

### Safety Property Tests
- No two leaders in same term
- Term monotonically increases
- Events applied in deterministic order

## TLA+ Formal Model

### Safety Properties (Invariants)
```tla
NoTwoLeadersInSameTerm ==
    \A i, j \in Peer :
        (i # j /\ state[i] = "Leader" /\ state[j] = "Leader")
        => currentTerm[i] # currentTerm[j]

EventDurability ==
    [][Len(eventLog') >= Len(eventLog)]_eventLog

FrameMonotonicity ==
    \A p \in Peer : frame[p] >= 0
```

### Liveness Properties
```tla
EventuallyLeader ==
    <>(\E p \in Peer : state[p] = "Leader")

EventualFrameConvergence ==
    <>[](\A i, j \in Peer : ~partitioned[i][j] => frame[i] = frame[j])
```

## Usage

### Running Tests
```bash
cd client
bun test src/network/__tests__/LockstepNetcode.jepsen.test.ts
```

### Running TLA+ Model Checker
```bash
cd tla
./run_tlc.sh
```

Requires TLA+ tools (tla2tools.jar) from https://github.com/tlaplus/tlaplus/releases

## Configuration Defaults

```typescript
const DEFAULT_CONFIG = {
  inputDelay: 3,           // Frames of input delay
  stateSyncInterval: 300,  // 5 seconds at 60fps
  eventBufferSize: 900,    // 15 seconds at 60fps
  electionTimeout: 1500,   // 1.5 seconds
  heartbeatInterval: 500,  // 0.5 seconds
}
```

## Migration Notes

The refactored `LockstepNetcode` maintains backwards compatibility:
- Same public API (`tick`, `addPeer`, `removePeer`, `broadcastStateSync`, etc.)
- Re-exports types from `types.ts` for existing imports
- New methods: `setLeaderChangeHandler`, `setPeerDisconnectHandler`, `getCurrentTerm`, `getCurrentLeader`, `getDebugInfo`

## References

- MongoDB TLA+ Raft model: `secret/tla_plus/Replication/RaftMongo/`
- Jepsen analyses: https://jepsen.io/analyses
- Raft consensus: https://raft.github.io/
