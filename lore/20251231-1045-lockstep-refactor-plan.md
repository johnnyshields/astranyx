# Lockstep Netcode Refactoring - COMPLETED

## Summary

Refactored the monolithic `LockstepNetcode` class into modular components with leader election, Jepsen-style failure tests, and TLA+ formal verification. All 10 tasks completed successfully.

## Context

The current implementation has:
- Owner-authoritative events for damage, pickups, enemy damage
- Periodic state sync (every 300 frames / 5 seconds)
- Immediate sync on checksum mismatch
- Pending events buffer for re-application after sync

## Planned Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     LockstepNetcode (Orchestrator)              │
├─────────────────────────────────────────────────────────────────┤
│  ┌──────────────┐  ┌──────────────┐  ┌────────────────────┐    │
│  │ LocalEvent   │  │ LeaderElection│  │ StateSyncManager  │    │
│  │ Queue        │  │              │  │                    │    │
│  ├──────────────┤  ├──────────────┤  ├────────────────────┤    │
│  │ pendingEvents│  │ currentTerm  │  │ lastSyncFrame      │    │
│  │ confirmedEvts│  │ currentLeader│  │ pendingLocalEvents │    │
│  │ eventLog     │  │ voteCount    │  │ syncInterval       │    │
│  └──────────────┘  │ heartbeatTimer│  └────────────────────┘    │
│                    └──────────────┘                             │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                    InputBuffer                            │  │
│  │  frameInputs: Map<frame, Map<playerId, FrameInput>>      │  │
│  │  checksumBuffer: Map<frame, Map<playerId, checksum>>     │  │
│  └──────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

## Configuration (User Confirmed)

| Setting | Value | Rationale |
|---------|-------|-----------|
| Event buffer size | 900 frames (~15 seconds) | Enough for recovery + debugging |
| Election timeout | 1500ms | Standard Raft timeout |
| Heartbeat interval | 500ms | 3 heartbeats before timeout |
| Minimum players | 1 (solo continue) | Others can rejoin |
| Oplog depth | Event buffer only | Simpler than full oplog replay |

## Implementation Tasks

1. **Create shared types.ts** - GameEvent and message types (IN PROGRESS)
2. **Extract InputBuffer class** - Frame input management
3. **Extract LocalEventQueue class** - Event buffering with 900-frame buffer
4. **Extract StateSyncManager class** - Sync coordination
5. **Implement LeaderElection class** - Raft-style with terms
6. **Refactor LockstepNetcode** - Use extracted classes
7. **Add leader failover** - Handle disconnects, trigger elections
8. **Create FaultInjection** - Test infrastructure
9. **Write Jepsen-style tests** - Partition, loss, failover scenarios
10. **Write TLA+ formal model** - Safety and liveness properties

## New Files to Create

```
client/src/network/
├── types.ts              # Shared types (GameEvent, PlayerInput, etc.)
├── InputBuffer.ts        # Frame input management
├── LocalEventQueue.ts    # Event buffering (~15 seconds)
├── StateSyncManager.ts   # State sync coordination
├── LeaderElection.ts     # Raft-inspired leader election
└── __tests__/
    ├── FaultInjection.ts           # Network fault simulation
    ├── LockstepNetcode.jepsen.test.ts  # Failure scenario tests
    └── LeaderElection.test.ts      # Election tests

tla/
├── LockstepNetcode.tla   # Main TLA+ spec
└── MCLockstepNetcode.tla # Model checker config
```

## Key Design Decisions

### Leader Election (Raft-inspired)
- Term-based voting prevents split-brain
- Player index 0 is initial leader
- Election triggered when leader disconnects or heartbeat timeout
- Only leader sends state sync

### Local Event Queue
- 900-frame buffer (~15 seconds at 60fps)
- Events preserved across state sync
- Re-applied after receiving authoritative state

### State Sync
- Periodic every 300 frames (5 seconds)
- Immediate on checksum desync
- Non-hosts buffer local events for re-application

## Implementation Complete

All tasks completed:

1. **types.ts** - Shared types for GameEvent, PlayerInput, NetMessage, election messages
2. **InputBuffer.ts** - Frame input management with checksum desync detection
3. **LocalEventQueue.ts** - Event buffering with 900-frame buffer (~15 seconds)
4. **StateSyncManager.ts** - Periodic and on-demand state synchronization
5. **LeaderElection.ts** - Raft-inspired leader election with terms, voting, heartbeats
6. **LockstepNetcode.ts** - Refactored to use extracted components
7. **FaultInjection.ts** - Network fault simulation (partitions, loss, delay, reordering)
8. **LockstepNetcode.jepsen.test.ts** - 29 Jepsen-style tests covering failure scenarios
9. **LockstepNetcode.tla** - TLA+ formal specification with safety properties
10. **MCLockstepNetcode.cfg** - Model checker configuration

## Test Results

```
29 pass, 0 fail
69 expect() calls
```

Tests cover:
- InputBuffer operations and desync detection
- LocalEventQueue buffering and filtering
- StateSyncManager timing and term validation
- LeaderElection voting, heartbeats, term updates
- Network partition scenarios (symmetric/asymmetric)
- Message loss (random, burst)
- Leader failures and elections
- Safety properties (no two leaders per term, monotonic terms)
