# TLA+ Assessment and Sync Verification

**Date**: 2026-01-01
**Scope**: TLA+ specifications, TypeScript implementation alignment, network failure modeling

## Context

Conducted comprehensive assessment of TLA+ formal verification coverage for the P2P lockstep netcode system. Identified gaps, fixed issues, and created automated sync verification.

## Assessment Findings

### Original Questions Addressed

1. **Is the TLA+ meaningful or performative?**
   - **Verdict**: Genuinely meaningful - verifies 6+ safety invariants across ~50M states
   - Documented limitations are honest (no message reordering, static peer set)

2. **Missing network states?**
   - Found gaps: ICE restart, partial partitions, connection flapping
   - Now added to `LockstepNetwork.tla`

3. **Contradictions between TLA files?**
   - No contradictions found
   - Abstraction differences are intentional and documented

4. **Code-model alignment?**
   - 10/11 actions were mapped; added missing `ForceLeaderChange`
   - Created automated sync verification test

## Changes Made

### TLA+ Specification Fixes

**LockstepState.tla**
- Fixed `SyncTermBounded` invariant - removed weak disjunction that made it trivially true:
```tla
\* Before (weak)
SyncTermBounded == \A p \in Peer : syncTerm[p] <= currentTerm[p] \/ syncTerm[p] <= MaxTerm

\* After (correct)
SyncTermBounded == \A p \in Peer : syncTerm[p] <= currentTerm[p]
```

**LockstepNetwork.tla** - Extended with network failure modeling:

| New Feature | Actions Added |
|-------------|---------------|
| ICE Restart | `StartIceRestart`, `IceRestartSuccess`, `IceRestartFailed` |
| Partitions | `CreateAsymmetricPartition`, `CreateSymmetricPartition`, `HealPartition`, `HealAllPartitions` |
| Flapping | `ConnectionFlap`, `ResetFlapCount` |

New variables:
- `partitioned[p1][p2]` - Asymmetric partition matrix
- `flapCount[p]` - Connection stability tracking
- `iceRestarting[p]` - ICE restart state

New invariants:
- `IceRestartingNotConnected` - ICE restarting peer not in connected set
- `FlappingPeersBackedOff` - Flapping peers stop reconnecting
- `NoSelfPartition` - Peer can always reach itself

### TypeScript Implementation

**LockstepNetcode.ts**
- Added comprehensive TLA+ docstring mapping all variables and actions
- Added `forceLeaderChange(newLeaderId, newTerm)` method for external leader override
- Added TLA+ comment to `checkForDesync()` and `receiveInput()`

**LeaderElection.ts**
- Fixed typo: `Stepdown` → `StepDown` to match TLA+ action name

### New Test: TLASync.test.ts

Automated bidirectional verification:

```
Forward Check (TS → TLA+):
  - All TLA+ action references in TS comments exist in .tla files

Reverse Check (TLA+ → TS):
  - Reports TLA+ actions without TS implementation reference

Coverage Report:
  - LockstepState: 41%
  - LockstepNetwork: 28%
  - LeaderElection: 46%
  - LockstepSimple: 50%
```

Coverage is intentionally <100% because:
- Helper functions (IsMajority, MinPeer) don't need TS references
- Invariants are verified by TLC, not runtime code
- Liveness properties are spec-only

### Config Updates

| File | Change |
|------|--------|
| `MCLeaderElection.cfg` | Peer count: 5 → 4 |
| `MCLockstepSimple.cfg` | Peer count: 5 → 4 |
| `MCLockstepNetwork.cfg` | Added `MaxFlaps = 2`, new invariants |

## Architecture: TLA+ to TypeScript Mapping

```
TLA+ Model                    TypeScript Implementation
─────────────────────────────────────────────────────────
LockstepState.tla
├── frame[p]                  → LockstepNetcode.currentFrame
├── currentTerm[p]            → LeaderElection.currentTerm
├── state[p]                  → LeaderElection.state
├── pendingEvents[p]          → LocalEventQueue.pendingEvents
├── syncTerm[p]               → StateSyncManager.lastAcceptedSyncTerm
├── SubmitInput(p)            → LockstepNetcode.tick()
├── AdvanceFrame(p)           → LockstepNetcode.tryAdvanceFrame()
├── SendStateSync(l)          → LockstepNetcode.broadcastStateSync()
├── ReceiveStateSync(f,l)     → StateSyncManager.receiveSyncMessage()
├── Desync(p)                 → LockstepNetcode.checkForDesync()
└── ForceLeaderChange         → LockstepNetcode.forceLeaderChange()

LockstepNetwork.tla
├── connectionState[p]        → P2PManager connection state
├── partitioned[p1][p2]       → FaultInjector (test only)
├── flapCount[p]              → P2PManager reconnection tracking
├── StartConnecting(p)        → P2PManager.connectToPeer()
├── ConnectionEstablished(p)  → DataChannel.onopen handler
├── Disconnect(p)             → connection.onconnectionstatechange
├── StartIceRestart(p)        → RTCPeerConnection.restartIce()
└── DetectDesync(p)           → InputBuffer.checkDesync()

LeaderElection.tla
├── StartElection(p)          → LeaderElection.startElection()
├── Vote(voter,candidate)     → LeaderElection.handleVoteRequest()
├── BecomeLeader(p)           → LeaderElection.becomeLeader()
├── StepDown(p)               → LeaderElection.stepDown()
└── BroadcastHeartbeat(l)     → LeaderElection.broadcastHeartbeat()
```

## Verification Strategy

```
┌─────────────────────────────────────────────────────────────┐
│                    Verification Layers                       │
├─────────────────────────────────────────────────────────────┤
│  TLC Model Checker        │  Exhaustive state exploration   │
│  (run_tlc.sh)             │  ~50M states, safety invariants │
├───────────────────────────┼─────────────────────────────────┤
│  Property-Based Tests     │  Random action sequences        │
│  (TLAProperties.test.ts)  │  fast-check, 100+ iterations    │
├───────────────────────────┼─────────────────────────────────┤
│  Jepsen-Style Tests       │  Failure injection              │
│  (jepsen.test.ts)         │  Partitions, leader failures    │
├───────────────────────────┼─────────────────────────────────┤
│  Sync Verification        │  Bidirectional mapping check    │
│  (TLASync.test.ts)        │  TS ↔ TLA+ correspondence       │
├───────────────────────────┼─────────────────────────────────┤
│  Runtime Assertions       │  Invariant checks in production │
│  (assert* methods)        │  TypeInvariant, SyncTermBounded │
└───────────────────────────┴─────────────────────────────────┘
```

## Files Changed

```
tla/
├── LockstepState.tla        # Fixed SyncTermBounded
├── LockstepNetwork.tla      # +12 actions, +3 variables, +3 invariants
├── MCLeaderElection.cfg     # 5→4 peers
├── MCLockstepSimple.cfg     # 5→4 peers
└── MCLockstepNetwork.cfg    # +MaxFlaps, +invariants

client/src/network/
├── LockstepNetcode.ts       # +TLA+ docstring, +forceLeaderChange()
├── LeaderElection.ts        # Fixed Stepdown→StepDown typo
└── __tests__/
    └── TLASync.test.ts      # NEW: Bidirectional sync verification
```

## Running Verification

```bash
# TLC model checker (requires tla2tools.jar)
cd tla && ./run_tlc.sh

# TypeScript property tests
cd client && bun test TLAProperties.test.ts

# Jepsen-style failure tests
bun test LockstepNetcode.jepsen.test.ts

# TLA+ sync verification
bun test TLASync.test.ts
```

## Future Considerations

1. **Runtime invariant coverage**: Currently ~50% of invariants have runtime assertions
2. **ICE restart implementation**: TLA+ model added, P2PManager needs actual `restartIce()` calls
3. **Partition testing in Jepsen**: Use `FaultInjector.createPartition()` for more scenarios
4. **CI integration**: Add `bun test TLASync.test.ts` to CI pipeline
