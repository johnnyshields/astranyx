# TLA+ Model Improvements and TypeScript Integration

## Summary

Comprehensive improvements to the TLA+ formal verification models for lockstep netcode, including file reorganization, new networking model, and runtime invariant checks in TypeScript.

## TLA+ File Reorganization

Renamed files for clarity:

| Old Name | New Name | Purpose |
|----------|----------|---------|
| `LockstepCore.tla` | `LockstepSimple.tla` | Fast verification (~1M states) |
| `LockstepFull.tla` | `LockstepState.tla` | State sync, events, leader authority |
| (new) | `LockstepNetwork.tla` | Messages, connections, peer lifecycle |

## New: LockstepNetwork.tla

Created new TLA+ model covering networking aspects not in other models:

```tla
\* Variables
connectionState    \* "disconnected" | "connecting" | "connected"
network            \* Set of in-flight messages
inputBuffer        \* peer -> frame -> has_input
checksums          \* peer -> frame -> checksum
desynced           \* Whether peer detected desync

\* Key Actions
StartConnecting(p)       \* Initiate WebRTC handshake
ConnectionEstablished(p) \* DataChannel.onopen
Disconnect(p)            \* Connection failure
SendInput(sender)        \* Broadcast input to peers
DeliverMessage(msg)      \* Non-deterministic delivery
LoseMessage(msg)         \* Model message loss
DetectDesync(p)          \* Checksum mismatch detection
```

**Safety Properties:**
- `TypeInvariant` - Valid states and bounds
- `ConnectedFrameBoundedDrift` - Frames within 1 of each other
- `NoAdvanceWithoutInputs` - Can only advance with all inputs

## LockstepState.tla Improvements

Added desync detection modeling:

```tla
VARIABLE inSync    \* Whether peer's state matches leader

Desync(p) ==
    /\ ~IsLeader(p)
    /\ inSync[p] = TRUE
    /\ inSync' = [inSync EXCEPT ![p] = FALSE]

ReceiveStateSync(follower, leader) ==
    ...
    /\ inSync' = [inSync EXCEPT ![follower] = TRUE]  \* Sync restores consistency

\* Liveness: desync eventually corrected
DesyncEventuallyCorrected ==
    (\E p \in Peer : IsLeader(p)) => <>(\A p \in Peer : inSync[p])
```

## LeaderElection.tla Fix

Added missing frame check to Vote action (was a contradiction between models):

```tla
VARIABLE frame    \* Current frame per peer (for log comparison)

Vote(voter, candidate) ==
    /\ state[candidate] = "Candidate"
    /\ voter # candidate
    /\ currentTerm[candidate] >= currentTerm[voter]
    /\ frame[candidate] >= frame[voter]  \* NEW: Log comparison
    /\ \/ votedFor[voter] = 0
       \/ currentTerm[candidate] > currentTerm[voter]
    ...
```

## TypeScript TLA+ Integration

### File Headers with TLA+ References

Each network module now documents its TLA+ model mapping:

```typescript
/**
 * LeaderElection - Raft-inspired leader election
 *
 * TLA+ Model: LeaderElection.tla
 * - currentTerm variable: election epoch (monotonically increasing)
 * - state variable: "Follower" | "Candidate" | "Leader"
 * - votedFor variable: who this peer voted for
 * - frame variable: current frame (for log comparison)
 *
 * Key TLA+ Actions:
 * - StartElection(p): follower -> candidate, term++
 * - Vote(voter, candidate): grant vote if term/frame valid
 * - BecomeLeader(p): candidate with majority -> leader
 */
```

### Runtime Invariant Checks

Added `assertInvariants()` methods to all network modules:

| Module | Invariants Checked |
|--------|-------------------|
| `LeaderElection.ts` | TypeInvariant (term >= 0, valid state), term monotonicity, leader/candidate consistency |
| `LocalEventQueue.ts` | LocalEventsPreserved (only local events after sync) |
| `StateSyncManager.ts` | SyncTermBounded (syncTerm <= currentTerm), TypeInvariant |
| `InputBuffer.ts` | TypeInvariant (frame >= 0), NoAdvanceWithoutInputs |
| `P2PManager.ts` | TypeInvariant (valid connection states) |

Example from LeaderElection.ts:

```typescript
assertInvariants(): void {
  // TypeInvariant: term >= 0
  if (this.currentTerm < 0) {
    throw new Error(`TLA+ TypeInvariant violated: term ${this.currentTerm} < 0`)
  }

  // Term monotonicity (local check)
  if (this.currentTerm < this.previousTerm) {
    throw new Error(
      `TLA+ Term monotonicity violated: term decreased from ${this.previousTerm} to ${this.currentTerm}`
    )
  }

  // Candidate must have voted for self
  if (this.state === 'candidate' && this.votedFor !== this.config.localPlayerId) {
    throw new Error(
      `TLA+ Consistency violated: candidate must vote for self`
    )
  }
}
```

## Updated run_tlc.sh

```bash
# Models:
#   LeaderElection  - Raft election, term safety, majority voting (~21K states)
#   LockstepSimple  - Frame sync, basic events, leader authority (~1M states)
#   LockstepState   - Event ownership, syncTerm validation, desync recovery (~50M states)
#   LockstepNetwork - Message loss, peer lifecycle, checksum detection (~TBD states)

# Usage:
./run_tlc.sh              # Run all models
./run_tlc.sh --quick      # Run LeaderElection + LockstepSimple
./run_tlc.sh --state      # Run only LockstepState
./run_tlc.sh --network    # Run only LockstepNetwork
```

## Model Coverage Matrix

| Aspect | LeaderElection | LockstepSimple | LockstepState | LockstepNetwork |
|--------|---------------|----------------|---------------|-----------------|
| Term/voting | Yes | Yes | Yes | - |
| Frame sync | Yes (abstract) | Yes | Yes | Yes |
| Events | - | Boolean | Tuples | - |
| State sync | - | Atomic | With term validation | - |
| Desync detection | - | - | Yes | Yes |
| Message loss | - | - | - | Yes |
| Peer lifecycle | - | - | - | Yes |
| Checksum comparison | - | - | - | Yes |

## Files Modified

**TLA+ Models:**
- `tla/LeaderElection.tla` - Added frame variable
- `tla/LockstepSimple.tla` - Renamed, added docs
- `tla/LockstepState.tla` - Renamed, added inSync/Desync
- `tla/LockstepNetwork.tla` - New file
- `tla/run_tlc.sh` - Updated for new names

**TypeScript:**
- `src/network/LeaderElection.ts` - TLA+ header, assertInvariants()
- `src/network/InputBuffer.ts` - TLA+ header, assertInvariants(), assertCanAdvance()
- `src/network/StateSyncManager.ts` - TLA+ header, assertInvariants()
- `src/network/LocalEventQueue.ts` - TLA+ header, assertLocalEventsOnly()
- `src/network/P2PManager.ts` - TLA+ header, assertInvariants()

## Next Steps

1. Run TLC on all models to verify no regressions
2. Call assertInvariants() in dev builds at key state transitions
3. Add Jepsen-style tests for message loss scenarios
4. Consider adding WebRTC connection state machine to LockstepNetwork
