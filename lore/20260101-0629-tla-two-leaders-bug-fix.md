# TLA+ NoTwoLeadersInSameTerm Bug Fix

## Summary

TLC model checker found a safety violation where two peers could become leaders in the same election term. This was caused by the `ReceiveStateSync` action updating a peer's term without properly stepping down candidates or clearing their votes.

## The Bug

**TLA+ Trace (simplified):**
1. Peer 2 becomes Candidate in term 1, collects majority votes `{1, 2}`
2. Meanwhile, Peer 1 becomes Leader in term 2 with votes `{1, 3}`
3. Peer 2 (still Candidate) receives StateSync from Peer 1
4. `ReceiveStateSync` updates Peer 2's term to 2, but leaves them as Candidate with old votes
5. `BecomeLeader` fires for Peer 2 using stale votes from term 1
6. **Result:** Two leaders (Peer 1 and Peer 2) in term 2

**Root Cause:** The Raft rule "any message from a higher term causes step down" was not applied to state sync messages.

## Fixes

### TLA+ Model (`LockstepState.tla`)

```diff
ReceiveStateSync(follower, leader) ==
    /\ ~IsLeader(follower)
    /\ IsLeader(leader)
    /\ currentTerm[leader] >= syncTerm[follower]
    /\ currentTerm' = [currentTerm EXCEPT ![follower] = ...]
    /\ syncTerm' = [syncTerm EXCEPT ![follower] = currentTerm[leader]]
+   /\ state' = [state EXCEPT ![follower] = "Follower"]
+   /\ votesReceived' = [votesReceived EXCEPT ![follower] = {}]
+   /\ votedFor' = [votedFor EXCEPT ![follower] = IF currentTerm[leader] > currentTerm[follower] THEN 0 ELSE votedFor[follower]]
    /\ pendingEvents' = ...
    /\ inSync' = ...
-   /\ UNCHANGED <<frame, state, votedFor, votesReceived, inputsReceived, heartbeatReceived>>
+   /\ UNCHANGED <<frame, inputsReceived, heartbeatReceived>>
```

### TypeScript (`LeaderElection.ts`)

Added public method for external term updates:

```typescript
onHigherTermSeen(term: number): void {
  if (term > this.currentTerm) {
    this.stepDown(term)
  }
}
```

### TypeScript (`LockstepNetcode.ts`)

Wire up state sync to trigger election step-down:

```typescript
private receiveStateSync(message: StateSyncMessage): void {
  if (this.isLeader()) return

  // RAFT RULE: Any message from higher term causes step down
  this.election.onHigherTermSeen(message.term)

  const pendingEvents = this.syncManager.receiveSyncMessage(message)
  this.onStateSync?.(message.state, message.frame, pendingEvents)
}
```

## Tests Added

1. **Unit test:** `candidate steps down via onHigherTermSeen (TLA+ ReceiveStateSync fix)`
2. **Edge case:** `onHigherTermSeen does nothing for same or lower term`
3. **Safety property:** `PROPERTY: Candidate cannot become leader after term bump from state sync`

## Files Changed

- `tla/LockstepState.tla` - Fixed ReceiveStateSync action
- `client/src/network/LeaderElection.ts` - Added onHigherTermSeen method
- `client/src/network/LockstepNetcode.ts` - Call onHigherTermSeen in receiveStateSync
- `client/src/network/__tests__/LockstepNetcode.jepsen.test.ts` - Added 3 tests

## Lesson Learned

The StateSyncManager and LeaderElection components both tracked `currentTerm` independently. When StateSyncManager received a higher term, it updated its own term but didn't notify LeaderElection. This architectural issue was revealed by TLA+ model checking.

The fix ensures that term updates from any message type (heartbeat, vote, OR state sync) all flow through the same `stepDown()` mechanism in LeaderElection.
