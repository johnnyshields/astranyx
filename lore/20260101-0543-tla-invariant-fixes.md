# TLA+ Invariant Fixes

## Summary

Fixed multiple TLA+ invariant violations discovered during model checking, and improved the accuracy of the state sync model to match the TypeScript implementation.

## Changes

### 1. LeaderVotedForSelf Invariant Fix

**Problem**: Initial state had peer 1 as Leader but `votedFor[1] = 0` (no vote).

**Fix**: Updated `Init` in all four TLA+ specs to set the initial leader's vote:
```tla
votedFor = [p \in Peer |-> IF p = MinPeer THEN p ELSE 0]
```

**Files**: LeaderElection.tla, LockstepSimple.tla, LockstepState.tla, LockstepNetwork.tla

### 2. SyncTermBounded Invariant Fix

**Problem**: `SendStateSync` atomically updated `syncTerm` for ALL peers, but followers might not have updated their `currentTerm` yet (e.g., peer 3 never voted, so `currentTerm[3] = 0` but `syncTerm[3] = 1`).

**Fix**: Two changes to match real Raft/TypeScript behavior:

1. **SendStateSync** - Leader only updates its own syncTerm:
```tla
SendStateSync(leader) ==
    /\ IsLeader(leader)
    /\ syncTerm' = [syncTerm EXCEPT ![leader] = currentTerm[leader]]
```

2. **ReceiveStateSync** - Follower updates BOTH syncTerm AND currentTerm:
```tla
ReceiveStateSync(follower, leader) ==
    ...
    /\ currentTerm' = [currentTerm EXCEPT ![follower] =
         IF currentTerm[leader] > currentTerm[follower]
         THEN currentTerm[leader] ELSE currentTerm[follower]]
    /\ syncTerm' = [syncTerm EXCEPT ![follower] = currentTerm[leader]]
```

**Files**: LockstepState.tla, LockstepNetwork.tla

### 3. MaxMessages Config Fix

**Problem**: `MaxMessages = 6` was too small for 3 peers exchanging inputs + state sync messages.

**Fix**: Increased to `MaxMessages = 20` in MCLockstepNetwork.cfg.

### 4. run-tlc.sh Improvements

Replaced `--quick`, `--state`, `--network` flags with flexible `-f`/`--file` option:
```bash
./run-tlc.sh                              # Run all models
./run-tlc.sh -f LeaderElection            # Single model
./run-tlc.sh -f LeaderElection,LockstepSimple  # Multiple models
./run-tlc.sh -f LockstepState --max       # With max resources
```

## TypeScript Alignment

Verified that `StateSyncManager.ts` already implements the correct behavior:
- Validates `message.term >= this.currentTerm` (rejects stale syncs)
- Updates `this.currentTerm = message.term` when receiving higher term

The TLA+ model was simplified/incorrect - the TypeScript was already right. This fix brings TLA+ in line with the implementation.

## Invariant Semantics

**SyncTermBounded**: `\A p \in Peer : syncTerm[p] <= currentTerm[p]`

This now holds because:
- Leader: Sets `syncTerm[leader] = currentTerm[leader]` in SendStateSync
- Follower: Sets `syncTerm[follower] = msgTerm` only after also setting `currentTerm[follower] >= msgTerm` in ReceiveStateSync

This matches the Raft rule: "If RPC contains term T > currentTerm, set currentTerm = T".
