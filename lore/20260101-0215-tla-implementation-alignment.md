# TLA+ Implementation Alignment

**Date**: 2026-01-01
**Scope**: Formal verification alignment between TLA+ model and TypeScript implementation

## Summary

Aligned the TLA+ formal specification with the TypeScript lockstep netcode implementation for Jepsen compliance. Added missing invariants, removed dead code, and established clear naming conventions between model and implementation.

## Changes

### TLA+ Model Updates (`tla/LockstepNetcode.tla`)

1. **Added log comparison to Vote action**
   ```tla
   Vote(voter, candidate) ==
       ...
       /\ frame[candidate] >= frame[voter]  \* Log comparison: candidate at least as up-to-date
   ```
   This matches the implementation's `message.lastFrame >= this.currentFrame` check.

2. **Added LeaderUpToDate invariant**
   ```tla
   LeaderUpToDate ==
       \A leader, p \in Peer :
           state[leader] = "Leader" => frame[leader] >= frame[p] - 1
   ```

3. **Removed dead code**
   - `MaxFrameReached` helper (unused)
   - `HeartbeatTimeout` action (unreachable - subsumed by ExpireHeartbeat + StartElection)

### TypeScript Renames

| Before | After | File |
|--------|-------|------|
| `isHost()` | `isLeader()` | LockstepNetcode.ts |
| `handleRequestVote()` | `handleVoteRequest()` | LeaderElection.ts |

### JSDoc TLA+ Annotations

Added comments linking implementation methods to TLA+ actions:

```typescript
// LeaderElection.ts
/**
 * Start an election (become candidate).
 * TLA+ model: StartElection(p) action - increments term, becomes candidate, votes for self.
 */
private startElection(): void { ... }

/**
 * Handle incoming vote request and grant vote if valid.
 * TLA+ model: Vote(voter, candidate) action
 */
private handleVoteRequest(message: RequestVoteMessage, fromPeerId: string): void { ... }

/**
 * Become leader after winning election.
 * TLA+ model: BecomeLeader(p) action - candidate with majority becomes leader.
 */
private becomeLeader(): void { ... }

/**
 * Step down to follower (discovered higher term).
 * TLA+ model: Stepdown(p) action - leader steps down on seeing higher term.
 */
private stepDown(newTerm: number): void { ... }

/**
 * Broadcast heartbeat to all peers (leader only).
 * TLA+ model: BroadcastHeartbeat(leader) action - sets heartbeatReceived for all peers.
 */
private broadcastHeartbeat(): void { ... }
```

```typescript
// LockstepNetcode.ts
/**
 * Called each game tick with local input.
 * TLA+ model: SubmitInput(p) action - submits input and tries to advance frame.
 */
tick(localInput: PlayerInput, events?: GameEvent[], checksum?: number): boolean { ... }

/**
 * Try to advance to next frame if all inputs received.
 * TLA+ model: AdvanceFrame(p) action - advances when inputsReceived = Peer.
 */
private tryAdvanceFrame(): boolean { ... }

/**
 * Check if this client is the leader.
 * TLA+ model: state[p] = "Leader"
 */
isLeader(): boolean { ... }
```

### Documentation Update

Updated `docs/synchronization.md` with:
- TLA+ verification section
- Verified properties table
- TLA+ Actions to Implementation mapping table
- Election flow documentation
- Message type definitions

## Verification Results

```
TLC Model Checker:
- States found: 143,136 distinct states
- Invariants verified:
  - NoTwoLeadersInSameTerm ✓
  - FrameBoundedDrift ✓
  - TypeInvariant ✓
  - LeaderUpToDate ✓
- Liveness properties:
  - EventuallyLeader ✓
  - EventuallyProgress ✓
```

## Test Results

- TypeScript typecheck: Pass
- Lockstep tests: 95 passing
- Server tests: 2 passing

## TLA+ Action Mapping

| TLA+ Action | TypeScript Method | File |
|-------------|-------------------|------|
| `SubmitInput(p)` | `tick()` | LockstepNetcode.ts |
| `AdvanceFrame(p)` | `tryAdvanceFrame()` | LockstepNetcode.ts |
| `BroadcastHeartbeat(leader)` | `broadcastHeartbeat()` | LeaderElection.ts |
| `ExpireHeartbeat(p)` | Election timer timeout | LeaderElection.ts |
| `StartElection(p)` | `startElection()` | LeaderElection.ts |
| `Vote(voter, candidate)` | `handleVoteRequest()` | LeaderElection.ts |
| `BecomeLeader(p)` | `becomeLeader()` | LeaderElection.ts |
| `StepDown(p)` | `stepDown()` | LeaderElection.ts |
| `RetryElection(p)` | `startElection()` (via timer) | LeaderElection.ts |

## Files Modified

- `tla/LockstepNetcode.tla` - Model updates
- `tla/LockstepNetcode.cfg` - Added LeaderUpToDate invariant
- `client/src/network/LockstepNetcode.ts` - Renamed isHost, added JSDoc
- `client/src/network/LeaderElection.ts` - Renamed method, added JSDoc
- `client/src/network/__tests__/LockstepNetcode.jepsen.test.ts` - Updated tests
- `docs/synchronization.md` - Complete rewrite with TLA+ details
