# Why Leader Election is Needed

## The Question

For P2P lockstep netcode, do we actually need Raft-style leader election? Or could we use a simpler fixed-host model?

## Why We Need a Leader

In lockstep netcode, all peers run the same deterministic simulation. But we still need **one authority** for:

1. **State sync** - Periodically sending authoritative game state to correct drift
2. **Desync detection** - When checksums mismatch, one peer's state must be "correct"
3. **Tiebreaking** - Floating-point drift or timing edge cases need a canonical source

## Why Election (Not Fixed Host)

Two approaches were considered:

| Approach | On Leader Disconnect | Complexity |
|----------|---------------------|------------|
| Fixed Host | Game ends | Low |
| Elected Leader | New leader elected, game continues | High |

**Decision: Elected Leader**

Reason: We don't want the game to end when one player disconnects. With 3+ players, the remaining players should be able to continue playing with a new leader.

## Trade-offs Accepted

Using Raft-style election means:
- More complex codebase (LeaderElection, term tracking, vote handling)
- TLA+ model checking needed to verify correctness
- Jepsen-style tests for failure scenarios
- Subtle bugs possible (see: NoTwoLeadersInSameTerm fix)

These costs are worth it for seamless gameplay continuity.

## Implementation

- `LeaderElection.ts` - Raft-inspired election protocol
- `StateSyncManager.ts` - Leader sends periodic state syncs
- `LockstepState.tla` - TLA+ spec verifying election + state sync safety

## Key Invariants

1. **NoTwoLeadersInSameTerm** - At most one leader per election term
2. **SyncTermBounded** - State syncs are only accepted from current/higher terms
3. **LocalEventsPreserved** - Player's own events survive state sync
