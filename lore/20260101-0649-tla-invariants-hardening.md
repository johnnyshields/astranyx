# TLA+ Invariants Hardening

## Summary

Added consistent invariants across all TLA+ models, implemented matching TypeScript runtime checks, and added comprehensive test coverage.

## TLA+ Invariants

All four TLA+ models now share a consistent set of invariants:

### Election Invariants
| Invariant | Description |
|-----------|-------------|
| `NoTwoLeadersInSameTerm` | At most one leader per term |
| `CandidateVotedForSelf` | Candidates vote for themselves |
| `LeaderVotedForSelf` | Leaders voted for themselves |
| `VotedForValid` | votedFor is null or valid peer |
| `VotesFromValidPeers` | All votes from valid peers |
| `LeaderHadMajority` | Leader has majority (or term 0 / forced) |

### Lockstep Invariants
| Invariant | Description |
|-----------|-------------|
| `FrameBoundedDrift` | Frames within 1 of each other |
| `InputsFromValidPeers` | Inputs from valid peers only |

### State Sync Invariants
| Invariant | Description |
|-----------|-------------|
| `SyncTermBounded` | syncTerm <= currentTerm |
| `LocalEventsPreserved` | Only local events survive sync |
| `LeaderUpToDate` | Leader at least as current as peers |

### Type Invariants
| Invariant | Description |
|-----------|-------------|
| `TypeInvariant` | Bounds on frame, term, state, etc. |

## Removed Redundant Invariants

- `FrameNonNegative` - Already covered by TypeInvariant
- `EventOwnerValid` - Implied by LocalEventsPreserved

## TypeScript Runtime Checks

Added `assertInvariants()` methods that verify:

### LeaderElection.ts
- `VotesFromValidPeers`: All votes from playerOrder
- `LeaderHadMajority`: Leader has majority votes (term > 0)

### InputBuffer.ts
- `InputsFromValidPeers`: All inputs from playerOrder

## Bug Fix: LeaderHadMajority

Initial leader at term 0 is assigned without election, so has no votes. Fixed invariant to allow term 0 leaders:

```tla
LeaderHadMajority ==
    \A p \in Peer : IsLeader(p) =>
        \/ IsMajority(votesReceived[p])
        \/ currentTerm[p] = 0  \* Initial leader
```

## Tests Added

New tests in `LockstepNetcode.jepsen.test.ts`:
- `INVARIANT: InputsFromValidPeers - assertInvariants catches invalid peers`
- `INVARIANT: VotesFromValidPeers - assertInvariants catches invalid voters`
- `INVARIANT: LeaderHadMajority - assertInvariants validates leader has majority`

Fixed existing test:
- `SCENARIO: Frame rollback prevention` - Added retentionFrames config

## Files Changed

### TLA+ Models
- `LeaderElection.tla` - Added VotesFromValidPeers, LeaderHadMajority
- `LockstepSimple.tla` - Added VotesFromValidPeers, LeaderHadMajority, InputsFromValidPeers
- `LockstepNetwork.tla` - Added VotedForValid, VotesFromValidPeers, LeaderHadMajority, InputsFromValidPeers; removed EventOwnerValid
- `LockstepState.tla` - Removed FrameNonNegative, EventOwnerValid; fixed LeaderHadMajority

### Config Files
- `MCLeaderElection.cfg` - Added VotesFromValidPeers, LeaderHadMajority
- `MCLockstepSimple.cfg` - Added VotesFromValidPeers, LeaderHadMajority, InputsFromValidPeers
- `MCLockstepNetwork.cfg` - Reorganized and added missing invariants
- `MCLockstepState.cfg` - Removed FrameNonNegative, EventOwnerValid

### TypeScript
- `LeaderElection.ts` - Added VotesFromValidPeers, LeaderHadMajority checks
- `InputBuffer.ts` - Added InputsFromValidPeers check
- `LockstepNetcode.jepsen.test.ts` - Added 3 new tests, fixed 1 test
