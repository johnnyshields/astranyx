# TLA+ Harden Assessment

Date: 2026-01-01

## Summary

Assessment of `/tla` directory for cleanup and consistency improvements.

## Effort/Impact Assessment Table

| # | Opportunity | Effort | Impact | Recommendation |
|---|-------------|--------|--------|----------------|
| 1 | Add missing invariants to LockstepSimple.tla | Quick | Medium | Auto-fix |
| 2 | Add missing invariants to MCLockstepSimple.cfg | Quick | Medium | Auto-fix |
| 3 | Remove unused `Sequences` EXTEND from LockstepNetwork.tla | Quick | Low | Auto-fix |
| 4 | Remove unused `CurrentLeader` helper from LockstepState.tla | Quick | Low | Auto-fix |
| 5 | Remove unused `CurrentLeader` helper from LockstepNetwork.tla | Quick | Low | Auto-fix |
| 6 | Standardize Peer count in configs (3 vs 4) | Easy | Low | Ask first |
| 7 | Extract common helpers to separate module | Moderate | Medium | Skip |

---

## Opportunity Details

### #1 Add missing invariants to LockstepSimple.tla
- **What**: Add `CandidateVotedForSelf`, `LeaderVotedForSelf`, `VotedForValid` invariants (already in LeaderElection.tla and LockstepState.tla)
- **Where**: `LockstepSimple.tla` - Safety Properties section
- **Why**: Consistency across models; catches vote-related bugs in simplified model
- **Trade-offs**: None - these are simple boolean checks

### #2 Add missing invariants to MCLockstepSimple.cfg
- **What**: Add the new invariants to the model checker config
- **Where**: `MCLockstepSimple.cfg`
- **Why**: Config should check all available invariants
- **Trade-offs**: Slightly longer model checking time (negligible)

### #3 Remove unused `Sequences` EXTEND from LockstepNetwork.tla
- **What**: Remove `Sequences` from EXTENDS (not used anywhere in the file)
- **Where**: `LockstepNetwork.tla:41`
- **Why**: Dead import; messages use tuples not sequences
- **Trade-offs**: None

### #4 Remove unused `CurrentLeader` helper from LockstepState.tla
- **What**: Remove the `CurrentLeader` definition (defined but never used)
- **Where**: `LockstepState.tla:60-62`
- **Why**: Dead code; `IsLeader(p)` is used instead
- **Trade-offs**: None

### #5 Remove unused `CurrentLeader` helper from LockstepNetwork.tla
- **What**: Remove the `CurrentLeader` definition (defined but never used)
- **Where**: `LockstepNetwork.tla:100-102`
- **Why**: Dead code; `IsLeader(p)` is used instead
- **Trade-offs**: None

### #6 Standardize Peer count in configs
- **What**: Use consistent Peer count across configs (currently 4 in LeaderElection/LockstepSimple, 3 in LockstepState/LockstepNetwork)
- **Where**: All `.cfg` files
- **Why**: Consistency; easier to compare run times across models
- **Trade-offs**: Changing peer count affects state space size significantly; current values may be intentional for run time

### #7 Extract common helpers to separate module
- **What**: Create `Common.tla` with shared definitions: `IsMajority`, `MinPeer`, `IsLeader`, etc.
- **Where**: New file + all `.tla` files
- **Why**: DRY; single source of truth for helpers
- **Trade-offs**: TLA+ module dependencies can be tricky; increased complexity for small benefit; TLC may have issues with INSTANCE
