# Harden Assessment - Lockstep Netcode Refactoring

## Overview

Assessment of the lockstep netcode refactoring that extracted modular components with leader election, Jepsen-style tests, and TLA+ verification.

## Effort/Impact Assessment Table

| # | Opportunity | Effort | Impact | Recommendation |
|---|-------------|--------|--------|----------------|
| 1 | Duplicate `inputsEqual` function | Quick | Medium | Auto-fix |
| 2 | Unused `messageQueue` field in MockDataChannel | Quick | Low | Auto-fix |
| 3 | Unused `PeerInfo` interface in types.ts | Quick | Low | Auto-fix |
| 4 | Unused `LinkFaults` interface in FaultInjection.ts | Quick | Low | Auto-fix |
| 5 | Inconsistent localPlayerId config (some classes need it, some don't use it) | Easy | Low | Skip |
| 6 | `maxRollbackFrames` is never used (pure lockstep) | Easy | Medium | Ask first |
| 7 | Missing unit tests for InputBuffer edge cases | Moderate | Medium | Ask first |
| 8 | Missing LeaderElection unit tests (election timeout, split vote) | Moderate | Medium | Ask first |
| 9 | HeartbeatMessage.checksum always 0 (not populated) | Easy | Low | Ask first |

## Opportunity Details

### #1: Duplicate `inputsEqual` function [Quick]

**What**: `inputsEqual` is defined in both `types.ts` (complete version checking all fields) and `LockstepNetcode.ts` (incomplete version missing secondary/swap/pickup/pause).

**Where**:
- `types.ts:53-66` - Complete version
- `LockstepNetcode.ts:52-61` - Incomplete version (only 6 fields vs 10)

**Why**: The incomplete version in LockstepNetcode could cause bugs if used. Should use the complete one from types.ts consistently.

**Trade-offs**: None - straightforward consolidation.

---

### #2: Unused `messageQueue` field in MockDataChannel [Quick]

**What**: `MockDataChannel.messageQueue` is declared but never used.

**Where**: `FaultInjection.ts:56`

**Why**: Dead code that adds confusion.

**Trade-offs**: None.

---

### #3: Unused `PeerInfo` interface in types.ts [Quick]

**What**: `PeerInfo` interface is defined but never imported or used anywhere.

**Where**: `types.ts:274-281`

**Why**: Dead code from planning phase that was never implemented.

**Trade-offs**: None - could be kept if planning to use it later, but currently unused.

---

### #4: Unused `LinkFaults` interface in FaultInjection.ts [Quick]

**What**: `LinkFaults` interface is exported but never used.

**Where**: `FaultInjection.ts:34-37`

**Why**: Dead code.

**Trade-offs**: None.

---

### #5: Inconsistent localPlayerId config [Skip]

**What**: `StateSyncManager` requires `localPlayerId` in config but never uses it internally.

**Where**: `StateSyncManager.ts:16`

**Why**: Minor inconsistency, doesn't affect functionality.

**Trade-offs**: Removing it could break API if someone passes it expecting it to be used.

**Recommendation**: Skip - low value change.

---

### #6: `maxRollbackFrames` is never used [Easy]

**What**: The `maxRollbackFrames` config option is stored but never read or used. Pure lockstep doesn't do rollback.

**Where**:
- `types.ts:240` - defined in LockstepConfig
- `types.ts:255` - in DEFAULT_CONFIG
- `LockstepNetcode.ts:93` - assigned but never read

**Why**: Dead config option that adds confusion. Either implement rollback or remove it.

**Trade-offs**: Removing changes the config interface (minor breaking change).

---

### #7: Missing InputBuffer edge case tests [Moderate]

**What**: Missing tests for:
- Pre-seeding behavior verification
- Behavior when `getOrderedInputs` called on partially filled frame
- Buffer overflow/cleanup verification with high frame numbers

**Where**: `LockstepNetcode.jepsen.test.ts`

**Why**: Current tests cover basic happy path but not edge cases.

**Trade-offs**: Takes time, but improves confidence.

---

### #8: Missing LeaderElection tests [Moderate]

**What**: Missing tests for:
- Election timeout (timer-based, needs mocking)
- Split vote scenario (no majority, timeout → new election)
- Term rollback rejection (can't vote for lower term candidate)

**Where**: `LockstepNetcode.jepsen.test.ts`

**Why**: Election is critical; more edge cases should be tested.

**Trade-offs**: Timer-based tests are tricky.

---

### #9: HeartbeatMessage.checksum always 0 [Easy]

**What**: In `LeaderElection.broadcastHeartbeat()`, the checksum is hardcoded to 0.

**Where**: `LeaderElection.ts:398`

**Why**: The checksum field exists but isn't populated. Either populate it (from game state) or remove the field.

**Trade-offs**: Would need to thread checksum through to LeaderElection, or just remove unused field.

---

## Summary

- **Quick fixes (4)**: #1-4 - duplicate code, unused fields/interfaces
- **Easy fixes (2)**: #6, #9 - unused config, unpopulated field
- **Moderate (2)**: #7-8 - additional test coverage
- **Skip (1)**: #5 - low value
