# Harden Assessment 2 - Post-Refactor Cleanup

## Overview

Assessment of the lockstep netcode after the major refactoring that extracted modular components. The previous harden pass addressed duplicate code and unused interfaces. This pass focuses on remaining cleanup and architectural refinements.

## Effort/Impact Assessment Table

| # | Opportunity | Effort | Impact | Recommendation |
|---|-------------|--------|--------|----------------|
| 1 | Unused `localPlayerId` in StateSyncManagerConfig | Quick | Low | Auto-fix |
| 2 | Unused `getLocalChecksum()` method in InputBuffer | Quick | Low | Auto-fix |
| 3 | Unused `getBufferedFrames()` method in InputBuffer | Quick | Low | Auto-fix |
| 4 | Unused `getInputDelay()` method in InputBuffer (LockstepNetcode has its own) | Quick | Low | Auto-fix |
| 5 | Multiple unused methods in LocalEventQueue | Easy | Low | Ask first |
| 6 | Verbose console.log in tick path (performance) | Easy | Medium | Ask first |
| 7 | Test helper duplication (`createPlayerOrder`, `createTestInput`) | Moderate | Low | Skip |

## Opportunity Details

### #1: Unused `localPlayerId` in StateSyncManagerConfig [Quick]

**What**: `StateSyncManagerConfig` requires `localPlayerId` but it's never used inside `StateSyncManager`.

**Where**: `StateSyncManager.ts:16-17`

**Why**: Dead config option adds confusion. Either use it or remove it.

**Trade-offs**: Minor breaking change to config interface.

---

### #2: Unused `getLocalChecksum()` method in InputBuffer [Quick]

**What**: `getLocalChecksum()` and `lastLocalChecksum` field are stored via `setLocalChecksum()` but never retrieved.

**Where**: `InputBuffer.ts:33, 167-175`

**Why**: Dead code. Checksums are compared per-player from the checksumBuffer, not via this method.

**Trade-offs**: None.

---

### #3: Unused `getBufferedFrames()` method in InputBuffer [Quick]

**What**: `getBufferedFrames()` returns list of all buffered frame numbers but is never called.

**Where**: `InputBuffer.ts:221-223`

**Why**: Likely for debugging but never used. Remove or keep for future debugging.

**Trade-offs**: Could be useful for debugging later.

---

### #4: Unused `getInputDelay()` method in InputBuffer [Quick]

**What**: `InputBuffer.getInputDelay()` duplicates `LockstepNetcode.getInputDelay()`. The InputBuffer method is never called externally.

**Where**: `InputBuffer.ts:214-216`

**Why**: LockstepNetcode exposes this publicly; InputBuffer version is unnecessary.

**Trade-offs**: None.

---

### #5: Multiple unused methods in LocalEventQueue [Easy]

**What**: Several methods are defined but never called:
- `getPendingEventsForFrame(frame)` - never called
- `getPendingEventsAfterFrame(frame)` - never called
- `confirmEventsUpToFrame(frame)` - never called
- `filterByType()` - never called
- `filterByOwner()` - never called

**Where**: `LocalEventQueue.ts:99-103, 108-112, 130-147, 188-199`

**Why**: These were likely designed for future use but not implemented. Adds code surface without value.

**Trade-offs**: Could be useful for future features. Keep if planning to use, otherwise remove.

---

### #6: Verbose console.log in tick path [Easy]

**What**: `LockstepNetcode.tick()` logs every input received and every frame status. This is noisy in production.

**Where**:
- `LockstepNetcode.ts:198-199` - logs every received input
- `LockstepNetcode.ts:254` - logs frame input count

**Why**: Performance and noise. These should be debug-level or conditional.

**Trade-offs**: Less visibility during debugging. Could add a `debug` config flag instead.

---

### #7: Test helper duplication [Skip]

**What**: `createPlayerOrder()` and `createTestInput()` are defined in both test files.

**Where**:
- `LockstepNetcode.test.ts:7-12, 29-44`
- `LockstepNetcode.jepsen.test.ts:33-41`

**Why**: Minor duplication. Could extract to shared test utils.

**Trade-offs**: Test files are isolated; duplication is acceptable for test clarity.

**Recommendation**: Skip - test file duplication is acceptable.

---

## Summary

- **Quick fixes (4)**: #1-4 - unused config/methods
- **Easy fixes (2)**: #5-6 - unused LocalEventQueue methods, verbose logging
- **Skip (1)**: #7 - test helper duplication (acceptable)
