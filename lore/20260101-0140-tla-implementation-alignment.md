# TLA+ ↔ Implementation Alignment Assessment

**Date:** 2026-01-01
**Focus:** Align naming between TLA+ model and TypeScript implementation

## Summary

The TLA+ model (`LockstepNetcode.tla`) was updated to match the implementation. Now we need to align naming and clean up redundant code for maintainability.

## Effort/Impact Assessment Table

| # | Opportunity | Effort | Impact | Recommendation |
|---|-------------|--------|--------|----------------|
| 1 | Rename `isHost()` → `isLeader()` | Quick | Medium | Auto-fix |
| 2 | Remove duplicate types in NetworkManager.ts | Quick | Medium | Auto-fix |
| 3 | Remove duplicate types in PhoenixClient.ts | Quick | Medium | Auto-fix |
| 4 | Remove unused `MaxFrameReached` in TLA+ | Quick | Low | Auto-fix |
| 5 | Remove dead `HeartbeatTimeout` action in TLA+ | Quick | Low | Auto-fix |
| 6 | Rename `handleRequestVote` → add clarity | Easy | Medium | Ask first |
| 7 | Add JSDoc linking TLA+ actions to methods | Easy | Medium | Ask first |

## Opportunity Details

### #1 - Rename `isHost()` → `isLeader()` [Quick]

**What:** Rename method from gaming terminology to formal model terminology
**Where:**
- `LockstepNetcode.ts:383` - method definition
- `LockstepNetcode.ts:333,356,369,470` - usages
- `MultiplayerManager.ts:456` - wrapper method
- Test files (3 usages)
**Why:** TLA+ model uses "Leader" terminology (from Raft). Aligning makes it easier to trace implementation to formal model.
**Trade-offs:** Breaking change for any external consumers (unlikely)

### #2 - Remove duplicate types in NetworkManager.ts [Quick]

**What:** Remove `PlayerInput`, `EntityState`, `GameEvent` definitions that duplicate `types.ts`
**Where:** `NetworkManager.ts:13-46`
**Why:** DRY - these types should come from the canonical source
**Trade-offs:** NetworkManager's `PlayerInput` has `timestamp` field that `types.ts` doesn't - may indicate NetworkManager is legacy/unused

### #3 - Remove duplicate types in PhoenixClient.ts [Quick]

**What:** Remove `EntityState`, `GameEvent`, `PlayerInput` definitions
**Where:** `PhoenixClient.ts:51-82`
**Why:** DRY - duplicated from `types.ts`
**Trade-offs:** None - these appear to be stale copies

### #4 - Remove unused `MaxFrameReached` in TLA+ [Quick]

**What:** Remove unused helper definition
**Where:** `LockstepNetcode.tla:62`
**Why:** Dead code - defined but never used
**Trade-offs:** None

### #5 - Remove dead `HeartbeatTimeout` action in TLA+ [Quick]

**What:** Remove `HeartbeatTimeout` action that doesn't meaningfully change state
**Where:** `LockstepNetcode.tla:114-118`
**Why:** The action only sets `FALSE` to `FALSE` - no state change
**Trade-offs:** None - it's modeled via `ExpireHeartbeat` + `StartElection`

### #6 - Rename `handleRequestVote` → add clarity [Easy]

**What:** Either rename to `handleVoteRequest` (passive) or add `grantVote()` helper to match TLA+ `Vote` action
**Where:** `LeaderElection.ts:286`
**Why:** TLA+ action is `Vote(voter, candidate)` - implementation name doesn't clearly convey that voting happens here
**Trade-offs:** Naming is subjective; current name is fine

### #7 - Add JSDoc linking TLA+ actions to methods [Easy]

**What:** Add JSDoc comments linking each method to its TLA+ action
**Where:** `LockstepNetcode.ts`, `LeaderElection.ts`
**Why:** Makes formal verification traceable
**Trade-offs:** More comments to maintain

## Files Changed

- `client/src/network/LockstepNetcode.ts`
- `client/src/network/LeaderElection.ts`
- `client/src/network/MultiplayerManager.ts`
- `client/src/network/NetworkManager.ts`
- `client/src/network/PhoenixClient.ts`
- `tla/LockstepNetcode.tla`
- Test files
