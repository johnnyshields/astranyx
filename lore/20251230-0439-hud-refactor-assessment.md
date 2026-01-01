# HUD Layer Refactor Assessment

## Summary

Recent work added camera-compensated play bounds and a separate HUD rendering layer. The implementation works but left some dead code and duplicated data structures that should be cleaned up.

## Effort/Impact Assessment Table

| # | Opportunity | Effort | Impact | Recommendation |
|---|-------------|--------|--------|----------------|
| 1 | Remove unused `_renderHealthBar` parameter | Quick | Low | Auto-fix |
| 2 | Remove unused `mulFixed` function | Quick | Low | Auto-fix |
| 3 | Remove unused `PLAYER_FRICTION` constant | Quick | Low | Auto-fix |
| 4 | Remove unused `RenderCommand` interface | Quick | Low | Auto-fix |
| 5 | Extract enemy scale/depth config to shared constant | Easy | Medium | Auto-fix |
| 6 | Extract boss sizes config to shared constant | Easy | Medium | Auto-fix |
| 7 | DRY up health bar color logic | Easy | Medium | Auto-fix |

## Opportunity Details

### #1 Remove unused `_renderHealthBar` parameter
- **What**: Remove the `_renderHealthBar` parameter from `renderEnemy()` and `renderBoss()` - it was added during refactor but never used (health bars are now rendered separately)
- **Where**: `Game.ts` lines 470, 603
- **Why**: Dead code cleanup, parameter is always ignored
- **Trade-offs**: None

### #2 Remove unused `mulFixed` function
- **What**: Remove the `mulFixed` function which is defined but never called
- **Where**: `Simulation.ts` line 36
- **Why**: Dead code cleanup
- **Trade-offs**: None (can be re-added if fixed-point multiplication is needed later)

### #3 Remove unused `PLAYER_FRICTION` constant
- **What**: Remove the `PLAYER_FRICTION` constant which is defined but never used (friction is hardcoded inline)
- **Where**: `Simulation.ts` line 319
- **Why**: Dead code cleanup, the value 0.91 is used directly in `updatePlayer`
- **Trade-offs**: None

### #4 Remove unused `RenderCommand` interface
- **What**: Remove the `RenderCommand` interface which is exported but never used
- **Where**: `Renderer.ts` lines 5-14
- **Why**: Dead code cleanup - this was likely for a command buffer pattern that was never implemented
- **Trade-offs**: None

### #5 Extract enemy scale/depth config to shared constant
- **What**: The enemy scale/depth switch statement is duplicated in `renderEnemy()` and `renderEnemyHealthBar()`. Extract to a shared `ENEMY_RENDER_CONFIG` constant.
- **Where**: `Game.ts` lines 479-521 and 569-582
- **Why**: DRY - same data in two places means they can get out of sync
- **Trade-offs**: Slightly more indirection

### #6 Extract boss sizes config to shared constant
- **What**: The boss sizes array is duplicated in `renderBoss()` and `renderBossHealthBar()`. Extract to a shared `BOSS_SIZES` constant.
- **Where**: `Game.ts` lines 611-618 and 766-773
- **Why**: DRY - same data in two places means they can get out of sync
- **Trade-offs**: None

### #7 DRY up health bar color logic
- **What**: The health bar color calculation (green > 50%, yellow > 25%, red otherwise) is duplicated in `renderEnemyHealthBar()` and `renderBossHealthBar()`. Extract to a helper function.
- **Where**: `Game.ts` lines 595-599 and 787-791
- **Why**: DRY - identical logic in two places
- **Trade-offs**: Minor - adds a function call
