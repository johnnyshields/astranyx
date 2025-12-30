# Harden Assessment: Multiplayer Implementation

## Summary

Review of the multiplayer lobby, WebRTC, and Phoenix integration implementation.

## Effort/Impact Assessment Table

| # | Opportunity | Effort | Impact | Recommendation |
|---|-------------|--------|--------|----------------|
| 1 | Remove duplicate player list update logic | Quick | Medium | Auto-fix |
| 2 | Remove unused `inputSequence` field in PhoenixClient | Quick | Low | Auto-fix |
| 3 | Extract `truncatePlayerId` helper (duplicated in LobbyUI) | Quick | Low | Auto-fix |
| 4 | Remove duplicate lobby hiding in `startMultiplayerGame` | Quick | Low | Auto-fix |
| 5 | Add connection timeout for Phoenix connect | Easy | High | Ask first |
| 6 | Add peer connection timeout handling | Easy | High | Ask first |
| 7 | Clear event handlers on cleanup in MultiplayerManager | Easy | Medium | Ask first |
| 8 | Add missing test coverage for MultiplayerManager | Moderate | Medium | Ask first |
| 9 | Add missing test coverage for LobbyUI | Moderate | Low | Skip |

---

## Opportunity Details

### #1 - Remove duplicate player list update logic [Quick]
**What**: Both `MultiplayerManager.setupPhoenixHandlers()` and the `onLobbyUpdate` handler in main.ts update the player list. The MultiplayerManager already updates `lobbyState.currentRoom.players` when `player_left` is received, but it filters the array manually when PhoenixClient already updates it via the `player_joined` handler.

**Where**: `MultiplayerManager.ts:115-123` - the `player_left` filter is redundant since PhoenixClient's `player_joined` handler provides the full updated players array.

**Why**: Reduces confusion about where player list state is authoritative.

### #2 - Remove unused `inputSequence` field [Quick]
**What**: `PhoenixClient.inputSequence` is incremented but the tick value is never used for anything meaningful in P2P lockstep mode.

**Where**: `PhoenixClient.ts:87, 206`

**Why**: Dead code that may confuse readers about its purpose.

### #3 - Extract `truncatePlayerId` helper [Quick]
**What**: The same player ID truncation logic (`playerId.length > 20 ? playerId.slice(0, 8) + '...' + playerId.slice(-8) : playerId`) appears twice in LobbyUI.

**Where**: `LobbyUI.ts:222-224, 251-253`

**Why**: DRY - single source of truth for display formatting.

### #4 - Remove duplicate lobby hiding [Quick]
**What**: `startMultiplayerGame` in main.ts calls both `lobbyScreen?.classList.add('hidden')` and `lobbyUI.hide()`. The `hide()` method already adds the 'hidden' class.

**Where**: `main.ts:289-291`

**Why**: Redundant code.

### #5 - Add connection timeout for Phoenix connect [Easy]
**What**: `PhoenixClient.connect()` has no timeout - if the server is unreachable, it will hang indefinitely.

**Where**: `PhoenixClient.ts:92-116`

**Why**: Poor UX - users should get feedback quickly if server is down.

**Trade-offs**: Adds complexity, but Phoenix socket has built-in timeout options we can use.

### #6 - Add peer connection timeout handling [Easy]
**What**: WebRTC peer connections in P2PManager have no timeout. If a peer fails to connect, the game will wait forever in `connecting_peers` state.

**Where**: `MultiplayerManager.ts:321-328`, `P2PManager.ts`

**Why**: Users stuck waiting with no feedback if WebRTC fails.

**Trade-offs**: Need to decide timeout duration and error handling behavior.

### #7 - Clear event handlers on cleanup [Easy]
**What**: `MultiplayerManager.cleanup()` doesn't clear the handler Sets (stateChangeHandlers, lobbyUpdateHandlers, etc.), which could cause memory leaks if the manager is recreated.

**Where**: `MultiplayerManager.ts:447-465`

**Why**: Memory leak prevention.

### #8 - Add test coverage for MultiplayerManager [Moderate]
**What**: MultiplayerManager has no tests. It's a critical orchestration component.

**Where**: New file `MultiplayerManager.test.ts`

**Why**: Ensures state machine transitions work correctly.

**Trade-offs**: Requires mocking PhoenixClient, P2PManager, LockstepNetcode.

### #9 - Add test coverage for LobbyUI [Moderate]
**What**: LobbyUI has no tests.

**Where**: New file `LobbyUI.test.ts`

**Why**: Ensures DOM manipulation works correctly.

**Trade-offs**: Low value since it's mostly DOM manipulation that's hard to break.
