# Lobby Player Name Customization & Input Fix

## Summary

Added player name (callsign) customization to the multiplayer lobby and fixed an issue where game keys (WASD, C, etc.) couldn't be typed in text input fields.

## Problem

1. **Key blocking**: The `Input` class was calling `preventDefault()` on game keys globally, which prevented typing W, A, S, D, C, and other characters in text inputs like the room name field.

2. **No player identity**: Players were identified only by auto-generated IDs like `player_1735848123456_a1b2c3d4e`, making it hard to identify who's who in the lobby.

## Solution

### Input Fix (`client/src/core/Input.ts`)

Added early return in `onKeyDown` when the event target is an input element:

```typescript
private onKeyDown = (e: KeyboardEvent): void => {
  const target = e.target as HTMLElement
  if (target.tagName === 'INPUT' || target.tagName === 'TEXTAREA' || target.isContentEditable) {
    return
  }
  // ... rest of handler
}
```

### Player Name Feature

**HTML** (`client/index.html`):
- Added "CALLSIGN" input field above the room list view
- Styled with magenta theme to differentiate from room name input
- Max 16 characters

**LobbyUI** (`client/src/ui/LobbyUI.ts`):
- `initPlayerName()`: Loads from localStorage or generates default like "PILOT-1234"
- Auto-saves to localStorage on input change
- `playerNames` Map tracks playerId → displayName
- `getDisplayName()` returns custom name or falls back to truncated ID
- Updated `updatePlayerList()` and `updatePeerStatus()` to use display names

## Data Flow

```
User enters name in input
       │
       ▼
localStorage.setItem('astranyx_player_name', name)
       │
       ▼
setLocalPlayerId() maps playerId → custom name
       │
       ▼
updatePlayerList() displays custom name with "YOU" tag
```

## Limitations

- Player names are client-side only
- Other players see truncated player IDs, not custom names
- Full name sharing would require server-side changes to broadcast names via Phoenix channels

## Files Changed

- `client/src/core/Input.ts` - Skip key capture in input fields
- `client/index.html` - Added callsign input + CSS
- `client/src/ui/LobbyUI.ts` - Name initialization, storage, display
