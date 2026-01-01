# Hybrid Lockstep + Owner-Authoritative Events Design

## Problem Statement

Pure lockstep simulates ALL game events (damage, death, pickups) on all clients independently. While this works if the simulation is 100% deterministic, there are concerns:

1. **No explicit control**: When your ship dies, the remote client computes it - you don't "tell" them
2. **Double pickup ambiguity**: Both players near a pickup - who gets it?
3. **Trust**: Each client is authoritative over their own state

## Current Architecture (Pure Lockstep)

```
Client A                          Client B
   |                                 |
   |-- Input for frame N ------>     |
   |     <------ Input for frame N --|
   |                                 |
[Simulate with both inputs]    [Simulate with both inputs]
   |                                 |
[Both compute identical results]
```

- Both clients run `Simulation.tick()` with the same inputs
- Collisions, damage, pickups all computed locally
- Works because iteration order is deterministic (player array index)

## Analysis: Is Double-Pickup Actually a Problem?

In current code (`Simulation.ts:2276`):
```typescript
for (const player of this.state.players) {
  if (dx < 18 && dy < 18) {
    this.addPlayerPowerup(player, powerup.type)
    break  // First player in array wins
  }
}
```

**This IS deterministic** - player at index 0 always wins if both are in range.

However, the user wants **explicit control** over certain events, not just determinism.

## Proposed Hybrid Architecture

**Principle**: Each player is authoritative over events that happen TO them.

| Event Type | Who Detects | Who Applies |
|------------|-------------|-------------|
| Movement | Both (via input) | Both |
| Player shooting | Both (via input) | Both |
| Enemy death | Both (deterministic) | Both |
| **Player damage** | Owner only | Owner broadcasts, all apply |
| **Player death** | Owner only | Owner broadcasts, all apply |
| **Pickup claimed** | First to claim | Claimer broadcasts, all apply |

### Event Types

```typescript
type GameEvent =
  | { type: 'damage'; playerId: string; amount: number; newShields: number }
  | { type: 'death'; playerId: string }
  | { type: 'pickup'; playerId: string; pickupId: number; pickupType: string }
  | { type: 'weapon_pickup'; playerId: string; dropId: number }
```

### Message Flow

```
Client A (Player 0)              Client B (Player 1)
   |                                 |
   |-- Frame N input --------->      |
   |-- Event: pickup#5 ------->      |
   |     <-------- Frame N input ----|
   |                                 |
[Skip collision for own damage]  [Skip collision for own damage]
[Apply received events]          [Apply received events]
```

### Implementation Changes

1. **LockstepNetcode**: Add `events` array to `FrameInput`
2. **Simulation**: Add methods:
   - `checkLocalPlayerCollisions(playerId)` - returns events for this player only
   - `applyEvent(event)` - applies an event from remote
   - Skip damage/pickup detection for remote players
3. **Game**: Before tick:
   - Detect events for local player
   - Send events with input
   - Apply received events from remote

### Pickup Priority (Tie-Breaking)

When both players claim the same pickup in the same frame:
- Lower player index wins (deterministic)
- Other player's claim is ignored

### Latency Considerations

- **Player damage**: Applied immediately on owner's client, 1-frame delay on remote
- **Pickups**: Claimed immediately, confirmed within input delay
- For a shoot-em-up at 60fps, 1-2 frame delay is imperceptible

## Alternative: Keep Pure Lockstep + Better Desync Detection

If the simulation is truly deterministic:
- Double-pickup is already resolved (player 0 wins)
- Desync detection via checksums catches any drift
- Simpler architecture, no latency for events

The current desync detection (added in previous session) compares state checksums every 30 frames.

## Recommendation

**Start with pure lockstep + desync detection**. If desyncs occur:
1. Add verbose logging to identify non-determinism source
2. Fix the non-determinism (likely floating point or iteration order)
3. Only move to hybrid if pure lockstep proves unreliable

The hybrid approach adds complexity and subtle latency. Pure lockstep is the gold standard for fighting games and works well when determinism is guaranteed.

## Files Affected (if implementing hybrid)

- `LockstepNetcode.ts` - Add events to FrameInput
- `Simulation.ts` - Add event detection/application methods
- `Game.ts` - Wire up event flow

## Decision

User requested owner-authoritative events. Proceeding with hybrid implementation.
