# TLA+ Model Analysis: Does It Match the Game?

## Summary

Analysis of whether the TLA+ specifications accurately model the Astranyx game's event system and netcode requirements.

**Conclusion:** The TLA+ model is well-designed for verifying the *netcode protocol* (synchronization, election, state sync). It correctly abstracts game-specific events because deterministic simulation + checksum-based desync detection handles game logic correctness.

---

## TLA+ Model Overview

Four specifications with increasing detail:

| Model | Purpose | State Space |
|-------|---------|-------------|
| LeaderElection.tla | Raft-inspired election | ~1M states |
| LockstepSimple.tla | Fast protocol verification | ~10M states |
| LockstepState.tla | Complete protocol with events | ~50M states |
| LockstepNetwork.tla | Realistic network faults | ~20-50M states |

### Key Verified Properties

1. **FrameBoundedDrift** - All peers within 1 frame of each other
2. **NoTwoLeadersInSameTerm** - Election safety
3. **LocalEventsPreserved** - After state sync, only local events remain
4. **SyncTermBounded** - No stale syncs from old leaders accepted
5. **DesyncEventuallyCorrected** - Liveness guarantee

---

## Game Event System

The game has 6 owner-authoritative event types:

| Event | Owner Detects | Effect |
|-------|--------------|--------|
| `damage` | Player (self) | Reduce shields/lives |
| `death` | Player (self) | Mark dead, start respawn timer |
| `respawn` | Player (self) | Restore to spawn position |
| `pickup` | Player (self) | Grant powerup, remove from world |
| `weapon_pickup` | Player (self) | Add weapon to inventory |
| `enemy_damage` | Player (bullet owner) | Reduce enemy HP, trigger death |

### Event Flow

```
Local player detects collision
  → Simulation emits event (owner-authoritative)
  → LockstepNetcode broadcasts to peers
  → Remote peers apply event before their tick
  → All simulations converge to same state
```

---

## Model vs Reality Comparison

### What the Model Captures Well

| Aspect | Model Coverage |
|--------|---------------|
| Frame synchronization | Full - FrameBoundedDrift invariant |
| Leader election | Full - Raft protocol with terms |
| State sync ordering | Full - syncTerm validation |
| Local event preservation | Full - LocalEventsPreserved invariant |
| Network partitions | Full - LockstepNetwork model |
| Message loss | Full - LoseMessage action |
| Peer disconnect/reconnect | Full - connected state variable |

### What the Model Abstracts

| Game Feature | Model Representation | Why It's OK |
|--------------|---------------------|-------------|
| 6 event types | Generic `<<owner, frame>>` tuples | Deterministic sim handles semantics |
| Event ordering (damage→death→respawn) | Not modeled | Applied in frame order, deterministic |
| Enemy spawns/waves/bosses | Not modeled | Seeded RNG ensures consistency |
| Lives/game-over | Not modeled | Part of deterministic state |
| Score/multiplier | Not modeled | Included in checksum |
| Weapon system | Not modeled | Part of deterministic state |

---

## Why This Abstraction Works

### The Hard Problem (TLA+ Verified)

Distributed consensus in a P2P system:
- Who has authority to broadcast state?
- How do we prevent split-brain (two leaders)?
- How do we ensure all peers see same events?
- How do we recover from desync?

**These are the properties TLA+ verifies.**

### The Easy Problem (Deterministic Simulation)

Given the same inputs and events in the same order:
- What's the game state after N frames?

**This is handled by:**
1. Seeded PRNG (xorshift32)
2. Fixed-point math (16.16 format)
3. Consistent array iteration order
4. Synchronous execution (no async)
5. Checksum validation every 30 frames

---

## Coverage Analysis

```
TLA+ Model Scope:
┌─────────────────────────────────────────────────────────┐
│  Leader Election                                        │
│  ├── Term-based voting                                  │
│  ├── Heartbeat/timeout                                  │
│  └── Single leader per term                             │
│                                                         │
│  Frame Synchronization                                  │
│  ├── Input buffering                                    │
│  ├── Frame advance conditions                           │
│  └── Bounded drift guarantee                            │
│                                                         │
│  State Sync Protocol                                    │
│  ├── Term validation                                    │
│  ├── Local event preservation                           │
│  └── Desync recovery                                    │
│                                                         │
│  Network Fault Tolerance                                │
│  ├── Partitions                                         │
│  ├── Message loss                                       │
│  └── Disconnect/reconnect                               │
└─────────────────────────────────────────────────────────┘

Deterministic Simulation Scope (NOT in TLA+):
┌─────────────────────────────────────────────────────────┐
│  Game Events (damage, death, respawn, pickup, etc.)     │
│  Enemy System (spawns, waves, bosses, AI)               │
│  Player System (lives, shields, weapons, powerups)      │
│  Collision Detection                                    │
│  Score/Multiplier                                       │
│  Visual Effects (particles, screen shake)               │
└─────────────────────────────────────────────────────────┘
```

---

## Potential Model Extensions

If deeper game-semantic verification is needed:

### 1. Event Ordering Model

Verify damage→death→respawn cascade:
```tla
EventOrder ==
  \A e1, e2 \in events :
    e1.type = "death" /\ e2.type = "respawn" /\ e1.player = e2.player
    => e1.frame < e2.frame
```

### 2. Event Idempotence Model

Verify duplicate events don't corrupt state:
```tla
IdempotentPickup ==
  \A p \in Pickups :
    Cardinality({e \in appliedEvents : e.pickupId = p}) <= 1
```

### 3. Entity ID Consistency

Verify IDs remain unique across state syncs:
```tla
UniqueIds ==
  \A e1, e2 \in entities : e1 # e2 => e1.id # e2.id
```

---

## Conclusion

The TLA+ model is **appropriate for this game** because:

1. **It verifies the hard parts** - Distributed consensus, synchronization, and fault tolerance are notoriously difficult to get right. TLA+ proves these correct.

2. **It trusts determinism for the rest** - Game logic is inherently deterministic. Given same inputs + events, all clients compute identical state.

3. **Checksum catches divergence** - Any simulation bug causing desync is detected within 30 frames and corrected via state sync.

4. **Separation of concerns** - The netcode protocol is verified independently of game mechanics. This allows game features to evolve without re-verifying the protocol.

The model doesn't need to understand what "damage" or "respawn" means - it only needs to ensure that when player A emits an event, player B receives and applies it at the correct frame. The deterministic simulation handles the semantics.
