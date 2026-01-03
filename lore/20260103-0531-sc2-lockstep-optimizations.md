# SC2-Style Lockstep Optimizations

Implementation of StarCraft II-inspired networking optimizations for Astranyx's P2P lockstep netcode.

## Background

StarCraft II handles thousands of units with deterministic lockstep by only sending inputs, not state. Their key optimizations:

1. **Input Delay Scheduling** - Commands execute N frames in future (2-6 based on ping)
2. **Simulation Buckets** - Simulation runs at ~16-22 ticks/sec, rendering interpolates at 60+ FPS
3. **Binary Protocol** - Bit-packed commands, delta encoding, compression
4. **Dynamic Latency Adaptation** - Adjust delay based on measured RTT
5. **Input Batching** - Group multiple frames into single packets

## Current Astranyx Architecture

| Aspect | Current | After Optimization |
|--------|---------|-------------------|
| Simulation rate | 60 FPS | 16 ticks/sec |
| Render rate | 60 FPS | 60 FPS (interpolated) |
| Network sync | Every render frame | Every sim tick |
| Message format | JSON (~120 bytes) | Binary (~6 bytes) |
| Input delay | Fixed 3 frames | Dynamic 2-6 frames |
| Batching | None | Adaptive 1-4 frames |

## Optimization 1: Simulation Tick Separation

### Concept

Decouple simulation from rendering:
- **Simulation**: 30 ticks/second (33.33ms per tick) - deterministic game logic
- **Rendering**: 60 FPS - visual interpolation between sim states

### Why Fixed Ticks?

**Ticks must be fixed duration** for determinism:
- Both clients must run the exact same simulation
- Variable tick times would cause desync (different physics outcomes)
- Fixed tick = same inputs + same duration = identical output

The render loop uses an accumulator pattern - rendering happens at variable rate (vsync), but simulation ticks are always exactly 66.67ms.

### Benefits

1. **2x reduction in network traffic** - Sync 30 times/sec instead of 60
2. **Smoother visuals** - Interpolation hides network jitter
3. **Lower CPU load** - Simulation runs less frequently
4. **More forgiving latency** - 33.33ms tick window vs 16.67ms

### Implementation

```typescript
// Engine.ts changes
const SIM_TICK_RATE = 30          // 30 ticks per second
const SIM_TICK_MS = 1000 / 30     // 33.33ms per simulation tick (FIXED for determinism)
const RENDER_RATE = 60            // 60 FPS rendering

class Engine {
  private simAccumulator = 0
  private previousState: GameState | null = null
  private currentState: GameState | null = null

  update(deltaMs: number): void {
    this.simAccumulator += deltaMs

    // Run simulation at fixed 16Hz
    while (this.simAccumulator >= SIM_TICK_MS) {
      this.previousState = this.currentState?.clone()
      this.game.simulationTick()  // Deterministic tick
      this.currentState = this.game.getState()
      this.simAccumulator -= SIM_TICK_MS
    }

    // Interpolate for rendering
    const alpha = this.simAccumulator / SIM_TICK_MS
    this.renderer.render(this.previousState, this.currentState, alpha)
  }
}
```

### Interpolation Strategy

For each renderable entity:
- Position: `lerp(prev.x, curr.x, alpha)`
- Rotation: `slerp(prev.rotation, curr.rotation, alpha)`
- Non-interpolated: health, score, UI elements (snap to current)

### Files to Modify

| File | Changes |
|------|---------|
| `Engine.ts` | Separate sim tick from render, add interpolation alpha |
| `Simulation.ts` | Expose previous + current state for interpolation |
| `Renderer.ts` | Accept interpolation alpha, lerp positions |
| `LockstepNetcode.ts` | Sync per sim tick (16Hz) not render frame (60Hz) |

## Optimization 2: Binary Protocol

### Message Format

**Header (1 byte)**
```
[7:4] Protocol version (0-15)
[3:0] Message type (0-15)
```

**Message Types**
- 0x0: FrameInput
- 0x1: FrameInputBatch
- 0x2: StateSync
- 0x3: StateSyncDelta
- 0x4: RequestVote
- 0x5: VoteResponse
- 0x6: Heartbeat
- 0x7: HeartbeatAck
- 0xF: JSON Fallback

### FrameInput (6-14 bytes vs ~120 JSON)

```
Byte 0:    Header (version + type 0x0)
Byte 1:    Flags
  [0]   hasChecksum
  [1]   hasEvents
  [2-7] playerIndex (0-63)
Bytes 2-3: Input bits (16 bits, little-endian)
  [0] up, [1] down, [2] left, [3] right
  [4] fire, [5] special, [6] secondary, [7] swap
  [8] pickup, [9] pause, [10-15] reserved
Bytes 4-5: Tick number (16-bit, wraps at 65536)
Bytes 6-9: Checksum (if hasChecksum)
Bytes 10+: Events (if hasEvents)
```

### Event Encoding

```
DamageEvent (7 bytes):    [0x0][playerIdx][amount:2][shields:2][lives:1]
DeathEvent (2 bytes):     [0x1][playerIdx]
RespawnEvent (2 bytes):   [0x2][playerIdx]
PickupEvent (5 bytes):    [0x3][playerIdx][pickupId:3]
WeaponPickup (5 bytes):   [0x4][playerIdx][dropId:3]
EnemyDamage (10 bytes):   [0x5][ownerIdx][enemyId:3][amount:2][health:2][killed:1]
```

### StateSync

```
Byte 0:    Header (version + type 0x2)
Bytes 1-4: Tick (32-bit)
Bytes 5-8: Checksum (32-bit)
Bytes 9-12: Term (32-bit)
Bytes 13-16: Payload length (32-bit)
Bytes 17+: Compressed JSON (pako deflate)
```

### New Files

```
client/src/network/protocol/
  BinaryProtocol.ts      # Header, message types
  InputEncoder.ts        # FrameInput encode/decode
  EventEncoder.ts        # GameEvent encode/decode
  ElectionEncoder.ts     # Election messages
  StateSyncEncoder.ts    # Compressed state sync
  MessageCodec.ts        # Unified interface
  index.ts               # Barrel export
```

## Optimization 3: Input Batching

Adaptive batching based on network latency:

| Latency | Batch Size | Effect |
|---------|------------|--------|
| < 30ms | 1 | Send every tick |
| 30-60ms | 2 | Batch 2 ticks |
| 60-100ms | 3 | Batch 3 ticks |
| > 100ms | 4 | Max batch |

```typescript
class InputBatcher {
  private pending: TickInput[] = []
  private batchSize = 1

  add(input: TickInput): ArrayBuffer | null {
    this.pending.push(input)
    if (this.pending.length >= this.batchSize) {
      return this.flush()
    }
    return null
  }

  updateBatchSize(latencyMs: number): void {
    if (latencyMs < 30) this.batchSize = 1
    else if (latencyMs < 60) this.batchSize = 2
    else if (latencyMs < 100) this.batchSize = 3
    else this.batchSize = 4
  }
}
```

## Optimization 4: Dynamic Input Delay

Adjust input delay based on measured RTT via heartbeats:

```typescript
class InputDelayController {
  private rttSamples: number[] = []
  private currentDelay = 3  // ticks (not frames anymore!)

  addRttSample(rtt: number): void {
    this.rttSamples.push(rtt)
    if (this.rttSamples.length > 10) this.rttSamples.shift()
  }

  getDelay(): number {
    const avgRtt = average(this.rttSamples)
    // At 30Hz, each tick is 33.33ms
    const targetDelay = Math.ceil(avgRtt / 33.33) + 1
    return clamp(targetDelay, 2, 6)  // 2-6 ticks
  }
}
```

With 30Hz simulation:
- 2 ticks delay = 66ms (good for local/LAN)
- 4 ticks delay = 133ms (good for regional)
- 6 ticks delay = 200ms (playable for intercontinental)

## Implementation Order

1. **Simulation tick separation** (biggest architectural change)
   - Modify Engine.ts for dual-rate loop
   - Add interpolation to Renderer
   - Update LockstepNetcode for tick-based sync
2. **Binary protocol**
   - Create protocol/ directory with encoders
   - Integrate MessageCodec into LockstepNetcode
3. **Input batching**
   - Create InputBatcher class
   - Wire into tick loop
4. **Dynamic input delay**
   - Add RTT measurement to heartbeats
   - Create InputDelayController

## Bandwidth Impact

| Scenario | Before | After | Reduction |
|----------|--------|-------|-----------|
| Per-tick input | 120 B JSON | 6 B binary | 95% |
| Ticks per second | 60 | 30 | 50% |
| **Total bandwidth** | **14.4 KB/s** | **360 B/s** | **97.5%** |

## Terminology Change

After this implementation:
- "Frame" = render frame (60 FPS)
- "Tick" = simulation tick (16 Hz) - this is what lockstep syncs
- "Input delay" measured in ticks, not frames

## Testing Strategy

1. Verify determinism preserved (same tick = same checksum)
2. Visual smoothness with interpolation
3. Network traffic reduction measurements
4. Latency feel at various RTT values
