# Binary Protocol

This document describes the SC2-inspired binary protocol optimizations implemented for Astranyx's P2P lockstep netcode.

## Overview

The binary protocol provides:
- **95% bandwidth reduction** vs JSON for frame inputs
- **Input batching** to reduce packet overhead at high latencies
- **Dynamic input delay** based on measured RTT
- **JSON fallback** for debugging

## Files

| File | Purpose |
|------|---------|
| `protocol/BinaryProtocol.ts` | Message type IDs, header encode/decode |
| `protocol/InputEncoder.ts` | FrameInput binary encode/decode |
| `protocol/EventEncoder.ts` | GameEvent binary encode/decode |
| `protocol/ElectionEncoder.ts` | Election message encoding |
| `protocol/StateSyncEncoder.ts` | StateSync with pako compression |
| `protocol/MessageCodec.ts` | Unified codec class |
| `InputBatcher.ts` | Adaptive input batching |
| `InputDelayController.ts` | Dynamic input delay from RTT |

## Binary Format

### Message Header (1 byte)

```
[4 bits version][4 bits type]
```

- Version: Currently 1
- Type: 0=FrameInput, 1=StateSync, 2=RequestVote, 3=VoteResponse, 4=Heartbeat, 5=HeartbeatAck

### FrameInput (6-14 bytes vs ~120 JSON)

```
[1B header][1B flags+playerIdx][2B input bits][2B frame][4B checksum?][events?]
```

- **Flags** (3 bits): hasChecksum, hasEvents, reserved
- **Player index** (5 bits): 0-31 players
- **Input bits** (16-bit bitfield):
  - Bit 0: up
  - Bit 1: down
  - Bit 2: left
  - Bit 3: right
  - Bit 4: fire
  - Bit 5: special
  - Bit 6: secondary
  - Bit 7: swap
  - Bit 8: pickup
  - Bit 9: pause
- **Frame** (16-bit): Wraps at 65535
- **Checksum** (32-bit, optional): CRC32 of game state
- **Events** (variable, optional): JSON encoded for flexibility

### Heartbeat (6-14 bytes)

```
[1B header][1B player index][2B term][2B frame][6B timestamp?]
```

- Timestamp is optional, used for RTT measurement
- Uses 48-bit (6 byte) timestamp with millisecond precision

### State Sync (variable)

```
[1B header][4B frame][4B checksum][4B term][4B payload length][compressed payload]
```

- Payload is pako-compressed JSON of game state

## Input Batching

SC2-style adaptive batching reduces packet overhead at high latencies.

### Batch Size Rules

| RTT | Batch Size |
|-----|------------|
| < 30ms | 1 (send every tick) |
| 30-60ms | 2 |
| 60-100ms | 3 |
| > 100ms | 4 (max) |

### Max Batch Delay

Maximum 33ms (1 simulation tick at 30Hz) to prevent input lag.

## Dynamic Input Delay

Input delay is calculated from RTT to hide network latency.

### Formula

```
delay_ticks = ceil(avg_rtt / tick_ms) + jitter_buffer
```

### Bounds

- Minimum: 2 ticks (66ms at 30Hz)
- Maximum: 6 ticks (200ms at 30Hz)
- Changes by max 1 tick per second (smooth transitions)

### RTT Measurement

RTT is measured via heartbeat timestamps:

1. Leader sends `HeartbeatMessage` with `timestamp = Date.now()`
2. Follower responds with `HeartbeatAckMessage` echoing the timestamp
3. Leader calculates `rtt = Date.now() - ack.timestamp`

## Configuration

Use `protocolMode` in `LockstepConfig`:

```typescript
const config: LockstepConfig = {
  // ... other config
  protocolMode: 'binary', // default
  // or
  protocolMode: 'json',   // for debugging
}
```

## Bandwidth Impact

| Message | JSON | Binary | Savings |
|---------|------|--------|---------|
| FrameInput | ~120B | 6B | 95% |
| Heartbeat | ~80B | 6B | 93% |
| StateSync | ~10KB | ~3KB | 70% |

At 30Hz with 2 players: **7.2 KB/s → 360 B/s**

## Protocol Detection

The codec automatically detects binary vs JSON on receive:

```typescript
// Binary messages start with valid header byte
if (data instanceof ArrayBuffer) {
  const view = new DataView(data)
  const header = view.getUint8(0)
  const version = (header >> 4) & 0x0F
  const type = header & 0x0F
  if (version === 1 && type <= 5) {
    // Binary message
  }
}
```

This allows mixing binary and JSON messages during transitions.
