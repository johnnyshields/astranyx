/**
 * InputEncoder - Binary encoding for FrameInput messages
 *
 * FrameInput binary format (6-14+ bytes):
 * Byte 0:    Header (version + type 0x0)
 * Byte 1:    Flags + playerIndex
 *   [0]   hasChecksum
 *   [1]   hasEvents
 *   [2-7] playerIndex (0-63)
 * Bytes 2-3: Input bits (16 bits, little-endian)
 *   [0] up, [1] down, [2] left, [3] right
 *   [4] fire, [5] special, [6] secondary, [7] swap
 *   [8] pickup, [9] pause, [10-15] reserved
 * Bytes 4-5: Frame/tick number (16-bit, little-endian)
 * Bytes 6-9: Checksum (if hasChecksum, 32-bit LE)
 * Bytes 10+: Events (if hasEvents, see EventEncoder)
 *
 * JSON comparison: ~120 bytes -> 6-10 bytes = 92-95% reduction
 */

import type { PlayerInput, FrameInput, GameEvent } from '../types.ts'
import { emptyInput } from '../types.ts'
import { PROTOCOL_VERSION, MessageType, encodeHeader, decodeHeader } from './BinaryProtocol.ts'
import { encodeEvents, decodeEvents, calculateEventsSize } from './EventEncoder.ts'

/**
 * Encode PlayerInput to 16-bit bitfield
 */
export function encodePlayerInput(input: PlayerInput): number {
  let bits = 0
  if (input.up) bits |= (1 << 0)
  if (input.down) bits |= (1 << 1)
  if (input.left) bits |= (1 << 2)
  if (input.right) bits |= (1 << 3)
  if (input.fire) bits |= (1 << 4)
  if (input.special) bits |= (1 << 5)
  if (input.secondary) bits |= (1 << 6)
  if (input.swap) bits |= (1 << 7)
  if (input.pickup) bits |= (1 << 8)
  if (input.pause) bits |= (1 << 9)
  return bits
}

/**
 * Decode 16-bit bitfield to PlayerInput
 */
export function decodePlayerInput(bits: number): PlayerInput {
  return {
    up: !!(bits & (1 << 0)),
    down: !!(bits & (1 << 1)),
    left: !!(bits & (1 << 2)),
    right: !!(bits & (1 << 3)),
    fire: !!(bits & (1 << 4)),
    special: !!(bits & (1 << 5)),
    secondary: !!(bits & (1 << 6)),
    swap: !!(bits & (1 << 7)),
    pickup: !!(bits & (1 << 8)),
    pause: !!(bits & (1 << 9)),
  }
}

/**
 * Encode FrameInput to binary ArrayBuffer
 * @param input The frame input to encode
 * @param playerOrder Map of player ID to index (0-63)
 * @returns Binary ArrayBuffer
 */
export function encodeFrameInput(
  input: FrameInput,
  playerOrder: Map<string, number>
): ArrayBuffer {
  const playerIndex = playerOrder.get(input.playerId) ?? 0
  const hasChecksum = input.checksum !== undefined
  const hasEvents = input.events && input.events.length > 0

  // Calculate size
  let size = 6 // Header + flags + inputBits + frame
  if (hasChecksum) size += 4
  if (hasEvents) size += calculateEventsSize(input.events!)

  const buffer = new ArrayBuffer(size)
  const view = new DataView(buffer)

  let offset = 0

  // Byte 0: Header
  view.setUint8(offset++, encodeHeader(PROTOCOL_VERSION, MessageType.FrameInput))

  // Byte 1: Flags + playerIndex
  const flags = (hasChecksum ? 1 : 0) | (hasEvents ? 2 : 0) | (playerIndex << 2)
  view.setUint8(offset++, flags)

  // Bytes 2-3: Input bits (little-endian)
  view.setUint16(offset, encodePlayerInput(input.input), true)
  offset += 2

  // Bytes 4-5: Frame number (little-endian, 16-bit wraps at 65536)
  view.setUint16(offset, input.frame & 0xFFFF, true)
  offset += 2

  // Bytes 6-9: Checksum (optional)
  if (hasChecksum) {
    view.setUint32(offset, input.checksum!, true)
    offset += 4
  }

  // Events (optional)
  if (hasEvents) {
    encodeEvents(view, offset, input.events!, playerOrder)
  }

  return buffer
}

/**
 * Decode binary ArrayBuffer to FrameInput
 * @param buffer Binary data
 * @param playerIdByIndex Array mapping index to player ID
 * @returns Decoded FrameInput
 */
export function decodeFrameInput(
  buffer: ArrayBuffer,
  playerIdByIndex: string[]
): FrameInput {
  const view = new DataView(buffer)
  let offset = 0

  // Byte 0: Header (skip, already validated)
  offset++

  // Byte 1: Flags + playerIndex
  const flagsByte = view.getUint8(offset++)
  const hasChecksum = !!(flagsByte & 1)
  const hasEvents = !!(flagsByte & 2)
  const playerIndex = flagsByte >> 2

  // Bytes 2-3: Input bits
  const inputBits = view.getUint16(offset, true)
  offset += 2

  // Bytes 4-5: Frame number
  const frame = view.getUint16(offset, true)
  offset += 2

  // Checksum (optional)
  let checksum: number | undefined
  if (hasChecksum) {
    checksum = view.getUint32(offset, true)
    offset += 4
  }

  // Events (optional)
  let events: GameEvent[] | undefined
  if (hasEvents) {
    events = decodeEvents(view, offset, buffer.byteLength - offset, playerIdByIndex)
  }

  return {
    frame,
    playerId: playerIdByIndex[playerIndex] ?? `player_${playerIndex}`,
    input: decodePlayerInput(inputBits),
    checksum,
    events,
  }
}

/**
 * Calculate size of encoded FrameInput
 */
export function calculateFrameInputSize(input: FrameInput): number {
  let size = 6 // Base size
  if (input.checksum !== undefined) size += 4
  if (input.events && input.events.length > 0) {
    size += calculateEventsSize(input.events)
  }
  return size
}
