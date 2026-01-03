/**
 * StateSyncEncoder - Binary encoding for state sync messages
 *
 * StateSync format:
 * Byte 0:      Header (version + type 0x2)
 * Bytes 1-4:   Frame (32-bit LE)
 * Bytes 5-8:   Checksum (32-bit LE)
 * Bytes 9-12:  Term (32-bit LE)
 * Bytes 13-16: Payload length (32-bit LE)
 * Bytes 17+:   Compressed JSON state (pako deflate)
 *
 * Note: We use JSON + compression for state sync because:
 * 1. State structure is complex and variable
 * 2. Sent infrequently (every 5 seconds or on desync)
 * 3. Compression provides ~70% reduction
 * 4. Binary encoding the full state would be complex and error-prone
 */

import type { StateSyncMessage } from '../types.ts'
import { PROTOCOL_VERSION, MessageType, encodeHeader } from './BinaryProtocol.ts'

// Header size before payload
const STATE_SYNC_HEADER_SIZE = 17

/**
 * Encode StateSync message
 * Uses JSON + pako compression for the state payload
 */
export function encodeStateSync(message: StateSyncMessage): ArrayBuffer {
  // Serialize state to JSON
  const jsonState = JSON.stringify(message.state)
  const jsonBytes = new TextEncoder().encode(jsonState)

  // Compress using pako if available, otherwise use raw JSON
  let payload: Uint8Array
  let isCompressed = false

  // Try to use pako for compression (check if available)
  if (typeof globalThis !== 'undefined' && 'pako' in globalThis) {
    try {
      // @ts-expect-error - pako may be loaded globally
      payload = globalThis.pako.deflate(jsonBytes)
      isCompressed = true
    } catch {
      payload = jsonBytes
    }
  } else {
    // No compression available, use raw JSON
    payload = jsonBytes
  }

  // Create buffer
  const buffer = new ArrayBuffer(STATE_SYNC_HEADER_SIZE + payload.length)
  const view = new DataView(buffer)

  // Write header
  // Use 0x2 for compressed, 0x3 for uncompressed (reuse StateSyncDelta type for now)
  const type = isCompressed ? MessageType.StateSync : MessageType.StateSyncDelta
  view.setUint8(0, encodeHeader(PROTOCOL_VERSION, type))
  view.setUint32(1, message.frame, true)
  view.setUint32(5, message.checksum, true)
  view.setUint32(9, message.term, true)
  view.setUint32(13, payload.length, true)

  // Write payload
  new Uint8Array(buffer, STATE_SYNC_HEADER_SIZE).set(payload)

  return buffer
}

/**
 * Decode StateSync message
 */
export function decodeStateSync(buffer: ArrayBuffer): StateSyncMessage {
  const view = new DataView(buffer)

  // Read header
  const headerByte = view.getUint8(0)
  const isCompressed = (headerByte & 0xF) === MessageType.StateSync
  const frame = view.getUint32(1, true)
  const checksum = view.getUint32(5, true)
  const term = view.getUint32(9, true)
  const payloadLength = view.getUint32(13, true)

  // Read payload
  const payload = new Uint8Array(buffer, STATE_SYNC_HEADER_SIZE, payloadLength)

  // Decompress if needed
  let jsonBytes: Uint8Array
  if (isCompressed && typeof globalThis !== 'undefined' && 'pako' in globalThis) {
    try {
      // @ts-expect-error - pako may be loaded globally
      jsonBytes = globalThis.pako.inflate(payload)
    } catch {
      // Fallback: assume uncompressed
      jsonBytes = payload
    }
  } else {
    jsonBytes = payload
  }

  // Parse JSON
  const jsonState = new TextDecoder().decode(jsonBytes)
  const state = JSON.parse(jsonState)

  return {
    type: 'state_sync',
    frame,
    state,
    checksum,
    term,
  }
}

/**
 * Encode StateSync without compression (for debugging/fallback)
 */
export function encodeStateSyncUncompressed(message: StateSyncMessage): ArrayBuffer {
  const jsonState = JSON.stringify(message.state)
  const jsonBytes = new TextEncoder().encode(jsonState)

  const buffer = new ArrayBuffer(STATE_SYNC_HEADER_SIZE + jsonBytes.length)
  const view = new DataView(buffer)

  view.setUint8(0, encodeHeader(PROTOCOL_VERSION, MessageType.StateSyncDelta)) // Delta = uncompressed
  view.setUint32(1, message.frame, true)
  view.setUint32(5, message.checksum, true)
  view.setUint32(9, message.term, true)
  view.setUint32(13, jsonBytes.length, true)

  new Uint8Array(buffer, STATE_SYNC_HEADER_SIZE).set(jsonBytes)

  return buffer
}
