/**
 * Binary Protocol - Core definitions for binary message encoding
 *
 * Message format:
 * [1 byte header] [payload...]
 *
 * Header byte:
 * [7:4] Protocol version (0-15)
 * [3:0] Message type (0-15)
 *
 * Benefits:
 * - 95% bandwidth reduction vs JSON
 * - Faster parsing (no string allocation)
 * - Consistent byte ordering (little-endian)
 */

export const PROTOCOL_VERSION = 1

/**
 * Message types for binary protocol
 */
export enum MessageType {
  FrameInput = 0x0,
  FrameInputBatch = 0x1,
  StateSync = 0x2,
  StateSyncDelta = 0x3,  // Future: delta state sync
  RequestVote = 0x4,
  VoteResponse = 0x5,
  Heartbeat = 0x6,
  HeartbeatAck = 0x7,
  // Reserved: 0x8 - 0xE
  JsonFallback = 0xF,    // For debugging - wraps JSON in binary envelope
}

/**
 * Encode protocol header byte
 * @param version Protocol version (0-15)
 * @param type Message type
 * @returns Header byte
 */
export function encodeHeader(version: number, type: MessageType): number {
  return ((version & 0xF) << 4) | (type & 0xF)
}

/**
 * Decode protocol header byte
 * @param byte Header byte
 * @returns Version and message type
 */
export function decodeHeader(byte: number): { version: number; type: MessageType } {
  return {
    version: (byte >> 4) & 0xF,
    type: (byte & 0xF) as MessageType,
  }
}

/**
 * Check if message is a binary protocol message
 * (vs raw JSON string)
 */
export function isBinaryMessage(data: ArrayBuffer | string): data is ArrayBuffer {
  return data instanceof ArrayBuffer
}

/**
 * Get message type name for debugging
 */
export function getMessageTypeName(type: MessageType): string {
  const names: Record<MessageType, string> = {
    [MessageType.FrameInput]: 'FrameInput',
    [MessageType.FrameInputBatch]: 'FrameInputBatch',
    [MessageType.StateSync]: 'StateSync',
    [MessageType.StateSyncDelta]: 'StateSyncDelta',
    [MessageType.RequestVote]: 'RequestVote',
    [MessageType.VoteResponse]: 'VoteResponse',
    [MessageType.Heartbeat]: 'Heartbeat',
    [MessageType.HeartbeatAck]: 'HeartbeatAck',
    [MessageType.JsonFallback]: 'JsonFallback',
  }
  return names[type] ?? `Unknown(${type})`
}
