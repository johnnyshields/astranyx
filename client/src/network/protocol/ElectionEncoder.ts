/**
 * ElectionEncoder - Binary encoding for leader election messages
 *
 * RequestVote (8 bytes):
 * Byte 0:    Header (version + type 0x4)
 * Bytes 1-4: Term (32-bit LE)
 * Byte 5:    CandidateIndex
 * Bytes 6-7: LastFrame (16-bit LE)
 *
 * VoteResponse (5 bytes):
 * Byte 0:    Header (version + type 0x5)
 * Bytes 1-3: Term (24-bit LE)
 * Byte 4:    Flags [0]=voteGranted, [1-7]=voterIndex
 *
 * Heartbeat (14 bytes with timestamp, 8 without):
 * Byte 0:    Header (version + type 0x6)
 * Bytes 1-4: Term (32-bit LE)
 * Byte 5:    LeaderIndex
 * Bytes 6-7: Frame (16-bit LE)
 * Bytes 8-13: Timestamp (48-bit LE, optional - if buffer size > 8)
 *
 * HeartbeatAck (14 bytes with timestamp, 8 without):
 * Byte 0:    Header (version + type 0x7)
 * Bytes 1-4: Term (32-bit LE)
 * Byte 5:    PeerIndex
 * Bytes 6-7: Frame (16-bit LE)
 * Bytes 8-13: Timestamp (48-bit LE, optional - echoed from heartbeat)
 */

import type {
  RequestVoteMessage,
  VoteResponseMessage,
  HeartbeatMessage,
  HeartbeatAckMessage,
} from '../types.ts'
import { PROTOCOL_VERSION, MessageType, encodeHeader } from './BinaryProtocol.ts'

// Message sizes (base without optional fields)
export const REQUEST_VOTE_SIZE = 8
export const VOTE_RESPONSE_SIZE = 5
export const HEARTBEAT_SIZE = 8
export const HEARTBEAT_SIZE_WITH_TIMESTAMP = 14
export const HEARTBEAT_ACK_SIZE = 8
export const HEARTBEAT_ACK_SIZE_WITH_TIMESTAMP = 14

/**
 * Encode RequestVote message
 */
export function encodeRequestVote(
  message: RequestVoteMessage,
  playerOrder: Map<string, number>
): ArrayBuffer {
  const buffer = new ArrayBuffer(REQUEST_VOTE_SIZE)
  const view = new DataView(buffer)

  view.setUint8(0, encodeHeader(PROTOCOL_VERSION, MessageType.RequestVote))
  view.setUint32(1, message.term, true)
  view.setUint8(5, playerOrder.get(message.candidateId) ?? 0)
  view.setUint16(6, (message.lastFrame ?? 0) & 0xFFFF, true)

  return buffer
}

/**
 * Decode RequestVote message
 */
export function decodeRequestVote(
  buffer: ArrayBuffer,
  playerIdByIndex: string[]
): RequestVoteMessage {
  const view = new DataView(buffer)

  const term = view.getUint32(1, true)
  const candidateIndex = view.getUint8(5)
  const lastSyncFrame = view.getUint16(6, true)

  return {
    type: 'request_vote',
    term,
    candidateId: playerIdByIndex[candidateIndex] ?? `player_${candidateIndex}`,
    lastFrame: lastSyncFrame,
  }
}

/**
 * Encode VoteResponse message
 */
export function encodeVoteResponse(
  message: VoteResponseMessage,
  playerOrder: Map<string, number>
): ArrayBuffer {
  const buffer = new ArrayBuffer(VOTE_RESPONSE_SIZE)
  const view = new DataView(buffer)

  view.setUint8(0, encodeHeader(PROTOCOL_VERSION, MessageType.VoteResponse))
  // 24-bit term (little-endian)
  view.setUint8(1, message.term & 0xFF)
  view.setUint8(2, (message.term >> 8) & 0xFF)
  view.setUint8(3, (message.term >> 16) & 0xFF)
  // Flags byte: voteGranted + voterIndex
  const voterIndex = playerOrder.get(message.voterId) ?? 0
  const flags = (message.voteGranted ? 1 : 0) | (voterIndex << 1)
  view.setUint8(4, flags)

  return buffer
}

/**
 * Decode VoteResponse message
 */
export function decodeVoteResponse(
  buffer: ArrayBuffer,
  playerIdByIndex: string[]
): VoteResponseMessage {
  const view = new DataView(buffer)

  // 24-bit term
  const term = view.getUint8(1) |
               (view.getUint8(2) << 8) |
               (view.getUint8(3) << 16)
  const flags = view.getUint8(4)
  const voteGranted = !!(flags & 1)
  const voterIndex = flags >> 1

  return {
    type: 'vote_response',
    term,
    voteGranted,
    voterId: playerIdByIndex[voterIndex] ?? `player_${voterIndex}`,
  }
}

/**
 * Encode Heartbeat message
 */
export function encodeHeartbeat(
  message: HeartbeatMessage,
  playerOrder: Map<string, number>
): ArrayBuffer {
  const hasTimestamp = message.timestamp !== undefined
  const size = hasTimestamp ? HEARTBEAT_SIZE_WITH_TIMESTAMP : HEARTBEAT_SIZE
  const buffer = new ArrayBuffer(size)
  const view = new DataView(buffer)

  view.setUint8(0, encodeHeader(PROTOCOL_VERSION, MessageType.Heartbeat))
  view.setUint32(1, message.term, true)
  view.setUint8(5, playerOrder.get(message.leaderId) ?? 0)
  view.setUint16(6, message.frame & 0xFFFF, true)

  if (hasTimestamp) {
    // 48-bit timestamp (little-endian): low 32 bits + high 16 bits
    const ts = message.timestamp!
    view.setUint32(8, ts & 0xFFFFFFFF, true)
    view.setUint16(12, Math.floor(ts / 0x100000000) & 0xFFFF, true)
  }

  return buffer
}

/**
 * Decode Heartbeat message
 */
export function decodeHeartbeat(
  buffer: ArrayBuffer,
  playerIdByIndex: string[]
): HeartbeatMessage {
  const view = new DataView(buffer)

  const term = view.getUint32(1, true)
  const leaderIndex = view.getUint8(5)
  const frame = view.getUint16(6, true)

  const result: HeartbeatMessage = {
    type: 'heartbeat',
    term,
    leaderId: playerIdByIndex[leaderIndex] ?? `player_${leaderIndex}`,
    frame,
  }

  // Read optional timestamp if buffer is large enough
  if (buffer.byteLength >= HEARTBEAT_SIZE_WITH_TIMESTAMP) {
    const low = view.getUint32(8, true)
    const high = view.getUint16(12, true)
    result.timestamp = low + high * 0x100000000
  }

  return result
}

/**
 * Encode HeartbeatAck message
 */
export function encodeHeartbeatAck(
  message: HeartbeatAckMessage,
  playerOrder: Map<string, number>
): ArrayBuffer {
  const hasTimestamp = message.timestamp !== undefined
  const size = hasTimestamp ? HEARTBEAT_ACK_SIZE_WITH_TIMESTAMP : HEARTBEAT_ACK_SIZE
  const buffer = new ArrayBuffer(size)
  const view = new DataView(buffer)

  view.setUint8(0, encodeHeader(PROTOCOL_VERSION, MessageType.HeartbeatAck))
  view.setUint32(1, message.term, true)
  view.setUint8(5, playerOrder.get(message.peerId) ?? 0)
  view.setUint16(6, message.frame & 0xFFFF, true)

  if (hasTimestamp) {
    // 48-bit timestamp (little-endian): low 32 bits + high 16 bits
    const ts = message.timestamp!
    view.setUint32(8, ts & 0xFFFFFFFF, true)
    view.setUint16(12, Math.floor(ts / 0x100000000) & 0xFFFF, true)
  }

  return buffer
}

/**
 * Decode HeartbeatAck message
 */
export function decodeHeartbeatAck(
  buffer: ArrayBuffer,
  playerIdByIndex: string[]
): HeartbeatAckMessage {
  const view = new DataView(buffer)

  const term = view.getUint32(1, true)
  const peerIndex = view.getUint8(5)
  const frame = view.getUint16(6, true)

  const result: HeartbeatAckMessage = {
    type: 'heartbeat_ack',
    term,
    peerId: playerIdByIndex[peerIndex] ?? `player_${peerIndex}`,
    frame,
  }

  // Read optional timestamp if buffer is large enough
  if (buffer.byteLength >= HEARTBEAT_ACK_SIZE_WITH_TIMESTAMP) {
    const low = view.getUint32(8, true)
    const high = view.getUint16(12, true)
    result.timestamp = low + high * 0x100000000
  }

  return result
}
