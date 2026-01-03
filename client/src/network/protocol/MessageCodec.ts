/**
 * MessageCodec - Unified binary encoding/decoding for all message types
 *
 * This is the main interface for the binary protocol.
 * Use this class to encode messages for sending and decode received messages.
 *
 * Features:
 * - Automatic message type detection
 * - JSON fallback for debugging
 * - Player ID <-> index mapping
 */

import type { NetMessage } from '../types.ts'
import { SafeConsole } from '../../core/SafeConsole.ts'
import {
  isFrameInput,
  isStateSyncMessage,
  isElectionMessage,
  isHeartbeatMessage,
} from '../types.ts'
import {
  PROTOCOL_VERSION,
  MessageType,
  decodeHeader,
  encodeHeader,
  getMessageTypeName,
} from './BinaryProtocol.ts'
import { encodeFrameInput, decodeFrameInput } from './InputEncoder.ts'
import { encodeStateSync, decodeStateSync } from './StateSyncEncoder.ts'
import {
  encodeRequestVote,
  decodeRequestVote,
  encodeVoteResponse,
  decodeVoteResponse,
  encodeHeartbeat,
  decodeHeartbeat,
  encodeHeartbeatAck,
  decodeHeartbeatAck,
} from './ElectionEncoder.ts'

export interface MessageCodecConfig {
  playerOrder: Map<string, number>
  useBinaryProtocol?: boolean // Default: true
  debug?: boolean // Log encoding stats
}

export class MessageCodec {
  private playerOrder: Map<string, number>
  private playerIdByIndex: string[]
  private useBinaryProtocol: boolean
  private debug: boolean

  // Stats for debugging
  private stats = {
    encoded: 0,
    decoded: 0,
    bytesSaved: 0,
  }

  constructor(config: MessageCodecConfig) {
    this.playerOrder = config.playerOrder
    this.useBinaryProtocol = config.useBinaryProtocol ?? true
    this.debug = config.debug ?? false

    // Build reverse lookup
    this.playerIdByIndex = Array.from(config.playerOrder.entries())
      .sort(([, a], [, b]) => a - b)
      .map(([id]) => id)
  }

  /**
   * Encode a message to binary or JSON
   * @param message The message to encode
   * @returns ArrayBuffer (binary) or string (JSON fallback)
   */
  encode(message: NetMessage): ArrayBuffer | string {
    if (!this.useBinaryProtocol) {
      return JSON.stringify(message)
    }

    const binary = this.encodeBinary(message)
    if (this.debug) {
      const jsonSize = JSON.stringify(message).length
      this.stats.encoded++
      this.stats.bytesSaved += jsonSize - binary.byteLength
    }
    return binary
  }

  /**
   * Decode a message from binary or JSON
   * @param data The raw data (ArrayBuffer or string)
   * @returns Decoded message
   */
  decode(data: ArrayBuffer | string): NetMessage {
    if (this.debug) {
      this.stats.decoded++
    }

    if (typeof data === 'string') {
      return JSON.parse(data)
    }

    return this.decodeBinary(data)
  }

  /**
   * Encode message to binary
   */
  private encodeBinary(message: NetMessage): ArrayBuffer {
    if (isFrameInput(message)) {
      return encodeFrameInput(message, this.playerOrder)
    }

    if (isStateSyncMessage(message)) {
      return encodeStateSync(message)
    }

    if (isElectionMessage(message)) {
      switch (message.type) {
        case 'request_vote':
          return encodeRequestVote(message, this.playerOrder)
        case 'vote_response':
          return encodeVoteResponse(message, this.playerOrder)
      }
    }

    if (isHeartbeatMessage(message)) {
      switch (message.type) {
        case 'heartbeat':
          return encodeHeartbeat(message, this.playerOrder)
        case 'heartbeat_ack':
          return encodeHeartbeatAck(message, this.playerOrder)
      }
    }

    // Fallback: wrap JSON in binary envelope
    return this.encodeJsonFallback(message)
  }

  /**
   * Decode binary message
   */
  private decodeBinary(buffer: ArrayBuffer): NetMessage {
    const view = new DataView(buffer)
    const header = decodeHeader(view.getUint8(0))

    if (header.version !== PROTOCOL_VERSION) {
      SafeConsole.warn(`Protocol version mismatch: expected ${PROTOCOL_VERSION}, got ${header.version}`)
    }

    switch (header.type) {
      case MessageType.FrameInput:
        return decodeFrameInput(buffer, this.playerIdByIndex)

      case MessageType.StateSync:
      case MessageType.StateSyncDelta:
        return decodeStateSync(buffer)

      case MessageType.RequestVote:
        return decodeRequestVote(buffer, this.playerIdByIndex)

      case MessageType.VoteResponse:
        return decodeVoteResponse(buffer, this.playerIdByIndex)

      case MessageType.Heartbeat:
        return decodeHeartbeat(buffer, this.playerIdByIndex)

      case MessageType.HeartbeatAck:
        return decodeHeartbeatAck(buffer, this.playerIdByIndex)

      case MessageType.JsonFallback:
        return this.decodeJsonFallback(buffer)

      default:
        throw new Error(`Unknown message type: ${getMessageTypeName(header.type)}`)
    }
  }

  /**
   * Encode message as JSON wrapped in binary envelope
   * Used as fallback for unknown message types
   */
  private encodeJsonFallback(message: NetMessage): ArrayBuffer {
    const json = JSON.stringify(message)
    const jsonBytes = new TextEncoder().encode(json)

    const buffer = new ArrayBuffer(1 + jsonBytes.length)
    const view = new DataView(buffer)

    view.setUint8(0, encodeHeader(PROTOCOL_VERSION, MessageType.JsonFallback))
    new Uint8Array(buffer, 1).set(jsonBytes)

    return buffer
  }

  /**
   * Decode JSON from binary envelope
   */
  private decodeJsonFallback(buffer: ArrayBuffer): NetMessage {
    const jsonBytes = new Uint8Array(buffer, 1)
    const json = new TextDecoder().decode(jsonBytes)
    return JSON.parse(json)
  }

  /**
   * Get encoding statistics (for debugging)
   */
  getStats(): { encoded: number; decoded: number; bytesSaved: number } {
    return { ...this.stats }
  }

  /**
   * Reset statistics
   */
  resetStats(): void {
    this.stats = { encoded: 0, decoded: 0, bytesSaved: 0 }
  }

  /**
   * Enable/disable binary protocol at runtime
   */
  setUseBinaryProtocol(enabled: boolean): void {
    this.useBinaryProtocol = enabled
  }

  /**
   * Check if using binary protocol
   */
  isUsingBinaryProtocol(): boolean {
    return this.useBinaryProtocol
  }
}
