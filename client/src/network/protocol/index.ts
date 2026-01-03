/**
 * Binary Protocol - Barrel exports
 *
 * Usage:
 * ```typescript
 * import { MessageCodec } from './protocol'
 *
 * const codec = new MessageCodec({ playerOrder })
 * const binary = codec.encode(message)
 * const decoded = codec.decode(binary)
 * ```
 */

// Core protocol
export {
  PROTOCOL_VERSION,
  MessageType,
  encodeHeader,
  decodeHeader,
  isBinaryMessage,
  getMessageTypeName,
} from './BinaryProtocol.ts'

// Input encoding
export {
  encodePlayerInput,
  decodePlayerInput,
  encodeFrameInput,
  decodeFrameInput,
  calculateFrameInputSize,
} from './InputEncoder.ts'

// Event encoding
export {
  encodeEvents,
  decodeEvents,
  calculateEventsSize,
} from './EventEncoder.ts'

// Election encoding
export {
  encodeRequestVote,
  decodeRequestVote,
  encodeVoteResponse,
  decodeVoteResponse,
  encodeHeartbeat,
  decodeHeartbeat,
  encodeHeartbeatAck,
  decodeHeartbeatAck,
} from './ElectionEncoder.ts'

// State sync encoding
export {
  encodeStateSync,
  decodeStateSync,
  encodeStateSyncUncompressed,
} from './StateSyncEncoder.ts'

// Unified codec
export { MessageCodec, type MessageCodecConfig } from './MessageCodec.ts'
