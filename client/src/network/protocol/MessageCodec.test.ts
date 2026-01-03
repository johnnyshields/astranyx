import { describe, it, expect, vi, beforeEach } from 'vitest'
import { MessageCodec, type MessageCodecConfig } from './MessageCodec'
import type {
  FrameInput,
  StateSyncMessage,
  RequestVoteMessage,
  VoteResponseMessage,
  HeartbeatMessage,
  HeartbeatAckMessage,
  PlayerInput,
  GameEvent,
} from '../types'

function createPlayerOrder(): Map<string, number> {
  return new Map([
    ['player1', 0],
    ['player2', 1],
  ])
}

function createEmptyInput(): PlayerInput {
  return {
    up: false,
    down: false,
    left: false,
    right: false,
    fire: false,
    special: false,
    secondary: false,
    swap: false,
    pickup: false,
    pause: false,
  }
}

function createCodecConfig(overrides?: Partial<MessageCodecConfig>): MessageCodecConfig {
  return {
    playerOrder: createPlayerOrder(),
    ...overrides,
  }
}

describe('MessageCodec', () => {
  describe('constructor', () => {
    it('should create codec with default settings', () => {
      const codec = new MessageCodec(createCodecConfig())
      expect(codec.isUsingBinaryProtocol()).toBe(true)
    })

    it('should allow disabling binary protocol (JSON mode)', () => {
      const codec = new MessageCodec(createCodecConfig({ useBinaryProtocol: false }))
      expect(codec.isUsingBinaryProtocol()).toBe(false)
    })

    it('should build player index lookup', () => {
      const codec = new MessageCodec(createCodecConfig())
      // The codec should work with the player order
      const message: HeartbeatMessage = {
        type: 'heartbeat',
        term: 1,
        leaderId: 'player2',
        frame: 100,
      }
      const encoded = codec.encode(message)
      const decoded = codec.decode(encoded) as HeartbeatMessage
      expect(decoded.leaderId).toBe('player2')
    })
  })

  describe('FrameInput encoding', () => {
    let codec: MessageCodec

    beforeEach(() => {
      codec = new MessageCodec(createCodecConfig())
    })

    it('should encode and decode basic FrameInput', () => {
      const message: FrameInput = {
        frame: 500,
        playerId: 'player1',
        input: createEmptyInput(),
      }

      const encoded = codec.encode(message)
      expect(encoded).toBeInstanceOf(ArrayBuffer)

      const decoded = codec.decode(encoded) as FrameInput
      expect(decoded.frame).toBe(500)
      expect(decoded.playerId).toBe('player1')
      expect(decoded.input).toEqual(createEmptyInput())
    })

    it('should encode and decode FrameInput with inputs', () => {
      const input: PlayerInput = {
        ...createEmptyInput(),
        up: true,
        fire: true,
      }

      const message: FrameInput = {
        frame: 1000,
        playerId: 'player2',
        input,
      }

      const encoded = codec.encode(message)
      const decoded = codec.decode(encoded) as FrameInput

      expect(decoded.input.up).toBe(true)
      expect(decoded.input.fire).toBe(true)
      expect(decoded.input.down).toBe(false)
    })

    it('should encode and decode FrameInput with checksum', () => {
      const message: FrameInput = {
        frame: 200,
        playerId: 'player1',
        input: createEmptyInput(),
        checksum: 0xCAFEBABE,
      }

      const encoded = codec.encode(message)
      const decoded = codec.decode(encoded) as FrameInput

      expect(decoded.checksum).toBe(0xCAFEBABE)
    })

    it('should encode and decode FrameInput with events', () => {
      const events: GameEvent[] = [
        { type: 'damage', playerId: 'player1', amount: 50, newShields: 50, newLives: 3 },
      ]

      const message: FrameInput = {
        frame: 300,
        playerId: 'player1',
        input: createEmptyInput(),
        events,
      }

      const encoded = codec.encode(message)
      const decoded = codec.decode(encoded) as FrameInput

      expect(decoded.events).toBeDefined()
      expect(decoded.events!.length).toBe(1)
      expect(decoded.events![0]!.type).toBe('damage')
    })
  })

  describe('StateSyncMessage encoding', () => {
    let codec: MessageCodec

    beforeEach(() => {
      codec = new MessageCodec(createCodecConfig())
    })

    it('should encode and decode StateSync', () => {
      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 1000,
        checksum: 12345,
        term: 5,
        state: { players: [], enemies: [] },
      }

      const encoded = codec.encode(message)
      expect(encoded).toBeInstanceOf(ArrayBuffer)

      const decoded = codec.decode(encoded) as StateSyncMessage
      expect(decoded.type).toBe('state_sync')
      expect(decoded.frame).toBe(1000)
      expect(decoded.checksum).toBe(12345)
      expect(decoded.term).toBe(5)
      expect(decoded.state).toEqual({ players: [], enemies: [] })
    })
  })

  describe('Election message encoding', () => {
    let codec: MessageCodec

    beforeEach(() => {
      codec = new MessageCodec(createCodecConfig())
    })

    it('should encode and decode RequestVote', () => {
      const message: RequestVoteMessage = {
        type: 'request_vote',
        term: 3,
        candidateId: 'player1',
        lastFrame: 500,
      }

      const encoded = codec.encode(message)
      const decoded = codec.decode(encoded) as RequestVoteMessage

      expect(decoded.type).toBe('request_vote')
      expect(decoded.term).toBe(3)
      expect(decoded.candidateId).toBe('player1')
      expect(decoded.lastFrame).toBe(500)
    })

    it('should encode and decode VoteResponse', () => {
      const message: VoteResponseMessage = {
        type: 'vote_response',
        term: 3,
        voteGranted: true,
        voterId: 'player2',
      }

      const encoded = codec.encode(message)
      const decoded = codec.decode(encoded) as VoteResponseMessage

      expect(decoded.type).toBe('vote_response')
      expect(decoded.term).toBe(3)
      expect(decoded.voteGranted).toBe(true)
      expect(decoded.voterId).toBe('player2')
    })
  })

  describe('Heartbeat message encoding', () => {
    let codec: MessageCodec

    beforeEach(() => {
      codec = new MessageCodec(createCodecConfig())
    })

    it('should encode and decode Heartbeat', () => {
      const message: HeartbeatMessage = {
        type: 'heartbeat',
        term: 10,
        leaderId: 'player1',
        frame: 2000,
      }

      const encoded = codec.encode(message)
      const decoded = codec.decode(encoded) as HeartbeatMessage

      expect(decoded.type).toBe('heartbeat')
      expect(decoded.term).toBe(10)
      expect(decoded.leaderId).toBe('player1')
      expect(decoded.frame).toBe(2000)
    })

    it('should encode and decode Heartbeat with timestamp', () => {
      const timestamp = Date.now()
      const message: HeartbeatMessage = {
        type: 'heartbeat',
        term: 10,
        leaderId: 'player1',
        frame: 2000,
        timestamp,
      }

      const encoded = codec.encode(message)
      const decoded = codec.decode(encoded) as HeartbeatMessage

      expect(decoded.timestamp).toBe(timestamp)
    })

    it('should encode and decode HeartbeatAck', () => {
      const message: HeartbeatAckMessage = {
        type: 'heartbeat_ack',
        term: 10,
        peerId: 'player2',
        frame: 2000,
      }

      const encoded = codec.encode(message)
      const decoded = codec.decode(encoded) as HeartbeatAckMessage

      expect(decoded.type).toBe('heartbeat_ack')
      expect(decoded.term).toBe(10)
      expect(decoded.peerId).toBe('player2')
      expect(decoded.frame).toBe(2000)
    })

    it('should encode and decode HeartbeatAck with timestamp', () => {
      const timestamp = 1700000000000
      const message: HeartbeatAckMessage = {
        type: 'heartbeat_ack',
        term: 10,
        peerId: 'player2',
        frame: 2000,
        timestamp,
      }

      const encoded = codec.encode(message)
      const decoded = codec.decode(encoded) as HeartbeatAckMessage

      expect(decoded.timestamp).toBe(timestamp)
    })
  })

  describe('JSON fallback', () => {
    it('should use JSON when binary protocol disabled', () => {
      const codec = new MessageCodec(createCodecConfig({ useBinaryProtocol: false }))

      const message: HeartbeatMessage = {
        type: 'heartbeat',
        term: 1,
        leaderId: 'player1',
        frame: 100,
      }

      const encoded = codec.encode(message)
      expect(typeof encoded).toBe('string')

      const decoded = codec.decode(encoded) as HeartbeatMessage
      expect(decoded.type).toBe('heartbeat')
    })

    it('should decode JSON strings', () => {
      const codec = new MessageCodec(createCodecConfig())

      const json = JSON.stringify({
        type: 'heartbeat',
        term: 1,
        leaderId: 'player1',
        frame: 100,
      })

      const decoded = codec.decode(json) as HeartbeatMessage
      expect(decoded.type).toBe('heartbeat')
    })
  })

  describe('setUseBinaryProtocol', () => {
    it('should allow toggling binary protocol at runtime', () => {
      const codec = new MessageCodec(createCodecConfig())
      expect(codec.isUsingBinaryProtocol()).toBe(true)

      codec.setUseBinaryProtocol(false)
      expect(codec.isUsingBinaryProtocol()).toBe(false)

      const message: HeartbeatMessage = {
        type: 'heartbeat',
        term: 1,
        leaderId: 'player1',
        frame: 100,
      }

      const encoded = codec.encode(message)
      expect(typeof encoded).toBe('string')

      codec.setUseBinaryProtocol(true)
      const encodedBinary = codec.encode(message)
      expect(encodedBinary).toBeInstanceOf(ArrayBuffer)
    })
  })

  describe('stats', () => {
    it('should track encoding stats when debug enabled', () => {
      const codec = new MessageCodec(createCodecConfig({ debug: true }))

      const message: HeartbeatMessage = {
        type: 'heartbeat',
        term: 1,
        leaderId: 'player1',
        frame: 100,
      }

      codec.encode(message)
      codec.encode(message)
      codec.encode(message)

      const stats = codec.getStats()
      expect(stats.encoded).toBe(3)
    })

    it('should track decoding stats when debug enabled', () => {
      const codec = new MessageCodec(createCodecConfig({ debug: true }))

      const message: HeartbeatMessage = {
        type: 'heartbeat',
        term: 1,
        leaderId: 'player1',
        frame: 100,
      }

      const encoded = codec.encode(message)
      codec.decode(encoded)
      codec.decode(encoded)

      const stats = codec.getStats()
      expect(stats.decoded).toBe(2)
    })

    it('should calculate bytes saved', () => {
      const codec = new MessageCodec(createCodecConfig({ debug: true }))

      // Large state sync message should show significant savings
      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 1000,
        checksum: 12345,
        term: 5,
        state: {
          players: [
            { id: 'player1', x: 100, y: 200, health: 100 },
            { id: 'player2', x: 300, y: 400, health: 75 },
          ],
          enemies: Array(10).fill({ id: 'e', x: 0, y: 0 }),
        },
      }

      codec.encode(message)
      const stats = codec.getStats()

      // Binary should save bytes vs JSON
      expect(stats.bytesSaved).toBeDefined()
    })

    it('should reset stats', () => {
      const codec = new MessageCodec(createCodecConfig({ debug: true }))

      const message: HeartbeatMessage = {
        type: 'heartbeat',
        term: 1,
        leaderId: 'player1',
        frame: 100,
      }

      codec.encode(message)
      codec.resetStats()

      const stats = codec.getStats()
      expect(stats.encoded).toBe(0)
      expect(stats.decoded).toBe(0)
      expect(stats.bytesSaved).toBe(0)
    })
  })

  describe('error handling', () => {
    it('should handle invalid buffer gracefully', () => {
      const codec = new MessageCodec(createCodecConfig())

      // Invalid header type
      const invalidBuffer = new ArrayBuffer(10)
      const view = new DataView(invalidBuffer)
      view.setUint8(0, 0x18) // Version 1, type 8 (unknown)

      expect(() => codec.decode(invalidBuffer)).toThrow()
    })

    it('should handle version mismatch with warning', () => {
      const codec = new MessageCodec(createCodecConfig())

      // Create buffer with version 2
      const message: HeartbeatMessage = {
        type: 'heartbeat',
        term: 1,
        leaderId: 'player1',
        frame: 100,
      }

      const validBuffer = codec.encode(message) as ArrayBuffer
      const view = new DataView(validBuffer)
      // Change version to 2
      const header = view.getUint8(0)
      view.setUint8(0, (header & 0x0F) | 0x20) // Version 2

      // Should still decode with warning
      const consoleSpy = vi.spyOn(console, 'warn').mockImplementation(() => {})
      const decoded = codec.decode(validBuffer) as HeartbeatMessage
      expect(decoded.type).toBe('heartbeat')
      consoleSpy.mockRestore()
    })
  })

  describe('bandwidth comparison', () => {
    it('should produce smaller binary than JSON for FrameInput', () => {
      const codec = new MessageCodec(createCodecConfig())

      const message: FrameInput = {
        frame: 1000,
        playerId: 'player1',
        input: { ...createEmptyInput(), up: true, fire: true },
      }

      const binary = codec.encode(message) as ArrayBuffer
      const json = JSON.stringify(message)

      // Binary should be significantly smaller
      expect(binary.byteLength).toBeLessThan(json.length)
      expect(binary.byteLength).toBeLessThan(json.length * 0.2) // At least 80% smaller
    })

    it('should produce smaller binary than JSON for Heartbeat', () => {
      const codec = new MessageCodec(createCodecConfig())

      const message: HeartbeatMessage = {
        type: 'heartbeat',
        term: 10,
        leaderId: 'player1',
        frame: 5000,
      }

      const binary = codec.encode(message) as ArrayBuffer
      const json = JSON.stringify(message)

      expect(binary.byteLength).toBeLessThan(json.length)
    })
  })
})
