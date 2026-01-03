import { describe, it, expect } from 'vitest'
import {
  PROTOCOL_VERSION,
  MessageType,
  encodeHeader,
  decodeHeader,
  isBinaryMessage,
  getMessageTypeName,
} from './BinaryProtocol'

describe('BinaryProtocol', () => {
  describe('PROTOCOL_VERSION', () => {
    it('should be version 1', () => {
      expect(PROTOCOL_VERSION).toBe(1)
    })

    it('should fit in 4 bits (0-15)', () => {
      expect(PROTOCOL_VERSION).toBeGreaterThanOrEqual(0)
      expect(PROTOCOL_VERSION).toBeLessThanOrEqual(15)
    })
  })

  describe('MessageType', () => {
    it('should have all expected message types', () => {
      expect(MessageType.FrameInput).toBe(0x0)
      expect(MessageType.FrameInputBatch).toBe(0x1)
      expect(MessageType.StateSync).toBe(0x2)
      expect(MessageType.StateSyncDelta).toBe(0x3)
      expect(MessageType.RequestVote).toBe(0x4)
      expect(MessageType.VoteResponse).toBe(0x5)
      expect(MessageType.Heartbeat).toBe(0x6)
      expect(MessageType.HeartbeatAck).toBe(0x7)
      expect(MessageType.JsonFallback).toBe(0xF)
    })

    it('should have types that fit in 4 bits (0-15)', () => {
      for (const type of Object.values(MessageType)) {
        if (typeof type === 'number') {
          expect(type).toBeGreaterThanOrEqual(0)
          expect(type).toBeLessThanOrEqual(15)
        }
      }
    })
  })

  describe('encodeHeader', () => {
    it('should encode version and type into single byte', () => {
      const header = encodeHeader(1, MessageType.FrameInput)
      expect(header).toBe(0x10) // version 1 in high nibble, type 0 in low
    })

    it('should encode all message types correctly', () => {
      expect(encodeHeader(1, MessageType.FrameInput)).toBe(0x10)
      expect(encodeHeader(1, MessageType.FrameInputBatch)).toBe(0x11)
      expect(encodeHeader(1, MessageType.StateSync)).toBe(0x12)
      expect(encodeHeader(1, MessageType.StateSyncDelta)).toBe(0x13)
      expect(encodeHeader(1, MessageType.RequestVote)).toBe(0x14)
      expect(encodeHeader(1, MessageType.VoteResponse)).toBe(0x15)
      expect(encodeHeader(1, MessageType.Heartbeat)).toBe(0x16)
      expect(encodeHeader(1, MessageType.HeartbeatAck)).toBe(0x17)
      expect(encodeHeader(1, MessageType.JsonFallback)).toBe(0x1F)
    })

    it('should handle version 0', () => {
      const header = encodeHeader(0, MessageType.Heartbeat)
      expect(header).toBe(0x06)
    })

    it('should handle max version (15)', () => {
      const header = encodeHeader(15, MessageType.JsonFallback)
      expect(header).toBe(0xFF)
    })
  })

  describe('decodeHeader', () => {
    it('should decode version and type from single byte', () => {
      const { version, type } = decodeHeader(0x10)
      expect(version).toBe(1)
      expect(type).toBe(MessageType.FrameInput)
    })

    it('should decode all encoded headers correctly', () => {
      // Round-trip test for all message types
      for (const [_name, type] of Object.entries(MessageType)) {
        if (typeof type === 'number') {
          const encoded = encodeHeader(PROTOCOL_VERSION, type)
          const decoded = decodeHeader(encoded)
          expect(decoded.version).toBe(PROTOCOL_VERSION)
          expect(decoded.type).toBe(type)
        }
      }
    })

    it('should decode version 0 correctly', () => {
      const { version, type } = decodeHeader(0x06)
      expect(version).toBe(0)
      expect(type).toBe(MessageType.Heartbeat)
    })

    it('should decode max values correctly', () => {
      const { version, type } = decodeHeader(0xFF)
      expect(version).toBe(15)
      expect(type).toBe(15) // JsonFallback
    })

    it('should be inverse of encodeHeader', () => {
      for (let version = 0; version <= 15; version++) {
        for (let type = 0; type <= 15; type++) {
          const encoded = encodeHeader(version, type)
          const decoded = decodeHeader(encoded)
          expect(decoded.version).toBe(version)
          expect(decoded.type).toBe(type)
        }
      }
    })
  })

  describe('isBinaryMessage', () => {
    it('should return true for ArrayBuffer', () => {
      const buffer = new ArrayBuffer(10)
      expect(isBinaryMessage(buffer)).toBe(true)
    })

    it('should return false for string', () => {
      expect(isBinaryMessage('{"type":"test"}')).toBe(false)
    })

    it('should return false for null', () => {
      expect(isBinaryMessage(null as unknown as ArrayBuffer | string)).toBe(false)
    })

    it('should return false for undefined', () => {
      expect(isBinaryMessage(undefined as unknown as ArrayBuffer | string)).toBe(false)
    })

    it('should return false for number', () => {
      expect(isBinaryMessage(42 as unknown as ArrayBuffer | string)).toBe(false)
    })

    it('should return false for object', () => {
      expect(isBinaryMessage({ type: 'test' } as unknown as ArrayBuffer | string)).toBe(false)
    })

    it('should return false for Uint8Array (not ArrayBuffer)', () => {
      const arr = new Uint8Array(10)
      expect(isBinaryMessage(arr as unknown as ArrayBuffer | string)).toBe(false)
    })
  })

  describe('getMessageTypeName', () => {
    it('should return correct names for all types', () => {
      expect(getMessageTypeName(MessageType.FrameInput)).toBe('FrameInput')
      expect(getMessageTypeName(MessageType.FrameInputBatch)).toBe('FrameInputBatch')
      expect(getMessageTypeName(MessageType.StateSync)).toBe('StateSync')
      expect(getMessageTypeName(MessageType.StateSyncDelta)).toBe('StateSyncDelta')
      expect(getMessageTypeName(MessageType.RequestVote)).toBe('RequestVote')
      expect(getMessageTypeName(MessageType.VoteResponse)).toBe('VoteResponse')
      expect(getMessageTypeName(MessageType.Heartbeat)).toBe('Heartbeat')
      expect(getMessageTypeName(MessageType.HeartbeatAck)).toBe('HeartbeatAck')
      expect(getMessageTypeName(MessageType.JsonFallback)).toBe('JsonFallback')
    })

    it('should return Unknown for invalid types', () => {
      expect(getMessageTypeName(99 as unknown as typeof MessageType[keyof typeof MessageType])).toBe('Unknown(99)')
      expect(getMessageTypeName(-1 as unknown as typeof MessageType[keyof typeof MessageType])).toBe('Unknown(-1)')
      expect(getMessageTypeName(8 as unknown as typeof MessageType[keyof typeof MessageType])).toBe('Unknown(8)') // Gap in enum
    })
  })
})
