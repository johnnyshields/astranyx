import { describe, it, expect } from 'vitest'
import {
  encodeStateSync,
  decodeStateSync,
  encodeStateSyncUncompressed,
} from './StateSyncEncoder'
import type { StateSyncMessage } from '../types'

describe('StateSyncEncoder', () => {
  describe('encodeStateSync / decodeStateSync', () => {
    it('should encode and decode basic state sync', () => {
      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 1000,
        checksum: 0xDEADBEEF,
        term: 5,
        state: { players: [], enemies: [], bullets: [] },
      }

      const buffer = encodeStateSync(message)
      expect(buffer.byteLength).toBeGreaterThan(17) // Header size

      const decoded = decodeStateSync(buffer)
      expect(decoded.type).toBe('state_sync')
      expect(decoded.frame).toBe(1000)
      expect(decoded.checksum).toBe(0xDEADBEEF)
      expect(decoded.term).toBe(5)
      expect(decoded.state).toEqual({ players: [], enemies: [], bullets: [] })
    })

    it('should handle complex state objects', () => {
      const state = {
        players: [
          { id: 'p1', x: 100.5, y: 200.75, health: 100 },
          { id: 'p2', x: 300, y: 400, health: 75 },
        ],
        enemies: [
          { id: 'e1', type: 'grunt', x: 500, y: 100 },
        ],
        bullets: [],
        frame: 1234,
        seed: 42,
      }

      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 5000,
        checksum: 0x12345678,
        term: 10,
        state,
      }

      const buffer = encodeStateSync(message)
      const decoded = decodeStateSync(buffer)

      expect(decoded.state).toEqual(state)
    })

    it('should handle large frame numbers', () => {
      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 0xFFFFFFFF, // Max 32-bit
        checksum: 0,
        term: 0,
        state: {},
      }

      const buffer = encodeStateSync(message)
      const decoded = decodeStateSync(buffer)

      expect(decoded.frame).toBe(0xFFFFFFFF)
    })

    it('should handle zero values', () => {
      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 0,
        checksum: 0,
        term: 0,
        state: {},
      }

      const buffer = encodeStateSync(message)
      const decoded = decodeStateSync(buffer)

      expect(decoded.frame).toBe(0)
      expect(decoded.checksum).toBe(0)
      expect(decoded.term).toBe(0)
    })

    it('should handle nested state objects', () => {
      const state = {
        level: {
          id: 1,
          name: 'Test Level',
          waves: [
            { id: 1, enemies: ['a', 'b'] },
            { id: 2, enemies: ['c'] },
          ],
        },
        stats: {
          score: 99999,
          multiplier: 2.5,
          chain: 10,
        },
      }

      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 100,
        checksum: 123,
        term: 1,
        state,
      }

      const buffer = encodeStateSync(message)
      const decoded = decodeStateSync(buffer)

      expect(decoded.state).toEqual(state)
    })

    it('should handle arrays in state', () => {
      const state = {
        items: [1, 2, 3, 4, 5],
        strings: ['a', 'b', 'c'],
        nested: [[1, 2], [3, 4]],
      }

      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 50,
        checksum: 456,
        term: 2,
        state,
      }

      const buffer = encodeStateSync(message)
      const decoded = decodeStateSync(buffer)

      expect(decoded.state).toEqual(state)
    })

    it('should handle special characters in strings', () => {
      const state = {
        name: 'Test "Player"',
        unicode: '日本語テスト',
        special: '\n\t\r\\',
      }

      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 1,
        checksum: 0,
        term: 0,
        state,
      }

      const buffer = encodeStateSync(message)
      const decoded = decodeStateSync(buffer)

      expect(decoded.state).toEqual(state)
    })

    it('should handle null and boolean values', () => {
      const state = {
        nullValue: null,
        trueValue: true,
        falseValue: false,
        nested: { nullable: null },
      }

      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 1,
        checksum: 0,
        term: 0,
        state,
      }

      const buffer = encodeStateSync(message)
      const decoded = decodeStateSync(buffer)

      expect(decoded.state).toEqual(state)
    })

    it('should handle floating point numbers', () => {
      const state = {
        pi: 3.14159265359,
        tiny: 0.000001,
        negative: -123.456,
      }

      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 1,
        checksum: 0,
        term: 0,
        state,
      }

      const buffer = encodeStateSync(message)
      const decoded = decodeStateSync(buffer)

      expect(decoded.state).toEqual(state)
    })
  })

  describe('encodeStateSyncUncompressed', () => {
    it('should encode without compression', () => {
      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 500,
        checksum: 0xABCD,
        term: 3,
        state: { test: 'data' },
      }

      const buffer = encodeStateSyncUncompressed(message)
      const decoded = decodeStateSync(buffer)

      expect(decoded.frame).toBe(500)
      expect(decoded.checksum).toBe(0xABCD)
      expect(decoded.term).toBe(3)
      expect(decoded.state).toEqual({ test: 'data' })
    })

    it('should produce valid buffer that can be decoded', () => {
      const state = {
        players: [{ id: 'p1', x: 100, y: 200 }],
      }

      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 1000,
        checksum: 12345,
        term: 7,
        state,
      }

      const buffer = encodeStateSyncUncompressed(message)
      expect(buffer).toBeInstanceOf(ArrayBuffer)

      const decoded = decodeStateSync(buffer)
      expect(decoded.state).toEqual(state)
    })
  })

  describe('compression behavior', () => {
    // Note: pako may or may not be available in test environment

    it('should work without pako (fallback to uncompressed)', () => {
      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 100,
        checksum: 0,
        term: 1,
        state: { data: 'test' },
      }

      // This should not throw even without pako
      const buffer = encodeStateSync(message)
      expect(buffer).toBeInstanceOf(ArrayBuffer)

      const decoded = decodeStateSync(buffer)
      expect(decoded.state).toEqual({ data: 'test' })
    })

    it('should handle repeated data well', () => {
      // Highly repetitive data compresses well
      const state = {
        data: 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA',
        more: 'BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB',
      }

      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 100,
        checksum: 0,
        term: 1,
        state,
      }

      const buffer = encodeStateSync(message)
      const decoded = decodeStateSync(buffer)

      expect(decoded.state).toEqual(state)
    })
  })

  describe('round-trip tests', () => {
    it('should round-trip multiple times', () => {
      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 9999,
        checksum: 0xFEDCBA98,
        term: 42,
        state: { round: 'trip', test: true },
      }

      // Encode -> decode -> encode -> decode
      const buffer1 = encodeStateSync(message)
      const decoded1 = decodeStateSync(buffer1)
      const buffer2 = encodeStateSync(decoded1)
      const decoded2 = decodeStateSync(buffer2)

      expect(decoded2).toEqual(decoded1)
      expect(decoded2.frame).toBe(message.frame)
      expect(decoded2.checksum).toBe(message.checksum)
      expect(decoded2.term).toBe(message.term)
      expect(decoded2.state).toEqual(message.state)
    })

    it('should produce deterministic output for same input', () => {
      const message: StateSyncMessage = {
        type: 'state_sync',
        frame: 100,
        checksum: 123,
        term: 1,
        state: { a: 1, b: 2, c: 3 },
      }

      const buffer1 = encodeStateSyncUncompressed(message)
      const buffer2 = encodeStateSyncUncompressed(message)

      const view1 = new Uint8Array(buffer1)
      const view2 = new Uint8Array(buffer2)

      expect(view1).toEqual(view2)
    })
  })
})
