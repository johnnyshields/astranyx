import { describe, it, expect } from 'vitest'
import {
  encodePlayerInput,
  decodePlayerInput,
  encodeFrameInput,
  decodeFrameInput,
  calculateFrameInputSize,
} from './InputEncoder'
import type { PlayerInput, FrameInput, GameEvent } from '../types'

// Input bit positions (must match InputEncoder implementation)
const INPUT_BIT_UP = 1 << 0
const INPUT_BIT_DOWN = 1 << 1
const INPUT_BIT_LEFT = 1 << 2
const INPUT_BIT_RIGHT = 1 << 3
const INPUT_BIT_FIRE = 1 << 4
const INPUT_BIT_SPECIAL = 1 << 5
const INPUT_BIT_SECONDARY = 1 << 6
const INPUT_BIT_SWAP = 1 << 7
const INPUT_BIT_PICKUP = 1 << 8
const INPUT_BIT_PAUSE = 1 << 9

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

function createPlayerOrder(): Map<string, number> {
  return new Map([
    ['player1', 0],
    ['player2', 1],
    ['player3', 2],
  ])
}

describe('InputEncoder', () => {
  describe('encodePlayerInput / decodePlayerInput', () => {
    it('should encode empty input as 0', () => {
      const input = createEmptyInput()
      expect(encodePlayerInput(input)).toBe(0)
    })

    it('should encode single inputs correctly', () => {
      expect(encodePlayerInput({ ...createEmptyInput(), up: true })).toBe(INPUT_BIT_UP)
      expect(encodePlayerInput({ ...createEmptyInput(), down: true })).toBe(INPUT_BIT_DOWN)
      expect(encodePlayerInput({ ...createEmptyInput(), left: true })).toBe(INPUT_BIT_LEFT)
      expect(encodePlayerInput({ ...createEmptyInput(), right: true })).toBe(INPUT_BIT_RIGHT)
      expect(encodePlayerInput({ ...createEmptyInput(), fire: true })).toBe(INPUT_BIT_FIRE)
      expect(encodePlayerInput({ ...createEmptyInput(), special: true })).toBe(INPUT_BIT_SPECIAL)
      expect(encodePlayerInput({ ...createEmptyInput(), secondary: true })).toBe(INPUT_BIT_SECONDARY)
      expect(encodePlayerInput({ ...createEmptyInput(), swap: true })).toBe(INPUT_BIT_SWAP)
      expect(encodePlayerInput({ ...createEmptyInput(), pickup: true })).toBe(INPUT_BIT_PICKUP)
      expect(encodePlayerInput({ ...createEmptyInput(), pause: true })).toBe(INPUT_BIT_PAUSE)
    })

    it('should encode multiple inputs correctly', () => {
      const input: PlayerInput = {
        ...createEmptyInput(),
        up: true,
        right: true,
        fire: true,
      }
      const encoded = encodePlayerInput(input)
      expect(encoded).toBe(INPUT_BIT_UP | INPUT_BIT_RIGHT | INPUT_BIT_FIRE)
    })

    it('should decode empty input', () => {
      const decoded = decodePlayerInput(0)
      expect(decoded).toEqual(createEmptyInput())
    })

    it('should decode single inputs correctly', () => {
      expect(decodePlayerInput(INPUT_BIT_UP).up).toBe(true)
      expect(decodePlayerInput(INPUT_BIT_DOWN).down).toBe(true)
      expect(decodePlayerInput(INPUT_BIT_LEFT).left).toBe(true)
      expect(decodePlayerInput(INPUT_BIT_RIGHT).right).toBe(true)
      expect(decodePlayerInput(INPUT_BIT_FIRE).fire).toBe(true)
      expect(decodePlayerInput(INPUT_BIT_SPECIAL).special).toBe(true)
      expect(decodePlayerInput(INPUT_BIT_SECONDARY).secondary).toBe(true)
      expect(decodePlayerInput(INPUT_BIT_SWAP).swap).toBe(true)
      expect(decodePlayerInput(INPUT_BIT_PICKUP).pickup).toBe(true)
      expect(decodePlayerInput(INPUT_BIT_PAUSE).pause).toBe(true)
    })

    it('should round-trip all input combinations', () => {
      // Test a selection of input combinations
      const testCases: PlayerInput[] = [
        createEmptyInput(),
        { ...createEmptyInput(), up: true },
        { ...createEmptyInput(), up: true, down: true },
        { ...createEmptyInput(), left: true, right: true, fire: true },
        {
          up: true,
          down: true,
          left: true,
          right: true,
          fire: true,
          special: true,
          secondary: true,
          swap: true,
          pickup: true,
          pause: true,
        },
      ]

      for (const input of testCases) {
        const encoded = encodePlayerInput(input)
        const decoded = decodePlayerInput(encoded)
        expect(decoded).toEqual(input)
      }
    })
  })

  describe('encodeFrameInput / decodeFrameInput', () => {
    const playerOrder = createPlayerOrder()
    const playerIdByIndex = ['player1', 'player2', 'player3']

    it('should encode minimal FrameInput', () => {
      const frameInput: FrameInput = {
        frame: 100,
        playerId: 'player1',
        input: createEmptyInput(),
      }

      const buffer = encodeFrameInput(frameInput, playerOrder)
      expect(buffer.byteLength).toBe(6) // Header + flags + input bits + frame
    })

    it('should decode minimal FrameInput', () => {
      const frameInput: FrameInput = {
        frame: 100,
        playerId: 'player1',
        input: createEmptyInput(),
      }

      const buffer = encodeFrameInput(frameInput, playerOrder)
      const decoded = decodeFrameInput(buffer, playerIdByIndex)

      expect(decoded.frame).toBe(100)
      expect(decoded.playerId).toBe('player1')
      expect(decoded.input).toEqual(createEmptyInput())
      expect(decoded.checksum).toBeUndefined()
      expect(decoded.events).toBeUndefined()
    })

    it('should encode and decode with checksum', () => {
      const frameInput: FrameInput = {
        frame: 200,
        playerId: 'player2',
        input: { ...createEmptyInput(), fire: true },
        checksum: 0xDEADBEEF,
      }

      const buffer = encodeFrameInput(frameInput, playerOrder)
      expect(buffer.byteLength).toBe(10) // 6 base + 4 checksum

      const decoded = decodeFrameInput(buffer, playerIdByIndex)
      expect(decoded.frame).toBe(200)
      expect(decoded.playerId).toBe('player2')
      expect(decoded.input.fire).toBe(true)
      expect(decoded.checksum).toBe(0xDEADBEEF)
    })

    it('should encode and decode with events', () => {
      const events: GameEvent[] = [
        { type: 'damage', playerId: 'player1', amount: 50, newShields: 75, newLives: 3 },
        { type: 'death', playerId: 'player1' },
      ]

      const frameInput: FrameInput = {
        frame: 300,
        playerId: 'player1',
        input: createEmptyInput(),
        events,
      }

      const buffer = encodeFrameInput(frameInput, playerOrder)
      const decoded = decodeFrameInput(buffer, playerIdByIndex)

      expect(decoded.frame).toBe(300)
      expect(decoded.events).toBeDefined()
      expect(decoded.events!.length).toBe(2)
      expect(decoded.events![0]!.type).toBe('damage')
      expect(decoded.events![1]!.type).toBe('death')
    })

    it('should encode and decode with checksum and events', () => {
      const events: GameEvent[] = [
        { type: 'pickup', playerId: 'player1', pickupId: 123 },
      ]

      const frameInput: FrameInput = {
        frame: 400,
        playerId: 'player3',
        input: { ...createEmptyInput(), up: true, left: true },
        checksum: 0x12345678,
        events,
      }

      const buffer = encodeFrameInput(frameInput, playerOrder)
      const decoded = decodeFrameInput(buffer, playerIdByIndex)

      expect(decoded.frame).toBe(400)
      expect(decoded.playerId).toBe('player3')
      expect(decoded.input.up).toBe(true)
      expect(decoded.input.left).toBe(true)
      expect(decoded.checksum).toBe(0x12345678)
      expect(decoded.events!.length).toBe(1)
      expect(decoded.events![0]!.type).toBe('pickup')
    })

    it('should handle frame number overflow (16-bit)', () => {
      const frameInput: FrameInput = {
        frame: 65535, // Max 16-bit value
        playerId: 'player1',
        input: createEmptyInput(),
      }

      const buffer = encodeFrameInput(frameInput, playerOrder)
      const decoded = decodeFrameInput(buffer, playerIdByIndex)
      expect(decoded.frame).toBe(65535)
    })

    it('should handle frame number wrapping', () => {
      const frameInput: FrameInput = {
        frame: 65536, // Wraps to 0
        playerId: 'player1',
        input: createEmptyInput(),
      }

      const buffer = encodeFrameInput(frameInput, playerOrder)
      const decoded = decodeFrameInput(buffer, playerIdByIndex)
      expect(decoded.frame).toBe(0) // Wrapped
    })

    it('should handle unknown player ID gracefully', () => {
      const frameInput: FrameInput = {
        frame: 100,
        playerId: 'unknown_player',
        input: createEmptyInput(),
      }

      const buffer = encodeFrameInput(frameInput, playerOrder)
      const decoded = decodeFrameInput(buffer, playerIdByIndex)
      // Unknown player defaults to index 0
      expect(decoded.playerId).toBe('player1')
    })

    it('should handle missing player in decode gracefully', () => {
      const frameInput: FrameInput = {
        frame: 100,
        playerId: 'player3',
        input: createEmptyInput(),
      }

      const buffer = encodeFrameInput(frameInput, playerOrder)
      // Decode with shorter player list
      const decoded = decodeFrameInput(buffer, ['player1'])
      expect(decoded.playerId).toBe('player_2') // Fallback format
    })
  })

  describe('calculateFrameInputSize', () => {
    it('should return 6 for minimal input', () => {
      const frameInput: FrameInput = {
        frame: 0,
        playerId: 'player1',
        input: createEmptyInput(),
      }
      expect(calculateFrameInputSize(frameInput)).toBe(6)
    })

    it('should add 4 bytes for checksum', () => {
      const frameInput: FrameInput = {
        frame: 0,
        playerId: 'player1',
        input: createEmptyInput(),
        checksum: 123,
      }
      expect(calculateFrameInputSize(frameInput)).toBe(10)
    })

    it('should add bytes for events', () => {
      const events: GameEvent[] = [
        { type: 'damage', playerId: 'player1', amount: 10, newShields: 90, newLives: 3 },
      ]
      const frameInput: FrameInput = {
        frame: 0,
        playerId: 'player1',
        input: createEmptyInput(),
        events,
      }
      const size = calculateFrameInputSize(frameInput)
      expect(size).toBeGreaterThan(6)
    })
  })
})
