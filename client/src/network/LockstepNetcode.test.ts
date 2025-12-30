import { describe, it, expect, beforeEach, vi } from 'vitest'
import {
  LockstepNetcode,
  type LockstepConfig,
  type PlayerInput,
  emptyInput,
  inputsEqual,
} from './LockstepNetcode'

function createMockDataChannel(): RTCDataChannel {
  return {
    readyState: 'open',
    send: vi.fn(),
    onmessage: null,
  } as unknown as RTCDataChannel
}

function createConfig(overrides?: Partial<LockstepConfig>): LockstepConfig {
  return {
    inputDelay: 3,
    maxRollbackFrames: 0,
    playerCount: 2,
    localPlayerId: 'player1',
    playerOrder: new Map([['player1', 0], ['player2', 1]]),
    ...overrides,
  }
}

function createInput(overrides?: Partial<PlayerInput>): PlayerInput {
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
    ...overrides,
  }
}

describe('LockstepNetcode', () => {
  let lockstep: LockstepNetcode
  let config: LockstepConfig

  beforeEach(() => {
    config = createConfig()
    lockstep = new LockstepNetcode(config)
  })

  describe('constructor', () => {
    it('should create with default config', () => {
      expect(lockstep.getCurrentFrame()).toBe(0)
      expect(lockstep.getConfirmedFrame()).toBe(-1)
      expect(lockstep.getInputDelay()).toBe(3)
    })

    it('should use custom input delay', () => {
      const customLockstep = new LockstepNetcode(createConfig({ inputDelay: 5 }))
      expect(customLockstep.getInputDelay()).toBe(5)
    })

    it('should default input delay to 3', () => {
      const partialConfig = createConfig()
      delete (partialConfig as unknown as Record<string, unknown>).inputDelay
      const customLockstep = new LockstepNetcode(partialConfig)
      expect(customLockstep.getInputDelay()).toBe(3)
    })
  })

  describe('start', () => {
    it('should reset state', () => {
      lockstep.start()
      expect(lockstep.getCurrentFrame()).toBe(0)
      expect(lockstep.getConfirmedFrame()).toBe(-1)
    })

    it('should allow starting multiple times', () => {
      lockstep.start()
      lockstep.start()
      expect(lockstep.getCurrentFrame()).toBe(0)
    })
  })

  describe('stop', () => {
    it('should stop processing', () => {
      lockstep.start()
      lockstep.stop()
      const result = lockstep.tick(createInput())
      expect(result).toBe(false)
    })
  })

  describe('tick', () => {
    it('should return false when not running', () => {
      const result = lockstep.tick(createInput())
      expect(result).toBe(false)
    })

    it('should return false when waiting for inputs', () => {
      lockstep.start()
      // With 2 players, need inputs from both to advance
      const result = lockstep.tick(createInput())
      expect(result).toBe(false)
    })
  })

  describe('addPeer', () => {
    it('should add peer and set up message handler', () => {
      lockstep.start()
      const channel = createMockDataChannel()
      lockstep.addPeer('player2', channel)
      expect(channel.onmessage).toBeDefined()
    })
  })

  describe('removePeer', () => {
    it('should remove peer', () => {
      lockstep.start()
      const channel = createMockDataChannel()
      lockstep.addPeer('player2', channel)
      lockstep.removePeer('player2')
      // No error thrown
    })

    it('should handle removing non-existent peer', () => {
      lockstep.removePeer('nonexistent')
      // No error thrown
    })
  })

  describe('input flow', () => {
    let channel: RTCDataChannel

    beforeEach(() => {
      lockstep.start()
      channel = createMockDataChannel()
      lockstep.addPeer('player2', channel)
    })

    it('should broadcast local input to peers', () => {
      lockstep.tick(createInput({ up: true }))
      expect(channel.send).toHaveBeenCalled()
      const sentData = JSON.parse((channel.send as ReturnType<typeof vi.fn>).mock.calls[0]![0])
      expect(sentData.playerId).toBe('player1')
      expect(sentData.input.up).toBe(true)
    })

    it('should store input for future frame with delay', () => {
      lockstep.tick(createInput({ up: true }))
      const sentData = JSON.parse((channel.send as ReturnType<typeof vi.fn>).mock.calls[0]![0])
      // Frame should be currentFrame + inputDelay
      expect(sentData.frame).toBe(0 + 3) // 0 + inputDelay(3)
    })

    it('should advance frame when all inputs received', () => {
      const inputHandler = vi.fn()
      lockstep.setInputHandler(inputHandler)

      // With input delay of 3, local tick sends input for frame 3
      // For frame 0 to process, both players need inputs for frame 0

      // Receive remote input for frame 0
      channel.onmessage?.({
        data: JSON.stringify({
          frame: 0,
          playerId: 'player2',
          input: createInput({ down: true }),
        })
      } as MessageEvent)

      // Receive local input for frame 0 (simulating what would happen before the delay system)
      channel.onmessage?.({
        data: JSON.stringify({
          frame: 0,
          playerId: 'player1',
          input: createInput({ up: true }),
        })
      } as MessageEvent)

      // Trigger a tick to try advancing
      lockstep.tick(createInput())

      // Now frame 0 should be processed
      expect(inputHandler).toHaveBeenCalled()
      expect(lockstep.getConfirmedFrame()).toBe(0)
      expect(lockstep.getCurrentFrame()).toBe(1)
    })

    it('should ignore inputs for already processed frames', () => {
      const inputHandler = vi.fn()
      lockstep.setInputHandler(inputHandler)

      // Setup frame 0 inputs
      channel.onmessage?.({
        data: JSON.stringify({
          frame: 0,
          playerId: 'player1',
          input: createInput(),
        })
      } as MessageEvent)

      channel.onmessage?.({
        data: JSON.stringify({
          frame: 0,
          playerId: 'player2',
          input: createInput(),
        })
      } as MessageEvent)

      // Trigger processing
      lockstep.tick(createInput())

      expect(lockstep.getConfirmedFrame()).toBe(0)

      // Try to receive old input again for already processed frame
      inputHandler.mockClear()
      channel.onmessage?.({
        data: JSON.stringify({
          frame: 0,
          playerId: 'player2',
          input: createInput({ up: true }),
        })
      } as MessageEvent)

      // Input handler should not be called again for frame 0
      expect(inputHandler).not.toHaveBeenCalled()
      expect(lockstep.getConfirmedFrame()).toBe(0)
    })
  })

  describe('isWaitingForInputs', () => {
    it('should return false initially', () => {
      expect(lockstep.isWaitingForInputs()).toBe(false)
    })

    it('should return true when waiting for peer inputs', () => {
      lockstep.start()
      lockstep.tick(createInput())
      expect(lockstep.isWaitingForInputs()).toBe(true)
    })
  })

  describe('getLocalPlayerIndex', () => {
    it('should return player index', () => {
      expect(lockstep.getLocalPlayerIndex()).toBe(0)
    })

    it('should return 0 for unknown player', () => {
      const unknownConfig = createConfig({ localPlayerId: 'unknown' })
      const unknownLockstep = new LockstepNetcode(unknownConfig)
      expect(unknownLockstep.getLocalPlayerIndex()).toBe(0)
    })
  })

  describe('setDesyncHandler', () => {
    it('should set desync handler', () => {
      const handler = vi.fn()
      lockstep.setDesyncHandler(handler)
      // Handler is stored (no direct way to verify without triggering desync)
    })
  })

  describe('single player mode', () => {
    it('should work with single player', () => {
      const singleConfig = createConfig({
        playerCount: 1,
        playerOrder: new Map([['player1', 0]]),
      })
      const singleLockstep = new LockstepNetcode(singleConfig)
      singleLockstep.start()

      const inputHandler = vi.fn()
      singleLockstep.setInputHandler(inputHandler)

      // Should advance immediately with just local input
      const result = singleLockstep.tick(createInput({ fire: true }))

      // In single player, we have our input for frame 0 + inputDelay
      // But we're trying to process frame 0
      // We need to check if we have inputs for frame 0

      // Actually, for frame 0 to process, we need input for frame 0
      // Local tick sends input for frame (0 + 3) = 3
      // So frame 0 has no inputs yet
      expect(result).toBe(false)
    })
  })
})

describe('emptyInput', () => {
  it('should return all false values', () => {
    const input = emptyInput()
    expect(input.up).toBe(false)
    expect(input.down).toBe(false)
    expect(input.left).toBe(false)
    expect(input.right).toBe(false)
    expect(input.fire).toBe(false)
    expect(input.special).toBe(false)
    expect(input.secondary).toBe(false)
    expect(input.swap).toBe(false)
    expect(input.pickup).toBe(false)
  })

  it('should return new object each time', () => {
    const input1 = emptyInput()
    const input2 = emptyInput()
    expect(input1).not.toBe(input2)
    input1.up = true
    expect(input2.up).toBe(false)
  })
})

describe('inputsEqual', () => {
  it('should return true for identical inputs', () => {
    const input1 = createInput({ up: true, fire: true })
    const input2 = createInput({ up: true, fire: true })
    expect(inputsEqual(input1, input2)).toBe(true)
  })

  it('should return false for different up', () => {
    const input1 = createInput({ up: true })
    const input2 = createInput({ up: false })
    expect(inputsEqual(input1, input2)).toBe(false)
  })

  it('should return false for different down', () => {
    const input1 = createInput({ down: true })
    const input2 = createInput({ down: false })
    expect(inputsEqual(input1, input2)).toBe(false)
  })

  it('should return false for different left', () => {
    const input1 = createInput({ left: true })
    const input2 = createInput({ left: false })
    expect(inputsEqual(input1, input2)).toBe(false)
  })

  it('should return false for different right', () => {
    const input1 = createInput({ right: true })
    const input2 = createInput({ right: false })
    expect(inputsEqual(input1, input2)).toBe(false)
  })

  it('should return false for different fire', () => {
    const input1 = createInput({ fire: true })
    const input2 = createInput({ fire: false })
    expect(inputsEqual(input1, input2)).toBe(false)
  })

  it('should return false for different special', () => {
    const input1 = createInput({ special: true })
    const input2 = createInput({ special: false })
    expect(inputsEqual(input1, input2)).toBe(false)
  })

  it('should return true for two empty inputs', () => {
    expect(inputsEqual(emptyInput(), emptyInput())).toBe(true)
  })

  it('should ignore secondary/swap/pickup fields', () => {
    // Note: inputsEqual only checks core movement/action inputs
    const input1 = createInput({ secondary: true })
    const input2 = createInput({ secondary: false })
    expect(inputsEqual(input1, input2)).toBe(true)
  })
})
