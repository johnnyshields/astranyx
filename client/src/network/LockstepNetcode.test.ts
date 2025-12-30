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
    pause: false,
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

    it('should advance frames 0 to inputDelay-1 (pre-seeded with empty inputs)', () => {
      lockstep.start()
      // With pre-seeding, frames 0-2 have empty inputs for all players
      // So first tick should advance from frame 0 to frame 1
      const result = lockstep.tick(createInput())
      expect(result).toBe(true)
      expect(lockstep.getCurrentFrame()).toBe(1)
    })

    it('should return false when waiting for inputs after pre-seeded frames', () => {
      lockstep.start()
      // Advance through pre-seeded frames (0, 1, 2)
      for (let i = 0; i < 3; i++) {
        lockstep.tick(createInput())
      }
      // Now frame 3 needs actual inputs from both players
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

    it('should return true when waiting for peer inputs after pre-seeded frames', () => {
      lockstep.start()
      // Advance through pre-seeded frames (0, 1, 2)
      for (let i = 0; i < 3; i++) {
        lockstep.tick(createInput())
      }
      // Now frame 3 needs actual inputs from both players
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
    it('should advance through pre-seeded frames in single player', () => {
      const singleConfig = createConfig({
        playerCount: 1,
        playerOrder: new Map([['player1', 0]]),
      })
      const singleLockstep = new LockstepNetcode(singleConfig)
      singleLockstep.start()

      const inputHandler = vi.fn()
      singleLockstep.setInputHandler(inputHandler)

      // With pre-seeding, frames 0-2 have empty inputs for the single player
      // So first tick should advance
      const result = singleLockstep.tick(createInput({ fire: true }))
      expect(result).toBe(true)
      expect(inputHandler).toHaveBeenCalled()
    })

    it('should continue advancing after pre-seeded frames (inputs from earlier ticks)', () => {
      const singleConfig = createConfig({
        playerCount: 1,
        playerOrder: new Map([['player1', 0]]),
      })
      const singleLockstep = new LockstepNetcode(singleConfig)
      singleLockstep.start()

      const inputHandler = vi.fn()
      singleLockstep.setInputHandler(inputHandler)

      // Advance through pre-seeded frames (0, 1, 2)
      // Each tick also sends input for a future frame
      for (let i = 0; i < 3; i++) {
        singleLockstep.tick(createInput())
      }

      // Now at frame 3, but tick 1 sent input for frame 3, tick 2 for frame 4, etc.
      // So frame 3 already has an input from earlier tick
      inputHandler.mockClear()

      const result = singleLockstep.tick(createInput({ fire: true }))
      // Should still advance because we have input from earlier tick
      expect(result).toBe(true)
      expect(inputHandler).toHaveBeenCalled()
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

describe('GameEvent handling', () => {
  let lockstep: LockstepNetcode
  let channel: RTCDataChannel

  function createGameEvent(type: string, playerId: string): import('./LockstepNetcode').GameEvent {
    switch (type) {
      case 'damage':
        return { type: 'damage', playerId, amount: 25, newShields: 75, newLives: 3 }
      case 'death':
        return { type: 'death', playerId }
      case 'respawn':
        return { type: 'respawn', playerId }
      case 'pickup':
        return { type: 'pickup', playerId, pickupId: 123 }
      case 'weapon_pickup':
        return { type: 'weapon_pickup', playerId, dropId: 456 }
      default:
        throw new Error(`Unknown event type: ${type}`)
    }
  }

  beforeEach(() => {
    const config = createConfig()
    lockstep = new LockstepNetcode(config)
    lockstep.start()
    channel = createMockDataChannel()
    lockstep.addPeer('player2', channel)
  })

  describe('sending events', () => {
    it('should include events in broadcast message', () => {
      const events = [createGameEvent('damage', 'player1')]
      lockstep.tick(createInput(), events)

      expect(channel.send).toHaveBeenCalled()
      const sentData = JSON.parse((channel.send as ReturnType<typeof vi.fn>).mock.calls[0]![0])
      expect(sentData.events).toBeDefined()
      expect(sentData.events).toHaveLength(1)
      expect(sentData.events[0].type).toBe('damage')
      expect(sentData.events[0].playerId).toBe('player1')
    })

    it('should not include events field when no events', () => {
      lockstep.tick(createInput())

      expect(channel.send).toHaveBeenCalled()
      const sentData = JSON.parse((channel.send as ReturnType<typeof vi.fn>).mock.calls[0]![0])
      expect(sentData.events).toBeUndefined()
    })

    it('should not include events field when empty array', () => {
      lockstep.tick(createInput(), [])

      expect(channel.send).toHaveBeenCalled()
      const sentData = JSON.parse((channel.send as ReturnType<typeof vi.fn>).mock.calls[0]![0])
      expect(sentData.events).toBeUndefined()
    })

    it('should include multiple events in single message', () => {
      const events = [
        createGameEvent('damage', 'player1'),
        createGameEvent('pickup', 'player1'),
      ]
      lockstep.tick(createInput(), events)

      const sentData = JSON.parse((channel.send as ReturnType<typeof vi.fn>).mock.calls[0]![0])
      expect(sentData.events).toHaveLength(2)
      expect(sentData.events[0].type).toBe('damage')
      expect(sentData.events[1].type).toBe('pickup')
    })

    it('should include all event types correctly', () => {
      const eventTypes = ['damage', 'death', 'respawn', 'pickup', 'weapon_pickup']

      for (const type of eventTypes) {
        const newLockstep = new LockstepNetcode(createConfig())
        newLockstep.start()
        const newChannel = createMockDataChannel()
        newLockstep.addPeer('player2', newChannel)

        const events = [createGameEvent(type, 'player1')]
        newLockstep.tick(createInput(), events)

        const sentData = JSON.parse((newChannel.send as ReturnType<typeof vi.fn>).mock.calls[0]![0])
        expect(sentData.events[0].type).toBe(type)
      }
    })
  })

  describe('receiving events', () => {
    it('should pass received events to input handler', () => {
      const inputHandler = vi.fn()
      lockstep.setInputHandler(inputHandler)

      // Simulate receiving input with events from player2
      const remoteEvents = [createGameEvent('damage', 'player2')]
      channel.onmessage?.({
        data: JSON.stringify({
          frame: 0,
          playerId: 'player2',
          input: createInput(),
          events: remoteEvents,
        })
      } as MessageEvent)

      // Also send our own input for frame 0 (to complete the frame)
      channel.onmessage?.({
        data: JSON.stringify({
          frame: 0,
          playerId: 'player1',
          input: createInput(),
        })
      } as MessageEvent)

      // Trigger processing
      lockstep.tick(createInput())

      expect(inputHandler).toHaveBeenCalled()
      const [, events] = inputHandler.mock.calls[0]!
      expect(events).toHaveLength(1)
      expect(events[0].type).toBe('damage')
      expect(events[0].playerId).toBe('player2')
    })

    it('should collect events from multiple players', () => {
      const inputHandler = vi.fn()
      lockstep.setInputHandler(inputHandler)

      // Player 1 events
      channel.onmessage?.({
        data: JSON.stringify({
          frame: 0,
          playerId: 'player1',
          input: createInput(),
          events: [createGameEvent('pickup', 'player1')],
        })
      } as MessageEvent)

      // Player 2 events
      channel.onmessage?.({
        data: JSON.stringify({
          frame: 0,
          playerId: 'player2',
          input: createInput(),
          events: [createGameEvent('damage', 'player2')],
        })
      } as MessageEvent)

      // Trigger processing
      lockstep.tick(createInput())

      expect(inputHandler).toHaveBeenCalled()
      const [, events] = inputHandler.mock.calls[0]!
      expect(events).toHaveLength(2)

      // Events should be in player order (player1 first, then player2)
      expect(events[0].playerId).toBe('player1')
      expect(events[1].playerId).toBe('player2')
    })

    it('should handle inputs without events', () => {
      const inputHandler = vi.fn()
      lockstep.setInputHandler(inputHandler)

      // No events from either player
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

      lockstep.tick(createInput())

      expect(inputHandler).toHaveBeenCalled()
      const [, events] = inputHandler.mock.calls[0]!
      expect(events).toEqual([])
    })

    it('should preserve event order within a player', () => {
      const inputHandler = vi.fn()
      lockstep.setInputHandler(inputHandler)

      // Multiple events from same player
      channel.onmessage?.({
        data: JSON.stringify({
          frame: 0,
          playerId: 'player1',
          input: createInput(),
          events: [
            createGameEvent('damage', 'player1'),
            createGameEvent('death', 'player1'),
            createGameEvent('respawn', 'player1'),
          ],
        })
      } as MessageEvent)

      channel.onmessage?.({
        data: JSON.stringify({
          frame: 0,
          playerId: 'player2',
          input: createInput(),
        })
      } as MessageEvent)

      lockstep.tick(createInput())

      const [, events] = inputHandler.mock.calls[0]!
      expect(events).toHaveLength(3)
      expect(events[0].type).toBe('damage')
      expect(events[1].type).toBe('death')
      expect(events[2].type).toBe('respawn')
    })
  })

  describe('event data integrity', () => {
    it('should preserve damage event fields', () => {
      const inputHandler = vi.fn()
      lockstep.setInputHandler(inputHandler)

      const damageEvent = {
        type: 'damage' as const,
        playerId: 'player2',
        amount: 50,
        newShields: 25,
        newLives: 2,
      }

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
          events: [damageEvent],
        })
      } as MessageEvent)

      lockstep.tick(createInput())

      const [, events] = inputHandler.mock.calls[0]!
      const received = events[0]
      expect(received.type).toBe('damage')
      if (received.type === 'damage') {
        expect(received.amount).toBe(50)
        expect(received.newShields).toBe(25)
        expect(received.newLives).toBe(2)
      }
    })

    it('should preserve pickup event fields', () => {
      const inputHandler = vi.fn()
      lockstep.setInputHandler(inputHandler)

      const pickupEvent = {
        type: 'pickup' as const,
        playerId: 'player2',
        pickupId: 999,
      }

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
          events: [pickupEvent],
        })
      } as MessageEvent)

      lockstep.tick(createInput())

      const [, events] = inputHandler.mock.calls[0]!
      const received = events[0]
      expect(received.type).toBe('pickup')
      if (received.type === 'pickup') {
        expect(received.pickupId).toBe(999)
      }
    })

    it('should preserve weapon_pickup event fields', () => {
      const inputHandler = vi.fn()
      lockstep.setInputHandler(inputHandler)

      const weaponPickupEvent = {
        type: 'weapon_pickup' as const,
        playerId: 'player2',
        dropId: 777,
      }

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
          events: [weaponPickupEvent],
        })
      } as MessageEvent)

      lockstep.tick(createInput())

      const [, events] = inputHandler.mock.calls[0]!
      const received = events[0]
      expect(received.type).toBe('weapon_pickup')
      if (received.type === 'weapon_pickup') {
        expect(received.dropId).toBe(777)
      }
    })
  })

  describe('edge cases', () => {
    it('should handle events with checksum', () => {
      const events = [createGameEvent('damage', 'player1')]
      lockstep.tick(createInput(), events, 12345)

      const sentData = JSON.parse((channel.send as ReturnType<typeof vi.fn>).mock.calls[0]![0])
      expect(sentData.events).toHaveLength(1)
      expect(sentData.checksum).toBe(12345)
    })

    it('should handle undefined events parameter', () => {
      lockstep.tick(createInput(), undefined, 12345)

      const sentData = JSON.parse((channel.send as ReturnType<typeof vi.fn>).mock.calls[0]![0])
      expect(sentData.events).toBeUndefined()
    })

    it('should not include events for already processed frames', () => {
      const inputHandler = vi.fn()
      lockstep.setInputHandler(inputHandler)

      // Setup frame 0 inputs
      channel.onmessage?.({
        data: JSON.stringify({
          frame: 0,
          playerId: 'player1',
          input: createInput(),
          events: [createGameEvent('pickup', 'player1')],
        })
      } as MessageEvent)

      channel.onmessage?.({
        data: JSON.stringify({
          frame: 0,
          playerId: 'player2',
          input: createInput(),
        })
      } as MessageEvent)

      // Process frame 0
      lockstep.tick(createInput())
      expect(lockstep.getConfirmedFrame()).toBe(0)

      // Try to send old event for frame 0 again
      inputHandler.mockClear()
      channel.onmessage?.({
        data: JSON.stringify({
          frame: 0,
          playerId: 'player2',
          input: createInput(),
          events: [createGameEvent('damage', 'player2')],
        })
      } as MessageEvent)

      // Old events should be ignored
      expect(inputHandler).not.toHaveBeenCalled()
    })
  })
})
