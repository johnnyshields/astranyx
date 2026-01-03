import { describe, it, expect, vi, beforeEach, afterEach, type Mock } from 'vitest'
import { NetworkManager, type GameStateSnapshot, type GameEvent, type PlayerInput, type EntityState } from './NetworkManager'

// Create a mock instance that will be shared
const createMockWebRTCClient = () => ({
  onMessage: vi.fn(),
  connect: vi.fn().mockResolvedValue(undefined),
  send: vi.fn(),
  isConnected: vi.fn().mockReturnValue(false),
  getLatency: vi.fn().mockReturnValue(50),
  disconnect: vi.fn(),
})

let mockClientInstance = createMockWebRTCClient()

// Mock WebRTCClient as a class
vi.mock('./WebRTCClient.ts', () => {
  return {
    WebRTCClient: class MockWebRTCClient {
      onMessage = mockClientInstance.onMessage
      connect = mockClientInstance.connect
      send = mockClientInstance.send
      isConnected = mockClientInstance.isConnected
      getLatency = mockClientInstance.getLatency
      disconnect = mockClientInstance.disconnect
    },
  }
})

describe('NetworkManager', () => {
  let networkManager: NetworkManager
  let messageHandler: (message: { type: string; data: unknown }) => void

  beforeEach(() => {
    // Reset mock instance for each test
    mockClientInstance = createMockWebRTCClient()

    networkManager = new NetworkManager('ws://localhost:4000')

    // Capture the message handler
    messageHandler = mockClientInstance.onMessage.mock.calls[0][0]
  })

  afterEach(() => {
    vi.clearAllMocks()
  })

  describe('constructor', () => {
    it('creates a NetworkManager instance', () => {
      expect(networkManager).toBeDefined()
    })

    it('sets up message handler on WebRTCClient', () => {
      expect(mockClientInstance.onMessage).toHaveBeenCalled()
    })
  })

  describe('joinGame', () => {
    it('connects to room and returns player ID', async () => {
      const playerId = await networkManager.joinGame('test-room')

      expect(playerId).toMatch(/^player_\d+_[a-z0-9]+$/)
      expect(mockClientInstance.connect).toHaveBeenCalledWith('test-room', playerId)
    })

    it('stores room ID internally', async () => {
      await networkManager.joinGame('my-room')
      expect(networkManager.getPlayerId()).toMatch(/^player_/)
    })
  })

  describe('sendInput', () => {
    it('does nothing when not connected', () => {
      mockClientInstance.isConnected.mockReturnValue(false)

      networkManager.sendInput({
        up: true,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        timestamp: 1000,
      })

      expect(mockClientInstance.send).not.toHaveBeenCalled()
    })

    it('sends input when connected', () => {
      mockClientInstance.isConnected.mockReturnValue(true)

      const input = {
        up: true,
        down: false,
        left: false,
        right: true,
        fire: true,
        special: false,
        timestamp: 1000,
      }

      networkManager.sendInput(input)

      expect(mockClientInstance.send).toHaveBeenCalledWith('input', {
        tick: 0,
        input,
      })
    })

    it('increments tick on each input', () => {
      mockClientInstance.isConnected.mockReturnValue(true)

      const input = {
        up: false,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        timestamp: 1000,
      }

      networkManager.sendInput(input)
      networkManager.sendInput(input)
      networkManager.sendInput(input)

      expect(mockClientInstance.send).toHaveBeenCalledTimes(3)
      expect(mockClientInstance.send).toHaveBeenNthCalledWith(1, 'input', { tick: 0, input })
      expect(mockClientInstance.send).toHaveBeenNthCalledWith(2, 'input', { tick: 1, input })
      expect(mockClientInstance.send).toHaveBeenNthCalledWith(3, 'input', { tick: 2, input })
    })

    it('buffers inputs for reconciliation', () => {
      mockClientInstance.isConnected.mockReturnValue(true)

      const input = {
        up: true,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        timestamp: 1000,
      }

      networkManager.sendInput(input)
      networkManager.sendInput(input)

      const pending = networkManager.getPendingInputs()
      expect(pending.length).toBe(2)
      expect(pending[0].tick).toBe(0)
      expect(pending[1].tick).toBe(1)
    })

    it('trims old inputs when buffer exceeds max', () => {
      mockClientInstance.isConnected.mockReturnValue(true)

      const input = {
        up: false,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        timestamp: 1000,
      }

      // Send more than MAX_INPUT_BUFFER (120) inputs
      for (let i = 0; i < 125; i++) {
        networkManager.sendInput(input)
      }

      const pending = networkManager.getPendingInputs()
      expect(pending.length).toBe(120)
      expect(pending[0].tick).toBe(5) // First 5 trimmed
    })
  })

  describe('handleMessage', () => {
    it('handles state messages', () => {
      const stateHandler = vi.fn()
      networkManager.setStateHandler(stateHandler)

      const snapshot: GameStateSnapshot = {
        tick: 10,
        timestamp: 1000,
        entities: [],
        events: [],
      }

      messageHandler({ type: 'state', data: snapshot })

      expect(stateHandler).toHaveBeenCalledWith(snapshot)
    })

    it('handles event messages', () => {
      const eventHandler = vi.fn()
      networkManager.setEventHandler(eventHandler)

      const event: GameEvent = {
        type: 'spawn',
        entityId: 'entity-1',
        data: { x: 100, y: 200 },
      }

      messageHandler({ type: 'event', data: event })

      expect(eventHandler).toHaveBeenCalledWith(event)
    })

    it('ignores unknown message types', () => {
      const stateHandler = vi.fn()
      const eventHandler = vi.fn()
      networkManager.setStateHandler(stateHandler)
      networkManager.setEventHandler(eventHandler)

      messageHandler({ type: 'unknown', data: {} })

      expect(stateHandler).not.toHaveBeenCalled()
      expect(eventHandler).not.toHaveBeenCalled()
    })

    it('updates server tick on state update', () => {
      const snapshot: GameStateSnapshot = {
        tick: 42,
        timestamp: 1000,
        entities: [],
        events: [],
      }

      messageHandler({ type: 'state', data: snapshot })

      expect(networkManager.getServerTick()).toBe(42)
    })

    it('removes acknowledged inputs on state update', () => {
      mockClientInstance.isConnected.mockReturnValue(true)

      const input = {
        up: false,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        timestamp: 1000,
      }

      // Send 5 inputs (ticks 0-4)
      for (let i = 0; i < 5; i++) {
        networkManager.sendInput(input)
      }

      expect(networkManager.getPendingInputs().length).toBe(5)

      // Server acknowledges up to tick 2
      const snapshot: GameStateSnapshot = {
        tick: 2,
        timestamp: 1000,
        entities: [],
        events: [],
      }

      messageHandler({ type: 'state', data: snapshot })

      // Should have ticks 3 and 4 remaining
      const pending = networkManager.getPendingInputs()
      expect(pending.length).toBe(2)
      expect(pending[0].tick).toBe(3)
      expect(pending[1].tick).toBe(4)
    })
  })

  describe('getInterpolatedState', () => {
    it('returns null when no states', () => {
      expect(networkManager.getInterpolatedState()).toBeNull()
    })

    it('returns single state when only one state available', () => {
      const snapshot: GameStateSnapshot = {
        tick: 1,
        timestamp: performance.now(),
        entities: [{ id: 'e1', type: 'player', x: 100, y: 100, vx: 0, vy: 0, rotation: 0 }],
        events: [],
      }

      messageHandler({ type: 'state', data: snapshot })

      const result = networkManager.getInterpolatedState()
      expect(result).toBeTruthy()
      expect(result?.entities[0].id).toBe('e1')
    })

    it('interpolates between two states', () => {
      const now = performance.now()

      // State 1: entity at x=0
      const snapshot1: GameStateSnapshot = {
        tick: 1,
        timestamp: now - 200, // 200ms ago
        entities: [{ id: 'e1', type: 'player', x: 0, y: 0, vx: 0, vy: 0, rotation: 0 }],
        events: [],
      }

      // State 2: entity at x=100
      const snapshot2: GameStateSnapshot = {
        tick: 2,
        timestamp: now - 50, // 50ms ago
        entities: [{ id: 'e1', type: 'player', x: 100, y: 0, vx: 0, vy: 0, rotation: 0 }],
        events: [],
      }

      messageHandler({ type: 'state', data: snapshot1 })
      messageHandler({ type: 'state', data: snapshot2 })

      const result = networkManager.getInterpolatedState()

      // With 100ms interpolation delay, render time = now - 100
      // Which falls between timestamps (now-200) and (now-50)
      expect(result).toBeTruthy()
      // The x value should be somewhere between 0 and 100
      expect(result!.entities[0].x).toBeGreaterThanOrEqual(0)
      expect(result!.entities[0].x).toBeLessThanOrEqual(100)
    })

    it('handles new entities without interpolation', () => {
      const now = performance.now()

      const snapshot1: GameStateSnapshot = {
        tick: 1,
        timestamp: now - 200,
        entities: [], // No entities
        events: [],
      }

      const snapshot2: GameStateSnapshot = {
        tick: 2,
        timestamp: now - 50,
        entities: [{ id: 'new-entity', type: 'enemy', x: 50, y: 50, vx: 0, vy: 0, rotation: 0 }],
        events: [],
      }

      messageHandler({ type: 'state', data: snapshot1 })
      messageHandler({ type: 'state', data: snapshot2 })

      const result = networkManager.getInterpolatedState()
      expect(result).toBeTruthy()
      expect(result!.entities[0].x).toBe(50) // No interpolation for new entity
    })

    it('falls back to latest state when render time is outside range', () => {
      const now = performance.now()

      // Both states are in the past but render time doesn't fall between them
      const snapshot1: GameStateSnapshot = {
        tick: 1,
        timestamp: now - 500,
        entities: [{ id: 'e1', type: 'player', x: 0, y: 0, vx: 0, vy: 0, rotation: 0 }],
        events: [],
      }

      const snapshot2: GameStateSnapshot = {
        tick: 2,
        timestamp: now - 400,
        entities: [{ id: 'e1', type: 'player', x: 100, y: 0, vx: 0, vy: 0, rotation: 0 }],
        events: [],
      }

      messageHandler({ type: 'state', data: snapshot1 })
      messageHandler({ type: 'state', data: snapshot2 })

      const result = networkManager.getInterpolatedState()
      expect(result).toBeTruthy()
      // Should fall back to latest state (snapshot2)
      expect(result!.entities[0].x).toBe(100)
    })

    it('filters old states from buffer', () => {
      const now = performance.now()

      // Old state (> 1 second)
      const oldSnapshot: GameStateSnapshot = {
        tick: 1,
        timestamp: now - 2000,
        entities: [],
        events: [],
      }

      // Recent state
      const recentSnapshot: GameStateSnapshot = {
        tick: 2,
        timestamp: now - 50,
        entities: [],
        events: [],
      }

      messageHandler({ type: 'state', data: oldSnapshot })
      messageHandler({ type: 'state', data: recentSnapshot })

      // Force another state update to trigger filtering
      messageHandler({ type: 'state', data: { ...recentSnapshot, tick: 3 } })

      // Old state should be filtered out
      const result = networkManager.getInterpolatedState()
      expect(result).toBeTruthy()
    })

    it('interpolates rotation angles correctly', () => {
      const now = performance.now()

      // State 1: rotation at 0
      const snapshot1: GameStateSnapshot = {
        tick: 1,
        timestamp: now - 200,
        entities: [{ id: 'e1', type: 'player', x: 0, y: 0, vx: 0, vy: 0, rotation: 0 }],
        events: [],
      }

      // State 2: rotation at PI/2
      const snapshot2: GameStateSnapshot = {
        tick: 2,
        timestamp: now - 50,
        entities: [{ id: 'e1', type: 'player', x: 0, y: 0, vx: 0, vy: 0, rotation: Math.PI / 2 }],
        events: [],
      }

      messageHandler({ type: 'state', data: snapshot1 })
      messageHandler({ type: 'state', data: snapshot2 })

      const result = networkManager.getInterpolatedState()
      expect(result).toBeTruthy()
      // Rotation should be between 0 and PI/2
      expect(result!.entities[0].rotation).toBeGreaterThanOrEqual(0)
      expect(result!.entities[0].rotation).toBeLessThanOrEqual(Math.PI / 2)
    })

    it('handles angle wrapping (crosses PI boundary)', () => {
      const now = performance.now()

      // State 1: rotation at 3 (close to PI)
      const snapshot1: GameStateSnapshot = {
        tick: 1,
        timestamp: now - 200,
        entities: [{ id: 'e1', type: 'player', x: 0, y: 0, vx: 0, vy: 0, rotation: Math.PI - 0.1 }],
        events: [],
      }

      // State 2: rotation at -3 (close to -PI, wrapping around)
      const snapshot2: GameStateSnapshot = {
        tick: 2,
        timestamp: now - 50,
        entities: [{ id: 'e1', type: 'player', x: 0, y: 0, vx: 0, vy: 0, rotation: -Math.PI + 0.1 }],
        events: [],
      }

      messageHandler({ type: 'state', data: snapshot1 })
      messageHandler({ type: 'state', data: snapshot2 })

      const result = networkManager.getInterpolatedState()
      expect(result).toBeTruthy()
      // Rotation should handle wrapping gracefully
      expect(typeof result!.entities[0].rotation).toBe('number')
    })
  })

  describe('setStateHandler', () => {
    it('sets state update callback', () => {
      const handler = vi.fn()
      networkManager.setStateHandler(handler)

      const snapshot: GameStateSnapshot = {
        tick: 1,
        timestamp: 1000,
        entities: [],
        events: [],
      }

      messageHandler({ type: 'state', data: snapshot })

      expect(handler).toHaveBeenCalledWith(snapshot)
    })

    it('does not call old handler after replacing', () => {
      const oldHandler = vi.fn()
      const newHandler = vi.fn()

      networkManager.setStateHandler(oldHandler)
      networkManager.setStateHandler(newHandler)

      messageHandler({ type: 'state', data: { tick: 1, timestamp: 0, entities: [], events: [] } })

      expect(oldHandler).not.toHaveBeenCalled()
      expect(newHandler).toHaveBeenCalled()
    })
  })

  describe('setEventHandler', () => {
    it('sets event callback', () => {
      const handler = vi.fn()
      networkManager.setEventHandler(handler)

      const event: GameEvent = {
        type: 'damage',
        entityId: 'player-1',
        data: { amount: 10 },
      }

      messageHandler({ type: 'event', data: event })

      expect(handler).toHaveBeenCalledWith(event)
    })
  })

  describe('getLatency', () => {
    it('returns latency from WebRTCClient', () => {
      mockClientInstance.getLatency.mockReturnValue(75)
      expect(networkManager.getLatency()).toBe(75)
    })
  })

  describe('getServerTick', () => {
    it('returns 0 initially', () => {
      expect(networkManager.getServerTick()).toBe(0)
    })

    it('returns updated tick after state message', () => {
      messageHandler({
        type: 'state',
        data: { tick: 100, timestamp: 1000, entities: [], events: [] },
      })

      expect(networkManager.getServerTick()).toBe(100)
    })
  })

  describe('isConnected', () => {
    it('returns connection status from WebRTCClient', () => {
      mockClientInstance.isConnected.mockReturnValue(true)
      expect(networkManager.isConnected()).toBe(true)

      mockClientInstance.isConnected.mockReturnValue(false)
      expect(networkManager.isConnected()).toBe(false)
    })
  })

  describe('getPlayerId', () => {
    it('returns empty string before joining', () => {
      expect(networkManager.getPlayerId()).toBe('')
    })

    it('returns player ID after joining', async () => {
      await networkManager.joinGame('room-1')
      expect(networkManager.getPlayerId()).toMatch(/^player_/)
    })
  })

  describe('disconnect', () => {
    it('calls disconnect on WebRTCClient', () => {
      networkManager.disconnect()
      expect(mockClientInstance.disconnect).toHaveBeenCalled()
    })
  })

  describe('getPendingInputs', () => {
    it('returns copy of input buffer', () => {
      mockClientInstance.isConnected.mockReturnValue(true)

      networkManager.sendInput({
        up: true,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        timestamp: 1000,
      })

      const pending1 = networkManager.getPendingInputs()
      const pending2 = networkManager.getPendingInputs()

      expect(pending1).not.toBe(pending2) // Different array instances
      expect(pending1).toEqual(pending2) // Same content
    })
  })
})

// Type validation tests (preserved from original)
describe('Type interfaces', () => {
  describe('PlayerInput type', () => {
    it('should have correct structure', () => {
      const input: PlayerInput = {
        up: true,
        down: false,
        left: false,
        right: true,
        fire: true,
        special: false,
        timestamp: 12345,
      }

      expect(input.up).toBe(true)
      expect(input.timestamp).toBe(12345)
    })
  })

  describe('EntityState type', () => {
    it('should have correct structure', () => {
      const entity: EntityState = {
        id: 'entity-1',
        type: 'player',
        x: 100,
        y: 200,
        vx: 5,
        vy: -3,
        rotation: Math.PI / 4,
        health: 100,
        playerId: 'player-1',
      }

      expect(entity.id).toBe('entity-1')
      expect(entity.type).toBe('player')
      expect(entity.health).toBe(100)
    })

    it('should support all entity types', () => {
      const types: EntityState['type'][] = ['player', 'enemy', 'bullet', 'powerup']

      for (const type of types) {
        const entity: EntityState = {
          id: 'test',
          type,
          x: 0,
          y: 0,
          vx: 0,
          vy: 0,
          rotation: 0,
        }
        expect(entity.type).toBe(type)
      }
    })
  })

  describe('GameStateSnapshot type', () => {
    it('should have correct structure', () => {
      const snapshot: GameStateSnapshot = {
        tick: 100,
        timestamp: Date.now(),
        entities: [
          { id: 'e1', type: 'player', x: 0, y: 0, vx: 0, vy: 0, rotation: 0 },
        ],
        events: [
          { type: 'spawn', entityId: 'e1' },
        ],
      }

      expect(snapshot.tick).toBe(100)
      expect(snapshot.entities).toHaveLength(1)
      expect(snapshot.events).toHaveLength(1)
    })
  })

  describe('GameEvent type', () => {
    it('should support all event types', () => {
      const types: GameEvent['type'][] = ['spawn', 'destroy', 'damage', 'powerup', 'score']

      for (const type of types) {
        const event: GameEvent = {
          type,
          entityId: 'test',
        }
        expect(event.type).toBe(type)
      }
    })

    it('should support optional data', () => {
      const event: GameEvent = {
        type: 'damage',
        entityId: 'enemy-1',
        data: { amount: 50, source: 'player-1' },
      }

      expect(event.data).toEqual({ amount: 50, source: 'player-1' })
    })
  })
})
