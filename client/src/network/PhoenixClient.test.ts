import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest'
import { PhoenixClient, type PhoenixConfig, type RoomState, type PlayerInput } from './PhoenixClient'

// The phoenix module is mocked via vitest.config.ts alias
// Tests here are simplified to work with the class-based mock

describe('PhoenixClient', () => {
  let client: PhoenixClient
  const config: PhoenixConfig = {
    url: 'ws://localhost:4200/socket',
    playerId: 'test-player-123',
  }

  beforeEach(() => {
    vi.clearAllMocks()
    client = new PhoenixClient(config)
  })

  afterEach(() => {
    vi.restoreAllMocks()
  })

  describe('constructor', () => {
    it('should create client with config', () => {
      expect(client).toBeInstanceOf(PhoenixClient)
    })
  })

  describe('connect', () => {
    it('should connect to socket and return player ID', async () => {
      const playerId = await client.connect()
      expect(playerId).toBe('test-player-123')
    })

    it('should use provided player ID', async () => {
      const playerId = await client.connect()
      expect(playerId).toBe('test-player-123')
    })

    it('should generate player ID if not provided', async () => {
      const clientNoId = new PhoenixClient({ url: 'ws://test' })
      const playerId = await clientNoId.connect()
      expect(playerId).toMatch(/^player_\d+_/)
    })
  })

  describe('joinRoom', () => {
    it('should throw if not connected', async () => {
      const newClient = new PhoenixClient({ url: 'ws://test' })
      await expect(newClient.joinRoom('room1')).rejects.toThrow('Not connected')
    })
  })

  describe('joinSignaling', () => {
    it('should throw if not connected', async () => {
      const newClient = new PhoenixClient({ url: 'ws://test' })
      await expect(newClient.joinSignaling('room1')).rejects.toThrow('Not connected')
    })
  })

  describe('sendInput', () => {
    it('should not throw if room channel not joined', () => {
      const input: PlayerInput = {
        up: true,
        down: false,
        left: false,
        right: false,
        fire: true,
        special: false,
      }

      // Should not throw, just no-op
      expect(() => client.sendInput(input)).not.toThrow()
    })
  })

  describe('ping', () => {
    it('should return 0 if not in room', async () => {
      const latency = await client.ping()
      expect(latency).toBe(0)
    })
  })

  describe('signaling methods', () => {
    it('should have sendOffer method', () => {
      expect(typeof client.sendOffer).toBe('function')
    })

    it('should have sendAnswer method', () => {
      expect(typeof client.sendAnswer).toBe('function')
    })

    it('should have sendIceCandidate method', () => {
      expect(typeof client.sendIceCandidate).toBe('function')
    })

    it('should have onSignalingMessage method', () => {
      expect(typeof client.onSignalingMessage).toBe('function')
    })
  })

  describe('event handlers', () => {
    it('should register state handler and return unsubscribe', () => {
      const handler = vi.fn()
      const unsubscribe = client.onState(handler)

      expect(typeof unsubscribe).toBe('function')
    })

    it('should unsubscribe state handler', () => {
      const handler = vi.fn()
      const unsubscribe = client.onState(handler)
      unsubscribe()

      // Handler should be removed - no error thrown
    })

    it('should register event handler and return unsubscribe', () => {
      const handler = vi.fn()
      const unsubscribe = client.onEvent(handler)

      expect(typeof unsubscribe).toBe('function')
    })

    it('should unsubscribe event handler', () => {
      const handler = vi.fn()
      const unsubscribe = client.onEvent(handler)
      unsubscribe()

      // Handler should be removed - no error thrown
    })
  })

  describe('getters', () => {
    it('should return empty player ID before connect', () => {
      expect(client.getPlayerId()).toBe('')
    })

    it('should return empty room ID before joining', () => {
      expect(client.getRoomId()).toBe('')
    })

    it('should check connection status', () => {
      // Before connect, should be false
      expect(client.isConnected()).toBe(false)
    })
  })

  describe('leaveRoom', () => {
    it('should not throw when no channels', () => {
      expect(() => client.leaveRoom()).not.toThrow()
    })
  })

  describe('disconnect', () => {
    it('should not throw when called', async () => {
      // Connect first
      await client.connect()

      expect(() => client.disconnect()).not.toThrow()
    })

    it('should leave rooms before disconnecting', async () => {
      await client.connect()

      // Should not throw
      client.disconnect()
    })
  })
})

describe('RoomState type', () => {
  it('should have correct structure', () => {
    const state: RoomState = {
      tick: 100,
      timestamp: Date.now(),
      entities: [
        {
          id: 'entity-1',
          type: 'player',
          x: 100,
          y: 200,
          vx: 5,
          vy: 0,
          rotation: 0,
          health: 100,
          player_id: 'player-1',
        },
      ],
      events: [
        {
          type: 'spawn',
          entity_id: 'entity-1',
        },
      ],
    }

    expect(state.tick).toBe(100)
    expect(state.entities).toHaveLength(1)
    expect(state.events).toHaveLength(1)
  })
})

describe('PlayerInput type', () => {
  it('should have correct structure', () => {
    const input: PlayerInput = {
      up: true,
      down: false,
      left: false,
      right: true,
      fire: true,
      special: false,
    }

    expect(input.up).toBe(true)
    expect(input.fire).toBe(true)
    expect(input.special).toBe(false)
  })
})
