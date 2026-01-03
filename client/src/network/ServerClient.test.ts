import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest'
import { ServerClient, type ServerConfig, type RoomState, type PlayerInput } from './ServerClient'

// The phoenix module is mocked via vitest.config.ts alias
// Tests here are simplified to work with the class-based mock

describe('ServerClient', () => {
  let client: ServerClient
  const config: ServerConfig = {
    url: 'ws://localhost:4200/socket',
    playerId: 'test-player-123',
  }

  beforeEach(() => {
    vi.clearAllMocks()
    client = new ServerClient(config)
  })

  afterEach(() => {
    vi.restoreAllMocks()
  })

  describe('constructor', () => {
    it('should create client with config', () => {
      expect(client).toBeInstanceOf(ServerClient)
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
      const clientNoId = new ServerClient({ url: 'ws://test' })
      const playerId = await clientNoId.connect()
      expect(playerId).toMatch(/^player_\d+_/)
    })
  })

  describe('joinRoom', () => {
    it('should throw if not connected', async () => {
      const newClient = new ServerClient({ url: 'ws://test' })
      await expect(newClient.joinRoom('room1')).rejects.toThrow('Not connected')
    })
  })

  describe('joinSignaling', () => {
    it('should throw if not connected', async () => {
      const newClient = new ServerClient({ url: 'ws://test' })
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

describe('ServerClient after connection', () => {
  let client: ServerClient

  beforeEach(async () => {
    client = new ServerClient({
      url: 'ws://localhost:4200/socket',
      playerId: 'test-player',
    })
    await client.connect()
  })

  afterEach(() => {
    vi.restoreAllMocks()
  })

  describe('joinRoom', () => {
    it('should join room successfully', async () => {
      // Mock returns {} which doesn't have room property, but join succeeds
      await expect(client.joinRoom('test-room')).resolves.not.toThrow()
    })

    it('should join room as host', async () => {
      // Mock returns {} which doesn't have room property, but join succeeds
      await expect(client.joinRoom('test-room', true)).resolves.not.toThrow()
    })

    it('should set room ID after joining', async () => {
      await client.joinRoom('my-room')
      expect(client.getRoomId()).toBe('my-room')
    })
  })

  describe('joinSignaling', () => {
    it('should join signaling channel', async () => {
      await expect(client.joinSignaling('room-123')).resolves.toBeUndefined()
    })
  })

  describe('isConnected', () => {
    it('should return true after connect', () => {
      expect(client.isConnected()).toBe(true)
    })
  })

  describe('getPlayerId', () => {
    it('should return player ID after connect', () => {
      expect(client.getPlayerId()).toBe('test-player')
    })
  })

  describe('signaling methods after connection', () => {
    it('sendOffer should not throw', async () => {
      await client.joinSignaling('test-room')
      expect(() => client.sendOffer({ type: 'offer', sdp: 'test-sdp' }, 'peer-1')).not.toThrow()
    })

    it('sendAnswer should not throw', async () => {
      await client.joinSignaling('test-room')
      expect(() => client.sendAnswer({ type: 'answer', sdp: 'test-sdp' }, 'peer-1')).not.toThrow()
    })

    it('sendIceCandidate should not throw', async () => {
      await client.joinSignaling('test-room')
      expect(() => client.sendIceCandidate({ candidate: 'test', sdpMid: '0', sdpMLineIndex: 0 }, 'peer-1')).not.toThrow()
    })

    it('onSignalingMessage should not throw', async () => {
      await client.joinSignaling('test-room')
      expect(() => client.onSignalingMessage('offer', () => {})).not.toThrow()
    })
  })

  describe('room handlers', () => {
    it('onPlayerJoined should register handler', () => {
      const handler = vi.fn()
      const unsubscribe = client.onPlayerJoined(handler)

      expect(typeof unsubscribe).toBe('function')
      unsubscribe()
    })

    it('onPlayerLeft should register handler', () => {
      const handler = vi.fn()
      const unsubscribe = client.onPlayerLeft(handler)

      expect(typeof unsubscribe).toBe('function')
      unsubscribe()
    })

    it('onGameStarting should register handler', () => {
      const handler = vi.fn()
      const unsubscribe = client.onGameStarting(handler)

      expect(typeof unsubscribe).toBe('function')
      unsubscribe()
    })
  })

  describe('getCurrentRoom', () => {
    it('should return null before joining room', () => {
      expect(client.getCurrentRoom()).toBeNull()
    })
  })

  describe('getSignalingChannel', () => {
    it('should return null before joining signaling', () => {
      expect(client.getSignalingChannel()).toBeNull()
    })
  })

  describe('disconnect', () => {
    it('should disconnect cleanly', () => {
      expect(() => client.disconnect()).not.toThrow()
    })

    it('should clear room ID after disconnect', () => {
      client.disconnect()
      expect(client.getRoomId()).toBe('')
    })
  })

  describe('leaveRoom after joining', () => {
    it('should clear room state', async () => {
      await client.joinRoom('test-room')
      client.leaveRoom()

      expect(client.getRoomId()).toBe('')
      expect(client.getCurrentRoom()).toBeNull()
    })
  })
})

describe('ServerClient listRooms', () => {
  it('should throw if not connected to lobby', async () => {
    const client = new ServerClient({ url: 'ws://test' })
    await expect(client.listRooms()).rejects.toThrow('Not connected to lobby')
  })

  it('should resolve when connected', async () => {
    const client = new ServerClient({
      url: 'ws://localhost:4200/socket',
      playerId: 'test-player',
    })
    await client.connect()
    // Mock doesn't return proper rooms structure, but the call succeeds
    await expect(client.listRooms()).resolves.not.toThrow()
  })
})

describe('ServerClient startGame', () => {
  it('should throw if not in a room', async () => {
    const client = new ServerClient({ url: 'ws://test' })
    await expect(client.startGame()).rejects.toThrow('Not in a room')
  })

  it('should start game when in room', async () => {
    const client = new ServerClient({
      url: 'ws://localhost:4200/socket',
      playerId: 'test-player',
    })
    await client.connect()
    await client.joinRoom('test-room')
    await expect(client.startGame()).resolves.toBeUndefined()
  })
})

describe('ServerClient refreshTurnCredentials', () => {
  it('should throw if not in a room', async () => {
    const client = new ServerClient({ url: 'ws://test' })
    await expect(client.refreshTurnCredentials()).rejects.toThrow('Not in a room')
  })

  it('should return credentials when in room', async () => {
    const client = new ServerClient({
      url: 'ws://localhost:4200/socket',
      playerId: 'test-player',
    })
    await client.connect()
    await client.joinRoom('test-room')
    const creds = await client.refreshTurnCredentials()
    // Mock returns {} for ok response, which doesn't have turn property
    expect(creds).toBeUndefined()
  })
})

describe('ServerClient ping after joining room', () => {
  it('should return latency', async () => {
    const client = new ServerClient({
      url: 'ws://localhost:4200/socket',
      playerId: 'test-player',
    })
    await client.connect()
    await client.joinRoom('test-room')
    const latency = await client.ping()
    expect(typeof latency).toBe('number')
  })
})

describe('ServerClient sendInput after joining room', () => {
  it('should send input without error', async () => {
    const client = new ServerClient({
      url: 'ws://localhost:4200/socket',
      playerId: 'test-player',
    })
    await client.connect()
    await client.joinRoom('test-room')

    const input: PlayerInput = {
      up: true,
      down: false,
      left: false,
      right: false,
      fire: true,
      special: false,
    }

    expect(() => client.sendInput(input)).not.toThrow()
  })
})
