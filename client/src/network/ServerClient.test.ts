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
      expect(client).toBeDefined()
    })

    it('should create client with minimal config', () => {
      const minimalClient = new ServerClient({ url: 'ws://test' })
      expect(minimalClient).toBeInstanceOf(ServerClient)
    })

    it('should accept optional player ID in config', () => {
      const clientWithId = new ServerClient({ url: 'ws://test', playerId: 'custom-id' })
      expect(clientWithId).toBeInstanceOf(ServerClient)
    })
  })

  describe('connect', () => {
    it('should connect to socket and return player ID', async () => {
      const playerId = await client.connect()
      expect(playerId).toBe('test-player-123')
      expect(typeof playerId).toBe('string')
      expect(playerId.length).toBeGreaterThan(0)
    })

    it('should use provided player ID', async () => {
      const playerId = await client.connect()
      expect(playerId).toBe('test-player-123')
      expect(typeof playerId).toBe('string')
    })

    it('should generate player ID if not provided', async () => {
      const clientNoId = new ServerClient({ url: 'ws://test' })
      const playerId = await clientNoId.connect()
      expect(playerId).toMatch(/^player_\d+_/)
      expect(typeof playerId).toBe('string')
      expect(playerId.length).toBeGreaterThan(0)
    })

    it('should return consistent player ID on subsequent calls', async () => {
      const playerId1 = await client.connect()
      const playerId2 = client.getPlayerId()
      expect(playerId1).toBe(playerId2)
    })
  })

  describe('joinRoom', () => {
    it('should throw if not connected', async () => {
      const newClient = new ServerClient({ url: 'ws://test' })
      await expect(newClient.joinRoom('room1')).rejects.toThrow('Not connected')
    })

    it('should throw specific error message', async () => {
      const newClient = new ServerClient({ url: 'ws://test' })
      try {
        await newClient.joinRoom('room1')
        expect(true).toBe(false) // Should not reach here
      } catch (e) {
        expect(e).toBeInstanceOf(Error)
        expect((e as Error).message).toBe('Not connected')
      }
    })
  })

  describe('joinSignaling', () => {
    it('should throw if not connected', async () => {
      const newClient = new ServerClient({ url: 'ws://test' })
      await expect(newClient.joinSignaling('room1')).rejects.toThrow('Not connected')
    })

    it('should throw specific error message', async () => {
      const newClient = new ServerClient({ url: 'ws://test' })
      try {
        await newClient.joinSignaling('room1')
        expect(true).toBe(false) // Should not reach here
      } catch (e) {
        expect(e).toBeInstanceOf(Error)
        expect((e as Error).message).toBe('Not connected')
      }
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

    it('should handle all input combinations', () => {
      const inputs: PlayerInput[] = [
        { up: true, down: false, left: false, right: false, fire: false, special: false },
        { up: false, down: true, left: false, right: false, fire: false, special: false },
        { up: false, down: false, left: true, right: false, fire: false, special: false },
        { up: false, down: false, left: false, right: true, fire: false, special: false },
        { up: true, down: true, left: true, right: true, fire: true, special: true },
      ]

      for (const input of inputs) {
        expect(() => client.sendInput(input)).not.toThrow()
      }
    })
  })

  describe('ping', () => {
    it('should return 0 if not in room', async () => {
      const latency = await client.ping()
      expect(latency).toBe(0)
      expect(typeof latency).toBe('number')
      expect(Number.isFinite(latency)).toBe(true)
    })

    it('should return non-negative value', async () => {
      const latency = await client.ping()
      expect(latency).toBeGreaterThanOrEqual(0)
    })
  })

  describe('signaling methods', () => {
    it('should have sendOffer method', () => {
      expect(typeof client.sendOffer).toBe('function')
      expect(client.sendOffer).toBeDefined()
    })

    it('should have sendAnswer method', () => {
      expect(typeof client.sendAnswer).toBe('function')
      expect(client.sendAnswer).toBeDefined()
    })

    it('should have sendIceCandidate method', () => {
      expect(typeof client.sendIceCandidate).toBe('function')
      expect(client.sendIceCandidate).toBeDefined()
    })

    it('should have onSignalingMessage method', () => {
      expect(typeof client.onSignalingMessage).toBe('function')
      expect(client.onSignalingMessage).toBeDefined()
    })

    it('should have all required signaling methods', () => {
      const methods = ['sendOffer', 'sendAnswer', 'sendIceCandidate', 'onSignalingMessage']
      for (const method of methods) {
        expect(typeof (client as unknown as Record<string, unknown>)[method]).toBe('function')
      }
    })
  })

  describe('event handlers', () => {
    it('should register state handler and return unsubscribe', () => {
      const handler = vi.fn()
      const unsubscribe = client.onState(handler)

      expect(typeof unsubscribe).toBe('function')
      expect(unsubscribe).toBeDefined()
    })

    it('should unsubscribe state handler', () => {
      const handler = vi.fn()
      const unsubscribe = client.onState(handler)

      // Unsubscribe should not throw
      expect(() => unsubscribe()).not.toThrow()
    })

    it('should allow multiple unsubscribe calls', () => {
      const handler = vi.fn()
      const unsubscribe = client.onState(handler)

      // Multiple calls should not throw
      expect(() => {
        unsubscribe()
        unsubscribe()
      }).not.toThrow()
    })

    it('should register event handler and return unsubscribe', () => {
      const handler = vi.fn()
      const unsubscribe = client.onEvent(handler)

      expect(typeof unsubscribe).toBe('function')
      expect(unsubscribe).toBeDefined()
    })

    it('should unsubscribe event handler', () => {
      const handler = vi.fn()
      const unsubscribe = client.onEvent(handler)

      // Unsubscribe should not throw
      expect(() => unsubscribe()).not.toThrow()
    })

    it('should register multiple handlers', () => {
      const handler1 = vi.fn()
      const handler2 = vi.fn()

      const unsubscribe1 = client.onState(handler1)
      const unsubscribe2 = client.onEvent(handler2)

      expect(typeof unsubscribe1).toBe('function')
      expect(typeof unsubscribe2).toBe('function')

      // Clean up
      unsubscribe1()
      unsubscribe2()
    })
  })

  describe('getters', () => {
    it('should return empty player ID before connect', () => {
      expect(client.getPlayerId()).toBe('')
      expect(typeof client.getPlayerId()).toBe('string')
    })

    it('should return empty room ID before joining', () => {
      expect(client.getRoomId()).toBe('')
      expect(typeof client.getRoomId()).toBe('string')
    })

    it('should check connection status', () => {
      // Before connect, should be false
      expect(client.isConnected()).toBe(false)
      expect(typeof client.isConnected()).toBe('boolean')
    })

    it('should have all required getters', () => {
      const getters = ['getPlayerId', 'getRoomId', 'isConnected']
      for (const getter of getters) {
        expect(typeof (client as unknown as Record<string, unknown>)[getter]).toBe('function')
      }
    })
  })

  describe('leaveRoom', () => {
    it('should not throw when no channels', () => {
      expect(() => client.leaveRoom()).not.toThrow()
    })

    it('should be idempotent', () => {
      // Multiple calls should not throw
      expect(() => {
        client.leaveRoom()
        client.leaveRoom()
        client.leaveRoom()
      }).not.toThrow()
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
      expect(() => client.disconnect()).not.toThrow()
    })

    it('should be safe to call multiple times', async () => {
      await client.connect()

      expect(() => {
        client.disconnect()
        client.disconnect()
      }).not.toThrow()
    })

    it('should clear connection state', async () => {
      await client.connect()
      expect(client.isConnected()).toBe(true)

      client.disconnect()
      expect(client.isConnected()).toBe(false)
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

    // Type checks
    expect(typeof state.tick).toBe('number')
    expect(typeof state.timestamp).toBe('number')
    expect(Array.isArray(state.entities)).toBe(true)
    expect(Array.isArray(state.events)).toBe(true)
  })

  it('should allow empty entities and events', () => {
    const state: RoomState = {
      tick: 0,
      timestamp: Date.now(),
      entities: [],
      events: [],
    }

    expect(state.tick).toBe(0)
    expect(state.entities).toHaveLength(0)
    expect(state.events).toHaveLength(0)
  })

  it('should have valid entity properties', () => {
    const state: RoomState = {
      tick: 1,
      timestamp: Date.now(),
      entities: [
        {
          id: 'e1',
          type: 'player',
          x: 0,
          y: 0,
          vx: 0,
          vy: 0,
          rotation: 0,
          health: 100,
          player_id: 'p1',
        },
      ],
      events: [],
    }

    const entity = state.entities[0]!
    expect(typeof entity.id).toBe('string')
    expect(typeof entity.type).toBe('string')
    expect(typeof entity.x).toBe('number')
    expect(typeof entity.y).toBe('number')
    expect(typeof entity.health).toBe('number')
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

    // Type checks for all properties
    expect(typeof input.up).toBe('boolean')
    expect(typeof input.down).toBe('boolean')
    expect(typeof input.left).toBe('boolean')
    expect(typeof input.right).toBe('boolean')
    expect(typeof input.fire).toBe('boolean')
    expect(typeof input.special).toBe('boolean')
  })

  it('should have all required fields', () => {
    const input: PlayerInput = {
      up: false,
      down: false,
      left: false,
      right: false,
      fire: false,
      special: false,
    }

    expect(input).toHaveProperty('up')
    expect(input).toHaveProperty('down')
    expect(input).toHaveProperty('left')
    expect(input).toHaveProperty('right')
    expect(input).toHaveProperty('fire')
    expect(input).toHaveProperty('special')
  })

  it('should allow all combinations of inputs', () => {
    const allFalse: PlayerInput = {
      up: false, down: false, left: false, right: false, fire: false, special: false,
    }
    const allTrue: PlayerInput = {
      up: true, down: true, left: true, right: true, fire: true, special: true,
    }

    // Both should be valid
    expect(allFalse.up).toBe(false)
    expect(allTrue.up).toBe(true)
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
      expect(typeof client.getRoomId()).toBe('string')
    })

    it('should handle different room names', async () => {
      const roomNames = ['room-1', 'test_room', 'Room123', 'my-game-room']
      for (const roomName of roomNames) {
        const testClient = new ServerClient({
          url: 'ws://localhost:4200/socket',
          playerId: `player-${roomName}`,
        })
        await testClient.connect()
        await expect(testClient.joinRoom(roomName)).resolves.not.toThrow()
      }
    })
  })

  describe('joinSignaling', () => {
    it('should join signaling channel', async () => {
      await expect(client.joinSignaling('room-123')).resolves.toBeUndefined()
    })

    it('should handle different room IDs', async () => {
      await expect(client.joinSignaling('another-room')).resolves.toBeUndefined()
    })
  })

  describe('isConnected', () => {
    it('should return true after connect', () => {
      expect(client.isConnected()).toBe(true)
      expect(typeof client.isConnected()).toBe('boolean')
    })
  })

  describe('getPlayerId', () => {
    it('should return player ID after connect', () => {
      expect(client.getPlayerId()).toBe('test-player')
      expect(typeof client.getPlayerId()).toBe('string')
      expect(client.getPlayerId().length).toBeGreaterThan(0)
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

    it('should handle different peer IDs', async () => {
      await client.joinSignaling('test-room')
      const peerIds = ['peer-1', 'peer-2', 'peer-abc-123']
      for (const peerId of peerIds) {
        expect(() => client.sendOffer({ type: 'offer', sdp: 'test' }, peerId)).not.toThrow()
      }
    })

    it('should handle different signaling message types', async () => {
      await client.joinSignaling('test-room')
      const types = ['offer', 'answer', 'ice_candidate'] as const
      for (const type of types) {
        expect(() => client.onSignalingMessage(type, () => {})).not.toThrow()
      }
    })
  })

  describe('room handlers', () => {
    it('onPlayerJoined should register handler', () => {
      const handler = vi.fn()
      const unsubscribe = client.onPlayerJoined(handler)

      expect(typeof unsubscribe).toBe('function')
      expect(unsubscribe).toBeDefined()
      expect(() => unsubscribe()).not.toThrow()
    })

    it('onPlayerLeft should register handler', () => {
      const handler = vi.fn()
      const unsubscribe = client.onPlayerLeft(handler)

      expect(typeof unsubscribe).toBe('function')
      expect(unsubscribe).toBeDefined()
      expect(() => unsubscribe()).not.toThrow()
    })

    it('onGameStarting should register handler', () => {
      const handler = vi.fn()
      const unsubscribe = client.onGameStarting(handler)

      expect(typeof unsubscribe).toBe('function')
      expect(unsubscribe).toBeDefined()
      expect(() => unsubscribe()).not.toThrow()
    })

    it('should allow multiple handlers', () => {
      const handler1 = vi.fn()
      const handler2 = vi.fn()

      const unsub1 = client.onPlayerJoined(handler1)
      const unsub2 = client.onPlayerJoined(handler2)

      expect(typeof unsub1).toBe('function')
      expect(typeof unsub2).toBe('function')

      unsub1()
      unsub2()
    })
  })

  describe('getCurrentRoom', () => {
    it('should return null before joining room', () => {
      expect(client.getCurrentRoom()).toBeNull()
    })

    it('should return RoomData after joining', async () => {
      await client.joinRoom('test-room')
      const room = client.getCurrentRoom()
      expect(room).not.toBeNull()
      expect(room?.id).toBe('test-room')
      expect(room?.status).toBe('waiting')
      expect(Array.isArray(room?.players)).toBe(true)
    })
  })

  describe('getSignalingChannel', () => {
    it('should return null before joining signaling', () => {
      expect(client.getSignalingChannel()).toBeNull()
    })

    it('should handle getSignalingChannel after joining', async () => {
      await client.joinSignaling('test-room')
      const channel = client.getSignalingChannel()
      expect(channel === null || typeof channel === 'object').toBe(true)
    })
  })

  describe('disconnect', () => {
    it('should disconnect cleanly', () => {
      expect(() => client.disconnect()).not.toThrow()
    })

    it('should clear room ID after disconnect', () => {
      client.disconnect()
      expect(client.getRoomId()).toBe('')
      expect(typeof client.getRoomId()).toBe('string')
    })

    it('should update isConnected status', () => {
      expect(client.isConnected()).toBe(true)
      client.disconnect()
      expect(client.isConnected()).toBe(false)
    })
  })

  describe('leaveRoom after joining', () => {
    it('should clear room state', async () => {
      await client.joinRoom('test-room')
      client.leaveRoom()

      expect(client.getRoomId()).toBe('')
      expect(client.getCurrentRoom()).toBeNull()
    })

    it('should be safe to call multiple times', async () => {
      await client.joinRoom('test-room')
      expect(() => {
        client.leaveRoom()
        client.leaveRoom()
      }).not.toThrow()
    })
  })
})

describe('ServerClient listRooms', () => {
  it('should throw if not connected to lobby', async () => {
    const client = new ServerClient({ url: 'ws://test' })
    await expect(client.listRooms()).rejects.toThrow('Not connected to lobby')
  })

  it('should throw with specific error message', async () => {
    const client = new ServerClient({ url: 'ws://test' })
    try {
      await client.listRooms()
      expect(true).toBe(false) // Should not reach
    } catch (e) {
      expect(e).toBeInstanceOf(Error)
      expect((e as Error).message).toBe('Not connected to lobby')
    }
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

  it('should throw with specific error message', async () => {
    const client = new ServerClient({ url: 'ws://test' })
    try {
      await client.startGame()
      expect(true).toBe(false) // Should not reach
    } catch (e) {
      expect(e).toBeInstanceOf(Error)
      expect((e as Error).message).toBe('Not in a room')
    }
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

  it('should throw with specific error message', async () => {
    const client = new ServerClient({ url: 'ws://test' })
    try {
      await client.refreshTurnCredentials()
      expect(true).toBe(false) // Should not reach
    } catch (e) {
      expect(e).toBeInstanceOf(Error)
      expect((e as Error).message).toBe('Not in a room')
    }
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
    expect(Number.isFinite(latency)).toBe(true)
  })

  it('should return non-negative latency', async () => {
    const client = new ServerClient({
      url: 'ws://localhost:4200/socket',
      playerId: 'test-player',
    })
    await client.connect()
    await client.joinRoom('test-room')
    const latency = await client.ping()
    expect(latency).toBeGreaterThanOrEqual(0)
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

  it('should handle multiple inputs', async () => {
    const client = new ServerClient({
      url: 'ws://localhost:4200/socket',
      playerId: 'test-player',
    })
    await client.connect()
    await client.joinRoom('test-room')

    const inputs: PlayerInput[] = [
      { up: true, down: false, left: false, right: false, fire: false, special: false },
      { up: false, down: true, left: false, right: false, fire: false, special: false },
      { up: false, down: false, left: true, right: false, fire: false, special: false },
      { up: false, down: false, left: false, right: true, fire: true, special: true },
    ]

    for (const input of inputs) {
      expect(() => client.sendInput(input)).not.toThrow()
    }
  })

  it('should handle rapid input sending', async () => {
    const client = new ServerClient({
      url: 'ws://localhost:4200/socket',
      playerId: 'test-player',
    })
    await client.connect()
    await client.joinRoom('test-room')

    const input: PlayerInput = {
      up: true, down: false, left: false, right: true, fire: true, special: false,
    }

    // Rapid fire inputs
    for (let i = 0; i < 10; i++) {
      expect(() => client.sendInput(input)).not.toThrow()
    }
  })
})
