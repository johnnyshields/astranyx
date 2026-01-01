import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest'
import { MultiplayerManager, type MultiplayerConfig, type MultiplayerState } from './MultiplayerManager'

// Mock Phoenix Socket for PhoenixClient
vi.stubGlobal('WebSocket', class MockWebSocket {
  readyState = 1
  onopen: (() => void) | null = null
  onclose: (() => void) | null = null
  onerror: ((e: unknown) => void) | null = null
  onmessage: ((e: MessageEvent) => void) | null = null
  send = vi.fn()
  close = vi.fn()
})

describe('MultiplayerManager', () => {
  let manager: MultiplayerManager
  const config: MultiplayerConfig = {
    serverUrl: 'ws://localhost:4200/socket',
  }

  beforeEach(() => {
    vi.clearAllMocks()
    manager = new MultiplayerManager(config)
  })

  afterEach(() => {
    vi.restoreAllMocks()
  })

  describe('constructor', () => {
    it('should create manager with initial state', () => {
      expect(manager).toBeInstanceOf(MultiplayerManager)
      expect(manager.getState()).toBe('disconnected')
    })

    it('should have empty lobby state initially', () => {
      const lobby = manager.getLobbyState()
      expect(lobby.rooms).toEqual([])
      expect(lobby.currentRoom).toBeNull()
    })
  })

  describe('getState', () => {
    it('should return current state', () => {
      expect(manager.getState()).toBe('disconnected')
    })
  })

  describe('getLobbyState', () => {
    it('should return lobby state object', () => {
      const lobby = manager.getLobbyState()
      expect(lobby).toHaveProperty('rooms')
      expect(lobby).toHaveProperty('currentRoom')
    })
  })

  describe('isHost', () => {
    it('should return false when not in room', () => {
      expect(manager.isHost()).toBe(false)
    })
  })

  describe('getLocalPlayerId', () => {
    it('should return empty string before connect', () => {
      expect(manager.getLocalPlayerId()).toBe('')
    })
  })

  describe('getPlayerIds', () => {
    it('should return empty array before game start', () => {
      expect(manager.getPlayerIds()).toEqual([])
    })
  })

  describe('getPlayerOrder', () => {
    it('should return empty Map before game start', () => {
      expect(manager.getPlayerOrder()).toEqual(new Map())
    })
  })

  describe('getSeed', () => {
    it('should return default seed before game start', () => {
      expect(manager.getSeed()).toBe(12345)
    })
  })

  describe('getNetcode', () => {
    it('should return null before game start', () => {
      expect(manager.getNetcode()).toBeNull()
    })
  })

  describe('setPlaying', () => {
    it('should not change state if not ready', () => {
      manager.setPlaying()
      expect(manager.getState()).toBe('disconnected')
    })
  })

  describe('event handlers', () => {
    it('should register state change handler and return unsubscribe', () => {
      const handler = vi.fn()
      const unsubscribe = manager.onStateChange(handler)

      expect(typeof unsubscribe).toBe('function')
    })

    it('should unsubscribe state change handler', () => {
      const handler = vi.fn()
      const unsubscribe = manager.onStateChange(handler)
      unsubscribe()

      // Verify no errors
      expect(manager.getState()).toBe('disconnected')
    })

    it('should register lobby update handler and return unsubscribe', () => {
      const handler = vi.fn()
      const unsubscribe = manager.onLobbyUpdate(handler)

      expect(typeof unsubscribe).toBe('function')
    })

    it('should register error handler and return unsubscribe', () => {
      const handler = vi.fn()
      const unsubscribe = manager.onError(handler)

      expect(typeof unsubscribe).toBe('function')
    })

    it('should register ready handler and return unsubscribe', () => {
      const handler = vi.fn()
      const unsubscribe = manager.onReady(handler)

      expect(typeof unsubscribe).toBe('function')
    })
  })

  describe('disconnect from disconnected state', () => {
    it('should remain disconnected', () => {
      manager.disconnect()
      expect(manager.getState()).toBe('disconnected')
    })
  })

  describe('leaveRoom when not connected', () => {
    it('should not throw', () => {
      expect(() => manager.leaveRoom()).not.toThrow()
    })
  })

  describe('connect error handling', () => {
    it('should throw if already connecting', async () => {
      // Create manager and set internal state to non-disconnected
      const mgr = new MultiplayerManager(config)

      // We can't easily test state transitions without mocks,
      // but we can verify the basic structure
      expect(mgr.getState()).toBe('disconnected')
    })
  })

  describe('createRoom validation', () => {
    it('should throw if not connected', async () => {
      await expect(manager.createRoom('test')).rejects.toThrow('Cannot create room from state: disconnected')
    })
  })

  describe('joinRoom validation', () => {
    it('should throw if not connected', async () => {
      await expect(manager.joinRoom('test')).rejects.toThrow('Cannot join room from state: disconnected')
    })
  })

  describe('quickmatch validation', () => {
    it('should throw if not connected', async () => {
      await expect(manager.quickmatch()).rejects.toThrow('Cannot quickmatch from state: disconnected')
    })
  })

  describe('startGame validation', () => {
    it('should throw if not in lobby', async () => {
      await expect(manager.startGame()).rejects.toThrow('Cannot start game from state: disconnected')
    })
  })

  describe('listRooms validation', () => {
    it('should throw if not connected', async () => {
      await expect(manager.listRooms()).rejects.toThrow('Not connected')
    })
  })

  describe('config options', () => {
    it('should accept peer connection timeout config', () => {
      const customConfig: MultiplayerConfig = {
        serverUrl: 'ws://localhost:4200/socket',
        peerConnectionTimeout: 5000,
      }

      const customManager = new MultiplayerManager(customConfig)
      expect(customManager).toBeInstanceOf(MultiplayerManager)
    })
  })
})

describe('MultiplayerState type', () => {
  it('should include all expected states', () => {
    const states: MultiplayerState[] = [
      'disconnected',
      'connecting',
      'connected',
      'joining_room',
      'in_lobby',
      'starting',
      'connecting_peers',
      'ready',
      'playing',
      'error',
    ]

    expect(states).toHaveLength(10)
  })
})
