import { describe, it, expect, beforeEach, vi, afterEach, type Mock } from 'vitest'
import { MultiplayerManager, type MultiplayerConfig, type MultiplayerState } from './MultiplayerManager'
import type { RoomInfo, GameStartingData } from './ServerClient'

// Mock callback functions for ServerClient
let serverClientInstance: {
  connect: Mock
  disconnect: Mock
  joinRoom: Mock
  leaveRoom: Mock
  listRooms: Mock
  startGame: Mock
  joinSignaling: Mock
  getPlayerId: Mock
  getSignalingChannel: Mock
  getCurrentRoom: Mock
  refreshTurnCredentials: Mock
  onPlayerJoined: Mock
  onPlayerLeft: Mock
  onGameStarting: Mock
}

let p2pManagerInstance: {
  setIceServers: Mock
  updateIceServers: Mock
  setSignalingChannel: Mock
  onConnected: Mock
  onDisconnected: Mock
  connectToPlayers: Mock
  disconnect: Mock
}

let lockstepNetcodeInstance: {
  addPeer: Mock
  removePeer: Mock
  stop: Mock
}

// Track callback handlers for later invocation
let playerJoinedHandler: ((payload: { players: string[] }) => void) | null = null
let playerLeftHandler: ((payload: { player_id: string }) => void) | null = null
let gameStartingHandler: ((data: GameStartingData) => void) | null = null
let p2pConnectedHandler: ((playerId: string, channel: RTCDataChannel) => void) | null = null
let p2pDisconnectedHandler: ((playerId: string) => void) | null = null

// Mock ServerClient
vi.mock('./ServerClient.ts', () => {
  return {
    ServerClient: class MockServerClient {
      connect = serverClientInstance.connect
      disconnect = serverClientInstance.disconnect
      joinRoom = serverClientInstance.joinRoom
      leaveRoom = serverClientInstance.leaveRoom
      listRooms = serverClientInstance.listRooms
      startGame = serverClientInstance.startGame
      joinSignaling = serverClientInstance.joinSignaling
      getPlayerId = serverClientInstance.getPlayerId
      getSignalingChannel = serverClientInstance.getSignalingChannel
      getCurrentRoom = serverClientInstance.getCurrentRoom
      refreshTurnCredentials = serverClientInstance.refreshTurnCredentials
      onPlayerJoined(handler: (payload: { players: string[] }) => void) {
        playerJoinedHandler = handler
      }
      onPlayerLeft(handler: (payload: { player_id: string }) => void) {
        playerLeftHandler = handler
      }
      onGameStarting(handler: (data: GameStartingData) => void) {
        gameStartingHandler = handler
      }
    },
  }
})

// Mock P2PManager
vi.mock('./P2PManager.ts', () => {
  return {
    P2PManager: class MockP2PManager {
      setIceServers = p2pManagerInstance.setIceServers
      updateIceServers = p2pManagerInstance.updateIceServers
      setSignalingChannel = p2pManagerInstance.setSignalingChannel
      onConnected(handler: (playerId: string, channel: RTCDataChannel) => void) {
        p2pConnectedHandler = handler
      }
      onDisconnected(handler: (playerId: string) => void) {
        p2pDisconnectedHandler = handler
      }
      connectToPlayers = p2pManagerInstance.connectToPlayers
      disconnect = p2pManagerInstance.disconnect
    },
  }
})

// Mock LockstepNetcode
vi.mock('./LockstepNetcode.ts', () => {
  return {
    LockstepNetcode: class MockLockstepNetcode {
      addPeer = lockstepNetcodeInstance.addPeer
      removePeer = lockstepNetcodeInstance.removePeer
      stop = lockstepNetcodeInstance.stop
    },
  }
})

describe('MultiplayerManager', () => {
  let manager: MultiplayerManager
  const config: MultiplayerConfig = {
    serverUrl: 'ws://localhost:4200/socket',
  }

  beforeEach(() => {
    vi.clearAllMocks()
    vi.useFakeTimers()

    // Reset handlers
    playerJoinedHandler = null
    playerLeftHandler = null
    gameStartingHandler = null
    p2pConnectedHandler = null
    p2pDisconnectedHandler = null

    // Create fresh mock instances
    serverClientInstance = {
      connect: vi.fn().mockResolvedValue(undefined),
      disconnect: vi.fn(),
      joinRoom: vi.fn().mockResolvedValue({
        id: 'test-room',
        players: ['player-1'],
        host: 'player-1',
        status: 'waiting',
      }),
      leaveRoom: vi.fn(),
      listRooms: vi.fn().mockResolvedValue([]),
      startGame: vi.fn().mockResolvedValue(undefined),
      joinSignaling: vi.fn().mockResolvedValue(undefined),
      getPlayerId: vi.fn().mockReturnValue('local-player'),
      getSignalingChannel: vi.fn().mockReturnValue({ push: vi.fn(), on: vi.fn() }),
      getCurrentRoom: vi.fn().mockReturnValue({ players: ['player-1'] }),
      refreshTurnCredentials: vi.fn().mockResolvedValue({
        urls: ['turn:localhost:3478'],
        username: 'user',
        credential: 'pass',
      }),
      onPlayerJoined: vi.fn(),
      onPlayerLeft: vi.fn(),
      onGameStarting: vi.fn(),
    }

    p2pManagerInstance = {
      setIceServers: vi.fn(),
      updateIceServers: vi.fn(),
      setSignalingChannel: vi.fn(),
      onConnected: vi.fn(),
      onDisconnected: vi.fn(),
      connectToPlayers: vi.fn(),
      disconnect: vi.fn(),
    }

    lockstepNetcodeInstance = {
      addPeer: vi.fn(),
      removePeer: vi.fn(),
      stop: vi.fn(),
    }

    manager = new MultiplayerManager(config)
  })

  afterEach(() => {
    vi.restoreAllMocks()
    vi.useRealTimers()
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

  describe('connect', () => {
    it('should connect successfully and transition states', async () => {
      const stateHandler = vi.fn()
      manager.onStateChange(stateHandler)

      await manager.connect()

      expect(serverClientInstance.connect).toHaveBeenCalled()
      expect(manager.getState()).toBe('connected')
      expect(stateHandler).toHaveBeenCalledWith('connecting')
      expect(stateHandler).toHaveBeenCalledWith('connected')
    })

    it('should throw if already connecting', async () => {
      await manager.connect()

      await expect(manager.connect()).rejects.toThrow('Cannot connect from state: connected')
    })

    it('should handle connection error', async () => {
      const error = new Error('Connection failed')
      serverClientInstance.connect.mockRejectedValue(error)

      const errorHandler = vi.fn()
      manager.onError(errorHandler)

      await expect(manager.connect()).rejects.toThrow('Connection failed')
      expect(manager.getState()).toBe('error')
      expect(errorHandler).toHaveBeenCalledWith(error)
    })
  })

  describe('disconnect', () => {
    it('should disconnect and cleanup', async () => {
      await manager.connect()
      manager.disconnect()

      expect(serverClientInstance.disconnect).toHaveBeenCalled()
      expect(manager.getState()).toBe('disconnected')
    })

    it('should remain disconnected when already disconnected', () => {
      manager.disconnect()
      expect(manager.getState()).toBe('disconnected')
    })
  })

  describe('listRooms', () => {
    it('should list rooms when connected', async () => {
      const rooms: RoomInfo[] = [
        { id: 'room-1', host: 'player-1', player_count: 1, max_players: 4, status: 'waiting' },
      ]
      serverClientInstance.listRooms.mockResolvedValue(rooms)

      await manager.connect()
      const result = await manager.listRooms()

      expect(result).toEqual(rooms)
      expect(manager.getLobbyState().rooms).toEqual(rooms)
    })

    it('should throw if not connected', async () => {
      await expect(manager.listRooms()).rejects.toThrow('Not connected')
    })

    it('should return empty array on error', async () => {
      await manager.connect()
      serverClientInstance.listRooms.mockRejectedValue(new Error('Network error'))

      const result = await manager.listRooms()
      expect(result).toEqual([])
    })
  })

  describe('createRoom', () => {
    it('should create room and join signaling', async () => {
      await manager.connect()
      await manager.createRoom('my-room')

      expect(serverClientInstance.joinRoom).toHaveBeenCalledWith('my-room', true)
      expect(serverClientInstance.joinSignaling).toHaveBeenCalledWith('my-room')
      expect(manager.getState()).toBe('in_lobby')
      expect(manager.isHost()).toBe(true)
    })

    it('should throw if not connected', async () => {
      await expect(manager.createRoom('test')).rejects.toThrow('Cannot create room from state: disconnected')
    })

    it('should handle join error and transition to error state', async () => {
      await manager.connect()
      serverClientInstance.joinRoom.mockRejectedValue(new Error('Room exists'))

      await expect(manager.createRoom('test')).rejects.toThrow('Room exists')
      // handleError sets state to 'error'
      expect(manager.getState()).toBe('error')
    })
  })

  describe('joinRoom', () => {
    it('should join room and signaling', async () => {
      serverClientInstance.joinRoom.mockResolvedValue({
        id: 'existing-room',
        players: ['host', 'local-player'],
        host: 'host',
        status: 'waiting',
      })

      await manager.connect()
      await manager.joinRoom('existing-room')

      expect(serverClientInstance.joinRoom).toHaveBeenCalledWith('existing-room', false)
      expect(manager.getState()).toBe('in_lobby')
      expect(manager.isHost()).toBe(false)
    })

    it('should throw if not connected', async () => {
      await expect(manager.joinRoom('test')).rejects.toThrow('Cannot join room from state: disconnected')
    })
  })

  describe('quickmatch', () => {
    it('should create a random room', async () => {
      await manager.connect()
      await manager.quickmatch()

      expect(serverClientInstance.joinRoom).toHaveBeenCalled()
      expect(manager.getState()).toBe('in_lobby')
    })

    it('should throw if not connected', async () => {
      await expect(manager.quickmatch()).rejects.toThrow('Cannot quickmatch from state: disconnected')
    })
  })

  describe('leaveRoom', () => {
    it('should leave room and cleanup', async () => {
      await manager.connect()
      await manager.createRoom('test-room')

      manager.leaveRoom()

      expect(serverClientInstance.leaveRoom).toHaveBeenCalled()
      expect(manager.getState()).toBe('connected')
      expect(manager.getLobbyState().currentRoom).toBeNull()
    })

    it('should not throw when not in room', () => {
      expect(() => manager.leaveRoom()).not.toThrow()
    })
  })

  describe('startGame', () => {
    it('should start game as host', async () => {
      await manager.connect()
      await manager.createRoom('test-room')

      await manager.startGame()

      expect(serverClientInstance.startGame).toHaveBeenCalled()
      expect(manager.getState()).toBe('starting')
    })

    it('should throw if not host', async () => {
      serverClientInstance.joinRoom.mockResolvedValue({
        id: 'existing-room',
        players: ['host', 'local-player'],
        host: 'host',
        status: 'waiting',
      })

      await manager.connect()
      await manager.joinRoom('existing-room')

      await expect(manager.startGame()).rejects.toThrow('Only the host can start the game')
    })

    it('should throw if not in lobby', async () => {
      await expect(manager.startGame()).rejects.toThrow('Cannot start game from state: disconnected')
    })

    it('should handle start error and transition to error state', async () => {
      await manager.connect()
      await manager.createRoom('test-room')
      serverClientInstance.startGame.mockRejectedValue(new Error('Not enough players'))

      const errorHandler = vi.fn()
      manager.onError(errorHandler)

      await expect(manager.startGame()).rejects.toThrow('Not enough players')
      // handleError sets state to 'error' after briefly being 'in_lobby'
      expect(manager.getState()).toBe('error')
      expect(errorHandler).toHaveBeenCalled()
    })
  })

  describe('game starting flow', () => {
    it('should setup P2P and netcode when game starts', async () => {
      await manager.connect()
      await manager.createRoom('test-room')
      await manager.startGame()

      // Simulate game_starting event from server
      const gameStartData: GameStartingData = {
        room: {
          id: 'test-room',
          players: ['local-player', 'peer-1'],
          host: 'local-player',
          status: 'starting',
        },
        player_order: { 'local-player': 0, 'peer-1': 1 },
        seed: 42,
        turn: {
          urls: ['turn:localhost:3478'],
          username: 'user',
          credential: 'cred',
          ttl: 3600,
        },
      }

      gameStartingHandler!(gameStartData)

      expect(manager.getState()).toBe('connecting_peers')
      expect(manager.getSeed()).toBe(42)
    })

    it('should handle game starting without TURN credentials', async () => {
      await manager.connect()
      await manager.createRoom('test-room')
      await manager.startGame()

      const gameStartData: GameStartingData = {
        room: {
          id: 'test-room',
          players: ['local-player'],
          host: 'local-player',
          status: 'starting',
        },
        player_order: { 'local-player': 0 },
        seed: 12345,
        turn: null,
      }

      gameStartingHandler!(gameStartData)

      // Should still work without TURN
      expect(manager.getSeed()).toBe(12345)
    })

    it('should transition to ready when all peers connect (single player)', async () => {
      const readyHandler = vi.fn()
      manager.onReady(readyHandler)

      await manager.connect()
      await manager.createRoom('test-room')
      await manager.startGame()

      // Single player game
      const gameStartData: GameStartingData = {
        room: {
          id: 'test-room',
          players: ['local-player'],
          host: 'local-player',
          status: 'starting',
        },
        player_order: { 'local-player': 0 },
        seed: 123,
        turn: null,
      }

      gameStartingHandler!(gameStartData)

      // Single player should immediately be ready
      expect(manager.getState()).toBe('ready')
      expect(readyHandler).toHaveBeenCalled()
    })

    it('should transition to ready when peer connects', async () => {
      const readyHandler = vi.fn()
      manager.onReady(readyHandler)

      await manager.connect()
      await manager.createRoom('test-room')
      await manager.startGame()

      const gameStartData: GameStartingData = {
        room: {
          id: 'test-room',
          players: ['local-player', 'peer-1'],
          host: 'local-player',
          status: 'starting',
        },
        player_order: { 'local-player': 0, 'peer-1': 1 },
        seed: 123,
        turn: null,
      }

      gameStartingHandler!(gameStartData)
      expect(manager.getState()).toBe('connecting_peers')

      // Simulate peer connection
      p2pConnectedHandler!('peer-1', {} as RTCDataChannel)

      expect(manager.getState()).toBe('ready')
      expect(readyHandler).toHaveBeenCalled()
    })

    it('should handle peer connection timeout', async () => {
      const timeoutConfig: MultiplayerConfig = {
        serverUrl: 'ws://localhost:4200/socket',
        peerConnectionTimeout: 1000,
      }

      // Reset handlers for new manager
      playerJoinedHandler = null
      playerLeftHandler = null
      gameStartingHandler = null
      p2pConnectedHandler = null
      p2pDisconnectedHandler = null

      manager = new MultiplayerManager(timeoutConfig)

      const errorHandler = vi.fn()
      manager.onError(errorHandler)

      await manager.connect()
      await manager.createRoom('test-room')
      await manager.startGame()

      const gameStartData: GameStartingData = {
        room: {
          id: 'test-room',
          players: ['local-player', 'peer-1'],
          host: 'local-player',
          status: 'starting',
        },
        player_order: { 'local-player': 0, 'peer-1': 1 },
        seed: 123,
        turn: null,
      }

      gameStartingHandler!(gameStartData)

      // Advance timers past timeout
      vi.advanceTimersByTime(1100)

      expect(manager.getState()).toBe('error')
      expect(errorHandler).toHaveBeenCalled()
    })
  })

  describe('player events', () => {
    it('should update player list on player joined', async () => {
      const lobbyHandler = vi.fn()
      manager.onLobbyUpdate(lobbyHandler)

      await manager.connect()
      await manager.createRoom('test-room')

      playerJoinedHandler!({ players: ['player-1', 'player-2'] })

      expect(manager.getLobbyState().currentRoom?.players).toEqual(['player-1', 'player-2'])
      expect(lobbyHandler).toHaveBeenCalled()
    })

    it('should update player list on player left', async () => {
      await manager.connect()
      await manager.createRoom('test-room')

      serverClientInstance.getCurrentRoom.mockReturnValue({ players: ['player-1'] })
      playerLeftHandler!({ player_id: 'player-2' })

      expect(manager.getLobbyState().currentRoom?.players).toEqual(['player-1'])
    })
  })

  describe('getters', () => {
    it('getState returns current state', () => {
      expect(manager.getState()).toBe('disconnected')
    })

    it('getLobbyState returns lobby state', () => {
      expect(manager.getLobbyState()).toEqual({ rooms: [], currentRoom: null })
    })

    it('isHost returns false when not in room', () => {
      expect(manager.isHost()).toBe(false)
    })

    it('getLocalPlayerId returns empty before connect', () => {
      expect(manager.getLocalPlayerId()).toBe('')
    })

    it('getLocalPlayerId returns player ID after connect', async () => {
      await manager.connect()
      expect(manager.getLocalPlayerId()).toBe('local-player')
    })

    it('getPlayerIds returns empty before game', () => {
      expect(manager.getPlayerIds()).toEqual([])
    })

    it('getPlayerOrder returns empty map before game', () => {
      expect(manager.getPlayerOrder()).toEqual(new Map())
    })

    it('getSeed returns default before game', () => {
      expect(manager.getSeed()).toBe(12345)
    })

    it('getNetcode returns null before game', () => {
      expect(manager.getNetcode()).toBeNull()
    })
  })

  describe('setPlaying', () => {
    it('should transition from ready to playing', async () => {
      await manager.connect()
      await manager.createRoom('test-room')
      await manager.startGame()

      const gameStartData: GameStartingData = {
        room: {
          id: 'test-room',
          players: ['local-player'],
          host: 'local-player',
          status: 'starting',
        },
        player_order: { 'local-player': 0 },
        seed: 123,
        turn: null,
      }

      gameStartingHandler!(gameStartData)
      expect(manager.getState()).toBe('ready')

      manager.setPlaying()
      expect(manager.getState()).toBe('playing')
    })

    it('should not change state if not ready', () => {
      manager.setPlaying()
      expect(manager.getState()).toBe('disconnected')
    })
  })

  describe('event handlers', () => {
    it('onStateChange returns unsubscribe function', () => {
      const handler = vi.fn()
      const unsubscribe = manager.onStateChange(handler)

      expect(typeof unsubscribe).toBe('function')
      unsubscribe()
    })

    it('onLobbyUpdate returns unsubscribe function', () => {
      const handler = vi.fn()
      const unsubscribe = manager.onLobbyUpdate(handler)

      expect(typeof unsubscribe).toBe('function')
    })

    it('onError returns unsubscribe function', () => {
      const handler = vi.fn()
      const unsubscribe = manager.onError(handler)

      expect(typeof unsubscribe).toBe('function')
    })

    it('onReady returns unsubscribe function', () => {
      const handler = vi.fn()
      const unsubscribe = manager.onReady(handler)

      expect(typeof unsubscribe).toBe('function')
    })

    it('unsubscribed handlers are not called', async () => {
      const handler = vi.fn()
      const unsubscribe = manager.onStateChange(handler)
      unsubscribe()

      await manager.connect()

      // Handler should not have been called after unsubscribe
      expect(handler).not.toHaveBeenCalled()
    })
  })

  describe('peer disconnection', () => {
    it('should remove peer from netcode on disconnect', async () => {
      await manager.connect()
      await manager.createRoom('test-room')
      await manager.startGame()

      const gameStartData: GameStartingData = {
        room: {
          id: 'test-room',
          players: ['local-player', 'peer-1'],
          host: 'local-player',
          status: 'starting',
        },
        player_order: { 'local-player': 0, 'peer-1': 1 },
        seed: 123,
        turn: null,
      }

      gameStartingHandler!(gameStartData)
      p2pConnectedHandler!('peer-1', {} as RTCDataChannel)

      // Now disconnect the peer
      p2pDisconnectedHandler!('peer-1')

      expect(lockstepNetcodeInstance.removePeer).toHaveBeenCalledWith('peer-1')
    })
  })

  describe('credential refresh', () => {
    it('should refresh credentials periodically during game', async () => {
      await manager.connect()
      await manager.createRoom('test-room')
      await manager.startGame()

      const gameStartData: GameStartingData = {
        room: {
          id: 'test-room',
          players: ['local-player'],
          host: 'local-player',
          status: 'starting',
        },
        player_order: { 'local-player': 0 },
        seed: 123,
        turn: { urls: ['turn:localhost'], username: 'u', credential: 'p', ttl: 3600 },
      }

      gameStartingHandler!(gameStartData)
      manager.setPlaying()

      // Advance to credential refresh interval (45 minutes)
      vi.advanceTimersByTime(45 * 60 * 1000)

      expect(serverClientInstance.refreshTurnCredentials).toHaveBeenCalled()
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
