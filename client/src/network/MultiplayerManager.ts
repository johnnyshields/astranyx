/**
 * Multiplayer Manager
 *
 * Orchestrates the full multiplayer flow:
 * 1. Connect to Phoenix server
 * 2. Create/join/list rooms
 * 3. Coordinate WebRTC peer connections
 * 4. Set up LockstepNetcode when all peers connect
 */

import { PhoenixClient, type RoomInfo, type RoomData, type GameStartingData } from './PhoenixClient.ts'
import { P2PManager } from './P2PManager.ts'
import { LockstepNetcode } from './LockstepNetcode.ts'

export type MultiplayerState =
  | 'disconnected'
  | 'connecting'
  | 'connected'
  | 'joining_room'
  | 'in_lobby'
  | 'starting'
  | 'connecting_peers'
  | 'ready'
  | 'playing'
  | 'error'

export interface MultiplayerConfig {
  serverUrl: string
  peerConnectionTimeout?: number
}

const DEFAULT_PEER_CONNECTION_TIMEOUT = 30000 // 30 seconds

export interface LobbyState {
  rooms: RoomInfo[]
  currentRoom: {
    id: string
    players: string[]
    host: string
    isHost: boolean
    status: 'waiting' | 'starting' | 'playing'
  } | null
}

type StateChangeHandler = (state: MultiplayerState) => void
type LobbyUpdateHandler = (lobby: LobbyState) => void
type ErrorHandler = (error: Error) => void
type ReadyHandler = () => void

export class MultiplayerManager {
  private config: MultiplayerConfig
  private state: MultiplayerState = 'disconnected'

  private phoenix: PhoenixClient | null = null
  private p2p: P2PManager | null = null
  private netcode: LockstepNetcode | null = null

  private lobbyState: LobbyState = {
    rooms: [],
    currentRoom: null,
  }

  // Game start data (received from server)
  private gameStartData: GameStartingData | null = null

  // Event handlers
  private stateChangeHandlers: Set<StateChangeHandler> = new Set()
  private lobbyUpdateHandlers: Set<LobbyUpdateHandler> = new Set()
  private errorHandlers: Set<ErrorHandler> = new Set()
  private readyHandlers: Set<ReadyHandler> = new Set()

  // Peer connection tracking
  private expectedPlayers: string[] = []
  private connectedPeers: Set<string> = new Set()
  private peerConnectionTimeoutId: ReturnType<typeof setTimeout> | null = null

  constructor(config: MultiplayerConfig) {
    this.config = config
  }

  // ==========================================================================
  // Connection
  // ==========================================================================

  async connect(): Promise<void> {
    if (this.state !== 'disconnected') {
      throw new Error(`Cannot connect from state: ${this.state}`)
    }

    this.setState('connecting')

    try {
      this.phoenix = new PhoenixClient({ url: this.config.serverUrl })
      await this.phoenix.connect()

      this.setupPhoenixHandlers()
      this.setState('connected')
    } catch (error) {
      this.handleError(error as Error)
      throw error
    }
  }

  disconnect(): void {
    this.cleanup()
    this.setState('disconnected')
  }

  private setupPhoenixHandlers(): void {
    if (!this.phoenix) return

    this.phoenix.onPlayerJoined((payload) => {
      if (this.lobbyState.currentRoom) {
        this.lobbyState.currentRoom.players = payload.players
        this.notifyLobbyUpdate()
      }
    })

    this.phoenix.onPlayerLeft((_payload) => {
      // PhoenixClient already filters currentRoom.players
      // Sync our lobby state from PhoenixClient's state
      if (this.lobbyState.currentRoom) {
        const phoenixRoom = this.phoenix?.getCurrentRoom()
        if (phoenixRoom) {
          this.lobbyState.currentRoom.players = phoenixRoom.players
        }
        this.notifyLobbyUpdate()
      }
    })

    this.phoenix.onGameStarting((data) => {
      this.handleGameStarting(data)
    })
  }

  // ==========================================================================
  // Room Management
  // ==========================================================================

  async listRooms(): Promise<RoomInfo[]> {
    if (!this.phoenix || this.state === 'disconnected') {
      throw new Error('Not connected')
    }

    try {
      const rooms = await this.phoenix.listRooms()
      this.lobbyState.rooms = rooms
      this.notifyLobbyUpdate()
      return rooms
    } catch (error) {
      console.error('Failed to list rooms:', error)
      return []
    }
  }

  async createRoom(roomId: string): Promise<void> {
    if (!this.phoenix || this.state !== 'connected') {
      throw new Error(`Cannot create room from state: ${this.state}`)
    }

    this.setState('joining_room')

    try {
      const room = await this.phoenix.joinRoom(roomId, true)
      await this.phoenix.joinSignaling(roomId)

      this.lobbyState.currentRoom = {
        id: room.id,
        players: room.players,
        host: room.host,
        isHost: true,
        status: room.status,
      }

      this.setState('in_lobby')
      this.notifyLobbyUpdate()
    } catch (error) {
      this.setState('connected')
      this.handleError(error as Error)
      throw error
    }
  }

  async joinRoom(roomId: string): Promise<void> {
    if (!this.phoenix || this.state !== 'connected') {
      throw new Error(`Cannot join room from state: ${this.state}`)
    }

    this.setState('joining_room')

    try {
      const room = await this.phoenix.joinRoom(roomId, false)
      await this.phoenix.joinSignaling(roomId)

      this.lobbyState.currentRoom = {
        id: room.id,
        players: room.players,
        host: room.host,
        isHost: room.host === this.phoenix.getPlayerId(),
        status: room.status,
      }

      this.setState('in_lobby')
      this.notifyLobbyUpdate()
    } catch (error) {
      this.setState('connected')
      this.handleError(error as Error)
      throw error
    }
  }

  async quickmatch(): Promise<void> {
    if (!this.phoenix || this.state !== 'connected') {
      throw new Error(`Cannot quickmatch from state: ${this.state}`)
    }

    // First, we need to temporarily join a "lobby" room to query available rooms
    // This is a bit of a workaround for the Phoenix channel architecture
    // For quickmatch, we'll generate a random room name and try to find existing rooms

    // Generate a random room name
    const randomRoomId = `game-${Math.random().toString(36).slice(2, 8)}`

    // For now, just create a new room
    // In a more sophisticated implementation, we'd query the server for available rooms first
    // via a dedicated endpoint or lobby channel
    await this.createRoom(randomRoomId)
  }

  leaveRoom(): void {
    if (!this.phoenix) return

    this.phoenix.leaveRoom()
    this.lobbyState.currentRoom = null

    if (this.p2p) {
      this.p2p.disconnect()
      this.p2p = null
    }

    this.netcode = null
    this.gameStartData = null
    this.expectedPlayers = []
    this.connectedPeers.clear()

    this.setState('connected')
    this.notifyLobbyUpdate()
  }

  // ==========================================================================
  // Game Start
  // ==========================================================================

  async startGame(): Promise<void> {
    if (!this.phoenix || this.state !== 'in_lobby') {
      throw new Error(`Cannot start game from state: ${this.state}`)
    }

    if (!this.lobbyState.currentRoom?.isHost) {
      throw new Error('Only the host can start the game')
    }

    this.setState('starting')

    try {
      await this.phoenix.startGame()
      // The actual game start is handled via the game_starting event
    } catch (error) {
      this.setState('in_lobby')
      this.handleError(error as Error)
      throw error
    }
  }

  private handleGameStarting(data: GameStartingData): void {
    console.log('Game starting with data:', data)

    this.gameStartData = data
    this.expectedPlayers = data.room.players
    this.connectedPeers.clear()

    // Create P2P manager
    const localPlayerId = this.phoenix!.getPlayerId()
    this.p2p = new P2PManager(localPlayerId)

    // Set up signaling channel
    const signalingChannel = this.phoenix!.getSignalingChannel()
    if (signalingChannel) {
      this.p2p.setSignalingChannel(signalingChannel)
    }

    // Create LockstepNetcode
    const playerOrder = new Map<string, number>()
    for (const [playerId, index] of Object.entries(data.player_order)) {
      playerOrder.set(playerId, index as number)
    }

    this.netcode = new LockstepNetcode({
      inputDelay: 3,
      maxRollbackFrames: 0,
      playerCount: this.expectedPlayers.length,
      localPlayerId: localPlayerId,
      playerOrder: playerOrder,
    })

    // Set up P2P connection handlers
    this.p2p.onConnected((playerId, channel) => {
      console.log(`Peer connected: ${playerId}`)
      this.connectedPeers.add(playerId)
      this.netcode!.addPeer(playerId, channel)
      this.checkAllPeersConnected()
    })

    this.p2p.onDisconnected((playerId) => {
      console.log(`Peer disconnected: ${playerId}`)
      this.connectedPeers.delete(playerId)
      this.netcode?.removePeer(playerId)
    })

    this.setState('connecting_peers')

    // Initiate connections to other players
    const otherPlayers = this.expectedPlayers.filter(p => p !== localPlayerId)
    this.p2p.connectToPlayers(otherPlayers)

    // Set up peer connection timeout
    if (otherPlayers.length > 0) {
      const timeout = this.config.peerConnectionTimeout ?? DEFAULT_PEER_CONNECTION_TIMEOUT
      this.peerConnectionTimeoutId = setTimeout(() => {
        if (this.state === 'connecting_peers') {
          const missing = otherPlayers.filter(p => !this.connectedPeers.has(p))
          console.error('Peer connection timeout. Missing peers:', missing)
          this.handleError(new Error(`Failed to connect to peers: ${missing.join(', ')}`))
        }
      }, timeout)
    }

    // Check if we're the only player (single player via multiplayer)
    this.checkAllPeersConnected()
  }

  private checkAllPeersConnected(): void {
    const localPlayerId = this.phoenix?.getPlayerId()
    const otherPlayers = this.expectedPlayers.filter(p => p !== localPlayerId)

    // Check if we have all peer connections
    if (this.connectedPeers.size >= otherPlayers.length) {
      console.log('All peers connected!')

      // Clear the timeout since we connected successfully
      this.clearPeerConnectionTimeout()

      this.setState('ready')

      // Notify that we're ready to start
      for (const handler of this.readyHandlers) {
        handler()
      }
    }
  }

  private clearPeerConnectionTimeout(): void {
    if (this.peerConnectionTimeoutId) {
      clearTimeout(this.peerConnectionTimeoutId)
      this.peerConnectionTimeoutId = null
    }
  }

  // ==========================================================================
  // Getters for Game
  // ==========================================================================

  getNetcode(): LockstepNetcode | null {
    return this.netcode
  }

  getLocalPlayerId(): string {
    return this.phoenix?.getPlayerId() ?? ''
  }

  getPlayerIds(): string[] {
    return this.expectedPlayers
  }

  getPlayerOrder(): Map<string, number> {
    if (!this.gameStartData) return new Map()

    const order = new Map<string, number>()
    for (const [playerId, index] of Object.entries(this.gameStartData.player_order)) {
      order.set(playerId, index as number)
    }
    return order
  }

  getSeed(): number {
    return this.gameStartData?.seed ?? 12345
  }

  // ==========================================================================
  // State Management
  // ==========================================================================

  getState(): MultiplayerState {
    return this.state
  }

  getLobbyState(): LobbyState {
    return this.lobbyState
  }

  isHost(): boolean {
    return this.lobbyState.currentRoom?.isHost ?? false
  }

  private setState(newState: MultiplayerState): void {
    if (this.state === newState) return

    console.log(`MultiplayerManager: ${this.state} → ${newState}`)
    this.state = newState

    for (const handler of this.stateChangeHandlers) {
      handler(newState)
    }
  }

  private notifyLobbyUpdate(): void {
    for (const handler of this.lobbyUpdateHandlers) {
      handler(this.lobbyState)
    }
  }

  private handleError(error: Error): void {
    console.error('MultiplayerManager error:', error)
    this.setState('error')

    for (const handler of this.errorHandlers) {
      handler(error)
    }
  }

  // ==========================================================================
  // Event Handlers
  // ==========================================================================

  onStateChange(handler: StateChangeHandler): () => void {
    this.stateChangeHandlers.add(handler)
    return () => this.stateChangeHandlers.delete(handler)
  }

  onLobbyUpdate(handler: LobbyUpdateHandler): () => void {
    this.lobbyUpdateHandlers.add(handler)
    return () => this.lobbyUpdateHandlers.delete(handler)
  }

  onError(handler: ErrorHandler): () => void {
    this.errorHandlers.add(handler)
    return () => this.errorHandlers.delete(handler)
  }

  onReady(handler: ReadyHandler): () => void {
    this.readyHandlers.add(handler)
    return () => this.readyHandlers.delete(handler)
  }

  // ==========================================================================
  // Cleanup
  // ==========================================================================

  private cleanup(): void {
    this.clearPeerConnectionTimeout()

    this.p2p?.disconnect()
    this.p2p = null

    this.netcode?.stop()
    this.netcode = null

    this.phoenix?.disconnect()
    this.phoenix = null

    this.lobbyState = {
      rooms: [],
      currentRoom: null,
    }

    this.gameStartData = null
    this.expectedPlayers = []
    this.connectedPeers.clear()

    // Clear all event handlers to prevent memory leaks
    this.stateChangeHandlers.clear()
    this.lobbyUpdateHandlers.clear()
    this.errorHandlers.clear()
    this.readyHandlers.clear()
  }

  /**
   * Mark the game as playing (called by Game after startMultiplayer)
   */
  setPlaying(): void {
    if (this.state === 'ready') {
      this.setState('playing')
    }
  }
}
