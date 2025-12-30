/**
 * Phoenix WebSocket client for lobby/rooms/signaling
 */

import { Socket, Channel } from 'phoenix'

export interface PhoenixConfig {
  url: string
  playerId?: string
  connectionTimeout?: number
}

const DEFAULT_CONNECTION_TIMEOUT = 10000 // 10 seconds

export interface RoomInfo {
  id: string
  host: string
  player_count: number
  max_players: number
  status: 'waiting' | 'starting' | 'playing'
}

export interface RoomData {
  id: string
  host: string
  players: string[]
  status: 'waiting' | 'starting' | 'playing'
}

export interface GameStartingData {
  room: RoomData
  player_order: Record<string, number>
  seed: number
}

export interface RoomState {
  tick: number
  timestamp: number
  entities: EntityState[]
  events: GameEvent[]
}

export interface EntityState {
  id: string
  type: 'player' | 'enemy' | 'bullet' | 'powerup'
  x: number
  y: number
  vx: number
  vy: number
  rotation: number
  health?: number
  player_id?: string
}

export interface GameEvent {
  type: string
  entity_id: string
  data?: unknown
}

export interface PlayerInput {
  up: boolean
  down: boolean
  left: boolean
  right: boolean
  fire: boolean
  special: boolean
}

type StateHandler = (state: RoomState) => void
type EventHandler = (event: GameEvent) => void
type PlayerJoinedHandler = (payload: { player_id: string; players: string[] }) => void
type PlayerLeftHandler = (payload: { player_id: string }) => void
type GameStartingHandler = (data: GameStartingData) => void

export class PhoenixClient {
  private socket: Socket | null = null
  private lobbyChannel: Channel | null = null
  private roomChannel: Channel | null = null
  private signalingChannel: Channel | null = null

  private playerId: string = ''
  private roomId: string = ''

  private stateHandlers: Set<StateHandler> = new Set()
  private eventHandlers: Set<EventHandler> = new Set()
  private playerJoinedHandlers: Set<PlayerJoinedHandler> = new Set()
  private playerLeftHandlers: Set<PlayerLeftHandler> = new Set()
  private gameStartingHandlers: Set<GameStartingHandler> = new Set()

  private currentRoom: RoomData | null = null

  constructor(private config: PhoenixConfig) {}

  async connect(): Promise<string> {
    return new Promise((resolve, reject) => {
      this.playerId = this.config.playerId || this.generatePlayerId()

      const timeout = this.config.connectionTimeout ?? DEFAULT_CONNECTION_TIMEOUT
      let timeoutId: ReturnType<typeof setTimeout> | null = null
      let settled = false

      const cleanup = () => {
        if (timeoutId) {
          clearTimeout(timeoutId)
          timeoutId = null
        }
      }

      // Set connection timeout
      timeoutId = setTimeout(() => {
        if (!settled) {
          settled = true
          this.socket?.disconnect()
          this.socket = null
          reject(new Error('Connection timeout - server unreachable'))
        }
      }, timeout)

      this.socket = new Socket(this.config.url, {
        params: { player_id: this.playerId },
      })

      this.socket.onOpen(async () => {
        if (!settled) {
          settled = true
          cleanup()
          console.log('Phoenix: Connected')

          // Auto-join lobby channel for room listing
          try {
            await this.joinLobby()
          } catch (e) {
            console.warn('Failed to join lobby channel:', e)
          }

          resolve(this.playerId)
        }
      })

      this.socket.onError((error: unknown) => {
        if (!settled) {
          settled = true
          cleanup()
          console.error('Phoenix: Connection error', error)
          reject(new Error('Failed to connect to server'))
        }
      })

      this.socket.onClose(() => {
        console.log('Phoenix: Disconnected')
      })

      this.socket.connect()
    })
  }

  private async joinLobby(): Promise<void> {
    if (!this.socket) {
      throw new Error('Not connected')
    }

    return new Promise((resolve, reject) => {
      this.lobbyChannel = this.socket!.channel('lobby:main', {})

      this.lobbyChannel
        .join()
        .receive('ok', () => {
          console.log('Joined lobby channel')
          resolve()
        })
        .receive('error', (error: { reason: string }) => {
          reject(new Error(error.reason))
        })
    })
  }

  async joinRoom(roomId: string, asHost = false): Promise<RoomData> {
    if (!this.socket) {
      throw new Error('Not connected')
    }

    this.roomId = roomId

    return new Promise((resolve, reject) => {
      this.roomChannel = this.socket!.channel(`room:${roomId}`, { host: asHost })

      this.roomChannel.on('state', (state: RoomState) => {
        for (const handler of this.stateHandlers) {
          handler(state)
        }
      })

      this.roomChannel.on('event', (event: GameEvent) => {
        for (const handler of this.eventHandlers) {
          handler(event)
        }
      })

      this.roomChannel.on('player_joined', (payload: { player_id: string; players: string[] }) => {
        console.log('Player joined:', payload.player_id)
        if (this.currentRoom) {
          this.currentRoom.players = payload.players
        }
        for (const handler of this.playerJoinedHandlers) {
          handler(payload)
        }
      })

      this.roomChannel.on('player_left', (payload: { player_id: string }) => {
        console.log('Player left:', payload.player_id)
        if (this.currentRoom) {
          this.currentRoom.players = this.currentRoom.players.filter(p => p !== payload.player_id)
        }
        for (const handler of this.playerLeftHandlers) {
          handler(payload)
        }
      })

      this.roomChannel.on('game_starting', (data: GameStartingData) => {
        console.log('Game starting:', data)
        for (const handler of this.gameStartingHandlers) {
          handler(data)
        }
      })

      this.roomChannel
        .join()
        .receive('ok', (response: { room: RoomData; player_id: string }) => {
          console.log('Joined room:', roomId)
          this.playerId = response.player_id
          this.currentRoom = response.room
          resolve(response.room)
        })
        .receive('error', (error: { reason: string }) => {
          console.error('Failed to join room:', error)
          reject(new Error(error.reason))
        })
    })
  }

  async joinSignaling(roomId: string): Promise<void> {
    if (!this.socket) {
      throw new Error('Not connected')
    }

    return new Promise((resolve, reject) => {
      this.signalingChannel = this.socket!.channel(`signaling:${roomId}`, {})

      this.signalingChannel
        .join()
        .receive('ok', () => {
          console.log('Joined signaling channel:', roomId)
          resolve()
        })
        .receive('error', (error: { reason: string }) => {
          reject(new Error(error.reason))
        })
    })
  }

  sendInput(input: PlayerInput): void {
    if (!this.roomChannel) return

    this.roomChannel.push('input', { input })
  }

  async ping(): Promise<number> {
    if (!this.roomChannel) return 0

    const start = performance.now()

    return new Promise((resolve) => {
      this.roomChannel!.push('ping', {})
        .receive('ok', () => {
          resolve(performance.now() - start)
        })
        .receive('error', () => {
          resolve(0)
        })
    })
  }

  // Signaling methods for WebRTC

  sendOffer(sdp: RTCSessionDescriptionInit, targetPlayerId: string): void {
    this.signalingChannel?.push('offer', {
      sdp,
      to: targetPlayerId,
    })
  }

  sendAnswer(sdp: RTCSessionDescriptionInit, targetPlayerId: string): void {
    this.signalingChannel?.push('answer', {
      sdp,
      to: targetPlayerId,
    })
  }

  sendIceCandidate(candidate: RTCIceCandidateInit, targetPlayerId: string): void {
    this.signalingChannel?.push('ice_candidate', {
      candidate,
      to: targetPlayerId,
    })
  }

  onSignalingMessage(
    type: 'offer' | 'answer' | 'ice_candidate' | 'peer_joined' | 'peer_left',
    handler: (payload: unknown) => void
  ): void {
    this.signalingChannel?.on(type, handler)
  }

  // Room management

  async listRooms(): Promise<RoomInfo[]> {
    if (!this.lobbyChannel) {
      throw new Error('Not connected to lobby')
    }

    return new Promise((resolve, reject) => {
      this.lobbyChannel!.push('list_rooms', {})
        .receive('ok', (response: { rooms: RoomInfo[] }) => {
          resolve(response.rooms)
        })
        .receive('error', (error: { reason: string }) => {
          reject(new Error(error.reason))
        })
    })
  }

  async startGame(): Promise<void> {
    if (!this.roomChannel) {
      throw new Error('Not in a room')
    }

    return new Promise((resolve, reject) => {
      this.roomChannel!.push('start_game', {})
        .receive('ok', () => resolve())
        .receive('error', (error: { reason: string }) => {
          reject(new Error(error.reason))
        })
    })
  }

  getCurrentRoom(): RoomData | null {
    return this.currentRoom
  }

  getSignalingChannel(): Channel | null {
    return this.signalingChannel
  }

  // Event handlers

  onState(handler: StateHandler): () => void {
    this.stateHandlers.add(handler)
    return () => this.stateHandlers.delete(handler)
  }

  onEvent(handler: EventHandler): () => void {
    this.eventHandlers.add(handler)
    return () => this.eventHandlers.delete(handler)
  }

  onPlayerJoined(handler: PlayerJoinedHandler): () => void {
    this.playerJoinedHandlers.add(handler)
    return () => this.playerJoinedHandlers.delete(handler)
  }

  onPlayerLeft(handler: PlayerLeftHandler): () => void {
    this.playerLeftHandlers.add(handler)
    return () => this.playerLeftHandlers.delete(handler)
  }

  onGameStarting(handler: GameStartingHandler): () => void {
    this.gameStartingHandlers.add(handler)
    return () => this.gameStartingHandlers.delete(handler)
  }

  // Getters

  getPlayerId(): string {
    return this.playerId
  }

  getRoomId(): string {
    return this.roomId
  }

  isConnected(): boolean {
    return this.socket?.isConnected() ?? false
  }

  // Cleanup

  leaveRoom(): void {
    this.roomChannel?.leave()
    this.roomChannel = null
    this.signalingChannel?.leave()
    this.signalingChannel = null
    this.currentRoom = null
    this.roomId = ''
  }

  disconnect(): void {
    this.leaveRoom()
    this.socket?.disconnect()
    this.socket = null
  }

  private generatePlayerId(): string {
    return `player_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`
  }
}
