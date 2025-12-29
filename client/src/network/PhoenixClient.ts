/**
 * Phoenix WebSocket client for lobby/rooms/signaling
 */

import { Socket, Channel } from 'phoenix'

export interface PhoenixConfig {
  url: string
  playerId?: string
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

export class PhoenixClient {
  private socket: Socket | null = null
  private roomChannel: Channel | null = null
  private signalingChannel: Channel | null = null

  private playerId: string = ''
  private roomId: string = ''

  private stateHandlers: Set<StateHandler> = new Set()
  private eventHandlers: Set<EventHandler> = new Set()

  private inputSequence = 0

  constructor(private config: PhoenixConfig) {}

  async connect(): Promise<string> {
    return new Promise((resolve, reject) => {
      this.playerId = this.config.playerId || this.generatePlayerId()

      this.socket = new Socket(this.config.url, {
        params: { player_id: this.playerId },
      })

      this.socket.onOpen(() => {
        console.log('Phoenix: Connected')
        resolve(this.playerId)
      })

      this.socket.onError((error: unknown) => {
        console.error('Phoenix: Connection error', error)
        reject(new Error('Failed to connect to server'))
      })

      this.socket.onClose(() => {
        console.log('Phoenix: Disconnected')
      })

      this.socket.connect()
    })
  }

  async joinRoom(roomId: string): Promise<RoomState> {
    if (!this.socket) {
      throw new Error('Not connected')
    }

    this.roomId = roomId

    return new Promise((resolve, reject) => {
      this.roomChannel = this.socket!.channel(`room:${roomId}`, {})

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

      this.roomChannel.on('player_joined', (payload: { player_id: string }) => {
        console.log('Player joined:', payload.player_id)
      })

      this.roomChannel.on('player_left', (payload: { player_id: string }) => {
        console.log('Player left:', payload.player_id)
      })

      this.roomChannel
        .join()
        .receive('ok', (response: { state: RoomState; player_id: string }) => {
          console.log('Joined room:', roomId)
          this.playerId = response.player_id
          resolve(response.state)
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

    this.roomChannel.push('input', {
      tick: this.inputSequence++,
      input,
    })
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

  // Event handlers

  onState(handler: StateHandler): () => void {
    this.stateHandlers.add(handler)
    return () => this.stateHandlers.delete(handler)
  }

  onEvent(handler: EventHandler): () => void {
    this.eventHandlers.add(handler)
    return () => this.eventHandlers.delete(handler)
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
