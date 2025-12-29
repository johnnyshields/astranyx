/**
 * WebRTC client for game networking
 *
 * Architecture:
 * 1. Phoenix WebSocket for signaling (SDP exchange, ICE candidates)
 * 2. WebRTC DataChannel for game traffic (low latency, unreliable mode)
 *
 * Flow:
 * - Client connects to Phoenix signaling server
 * - Server assigns to game room
 * - Clients exchange SDP offers/answers via Phoenix
 * - Once connected, game data flows over DataChannel
 */

export interface GameMessage {
  type: 'input' | 'state' | 'event' | 'ping' | 'pong'
  seq: number
  timestamp: number
  data: unknown
}

export interface NetworkConfig {
  signalingUrl: string
  iceServers?: RTCIceServer[]
}

type ConnectionState = 'disconnected' | 'connecting' | 'signaling' | 'connected'
type MessageHandler = (message: GameMessage) => void

export class WebRTCClient {
  private config: NetworkConfig
  private state: ConnectionState = 'disconnected'

  // Signaling (Phoenix WebSocket)
  private signaling: WebSocket | null = null

  // WebRTC
  private peerConnection: RTCPeerConnection | null = null
  private dataChannel: RTCDataChannel | null = null

  // Message handling
  private messageHandlers: Set<MessageHandler> = new Set()
  private sequenceNumber = 0

  // Latency tracking
  private lastPingTime = 0
  private latency = 0

  constructor(config: NetworkConfig) {
    this.config = {
      signalingUrl: config.signalingUrl,
      iceServers: config.iceServers ?? [
        { urls: 'stun:stun.l.google.com:19302' },
        { urls: 'stun:stun1.l.google.com:19302' },
      ],
    }
  }

  async connect(roomId: string, playerId: string): Promise<void> {
    if (this.state !== 'disconnected') {
      throw new Error(`Cannot connect: current state is ${this.state}`)
    }

    this.state = 'connecting'

    try {
      // 1. Connect to signaling server
      await this.connectSignaling(roomId, playerId)

      // 2. Create peer connection
      this.createPeerConnection()

      // 3. Create data channel (as initiator)
      this.createDataChannel()

      // 4. Create and send offer
      await this.createAndSendOffer()

      console.log('WebRTC: Waiting for connection...')
    } catch (error) {
      this.state = 'disconnected'
      throw error
    }
  }

  private connectSignaling(roomId: string, playerId: string): Promise<void> {
    return new Promise((resolve, reject) => {
      const url = `${this.config.signalingUrl}?room=${roomId}&player=${playerId}`
      this.signaling = new WebSocket(url)

      this.signaling.onopen = () => {
        console.log('Signaling: Connected')
        this.state = 'signaling'
        resolve()
      }

      this.signaling.onerror = (error) => {
        console.error('Signaling: Error', error)
        reject(new Error('Signaling connection failed'))
      }

      this.signaling.onclose = () => {
        console.log('Signaling: Disconnected')
      }

      this.signaling.onmessage = (event) => {
        this.handleSignalingMessage(JSON.parse(event.data as string))
      }
    })
  }

  private createPeerConnection(): void {
    this.peerConnection = new RTCPeerConnection({
      iceServers: this.config.iceServers,
    })

    this.peerConnection.onicecandidate = (event) => {
      if (event.candidate) {
        this.sendSignaling({
          type: 'ice_candidate',
          candidate: event.candidate,
        })
      }
    }

    this.peerConnection.onconnectionstatechange = () => {
      const state = this.peerConnection?.connectionState
      console.log('WebRTC: Connection state:', state)

      if (state === 'connected') {
        this.state = 'connected'
        this.startPingLoop()
      } else if (state === 'disconnected' || state === 'failed') {
        this.handleDisconnect()
      }
    }

    this.peerConnection.ondatachannel = (event) => {
      // Handle incoming data channel (when we're the answerer)
      this.setupDataChannel(event.channel)
    }
  }

  private createDataChannel(): void {
    if (!this.peerConnection) return

    // Create unreliable channel for game data (like UDP)
    const channel = this.peerConnection.createDataChannel('game', {
      ordered: false,
      maxRetransmits: 0,
    })

    this.setupDataChannel(channel)
  }

  private setupDataChannel(channel: RTCDataChannel): void {
    this.dataChannel = channel

    channel.binaryType = 'arraybuffer'

    channel.onopen = () => {
      console.log('DataChannel: Open')
    }

    channel.onclose = () => {
      console.log('DataChannel: Closed')
    }

    channel.onmessage = (event) => {
      const message = this.decodeMessage(event.data as ArrayBuffer)
      if (message) {
        this.handleGameMessage(message)
      }
    }
  }

  private async createAndSendOffer(): Promise<void> {
    if (!this.peerConnection) return

    const offer = await this.peerConnection.createOffer()
    await this.peerConnection.setLocalDescription(offer)

    this.sendSignaling({
      type: 'offer',
      sdp: offer,
    })
  }

  private async handleSignalingMessage(message: {
    type: string
    sdp?: RTCSessionDescriptionInit
    candidate?: RTCIceCandidateInit
  }): Promise<void> {
    if (!this.peerConnection) return

    switch (message.type) {
      case 'offer':
        await this.peerConnection.setRemoteDescription(
          new RTCSessionDescription(message.sdp!)
        )
        const answer = await this.peerConnection.createAnswer()
        await this.peerConnection.setLocalDescription(answer)
        this.sendSignaling({ type: 'answer', sdp: answer })
        break

      case 'answer':
        await this.peerConnection.setRemoteDescription(
          new RTCSessionDescription(message.sdp!)
        )
        break

      case 'ice_candidate':
        await this.peerConnection.addIceCandidate(
          new RTCIceCandidate(message.candidate!)
        )
        break
    }
  }

  private sendSignaling(message: object): void {
    if (this.signaling?.readyState === WebSocket.OPEN) {
      this.signaling.send(JSON.stringify(message))
    }
  }

  // Game message encoding/decoding (binary format for efficiency)
  private encodeMessage(message: GameMessage): ArrayBuffer {
    // Simple encoding: JSON for now, can optimize to binary later
    const json = JSON.stringify(message)
    const encoder = new TextEncoder()
    return encoder.encode(json).buffer as ArrayBuffer
  }

  private decodeMessage(data: ArrayBuffer): GameMessage | null {
    try {
      const decoder = new TextDecoder()
      const json = decoder.decode(data)
      return JSON.parse(json) as GameMessage
    } catch {
      console.error('Failed to decode message')
      return null
    }
  }

  private handleGameMessage(message: GameMessage): void {
    if (message.type === 'pong') {
      this.latency = performance.now() - this.lastPingTime
      return
    }

    for (const handler of this.messageHandlers) {
      handler(message)
    }
  }

  // Public API

  send(type: GameMessage['type'], data: unknown): void {
    if (!this.dataChannel || this.dataChannel.readyState !== 'open') {
      return
    }

    const message: GameMessage = {
      type,
      seq: this.sequenceNumber++,
      timestamp: performance.now(),
      data,
    }

    this.dataChannel.send(this.encodeMessage(message))
  }

  onMessage(handler: MessageHandler): () => void {
    this.messageHandlers.add(handler)
    return () => this.messageHandlers.delete(handler)
  }

  getLatency(): number {
    return this.latency
  }

  getState(): ConnectionState {
    return this.state
  }

  isConnected(): boolean {
    return this.state === 'connected'
  }

  private startPingLoop(): void {
    setInterval(() => {
      if (this.isConnected()) {
        this.lastPingTime = performance.now()
        this.send('ping', null)
      }
    }, 1000)
  }

  private handleDisconnect(): void {
    this.state = 'disconnected'
    this.cleanup()
    // TODO: Implement reconnection logic
  }

  disconnect(): void {
    this.cleanup()
    this.state = 'disconnected'
  }

  private cleanup(): void {
    this.dataChannel?.close()
    this.dataChannel = null

    this.peerConnection?.close()
    this.peerConnection = null

    this.signaling?.close()
    this.signaling = null
  }
}
