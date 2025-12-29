/**
 * P2P Connection Manager
 *
 * Handles WebRTC peer connections between players.
 * Uses Phoenix signaling channel to exchange SDP/ICE.
 */

import type { Channel } from 'phoenix'

export interface PeerConnection {
  playerId: string
  connection: RTCPeerConnection
  dataChannel: RTCDataChannel | null
  state: 'connecting' | 'connected' | 'disconnected'
}

interface SignalingMessage {
  type: 'offer' | 'answer' | 'ice_candidate'
  from: string
  to: string
  sdp?: RTCSessionDescriptionInit
  candidate?: RTCIceCandidateInit
}

type ConnectionHandler = (playerId: string, channel: RTCDataChannel) => void
type DisconnectHandler = (playerId: string) => void

export class P2PManager {
  private localPlayerId: string
  private signalingChannel: Channel | null = null
  private peers: Map<string, PeerConnection> = new Map()

  private onPeerConnected: ConnectionHandler | null = null
  private onPeerDisconnected: DisconnectHandler | null = null

  private readonly iceServers: RTCIceServer[] = [
    { urls: 'stun:stun.l.google.com:19302' },
    { urls: 'stun:stun1.l.google.com:19302' },
  ]

  constructor(localPlayerId: string) {
    this.localPlayerId = localPlayerId
  }

  /**
   * Set up signaling via Phoenix channel
   */
  setSignalingChannel(channel: Channel): void {
    this.signalingChannel = channel

    channel.on('offer', (msg: SignalingMessage) => {
      if (msg.to === this.localPlayerId) {
        this.handleOffer(msg.from, msg.sdp!)
      }
    })

    channel.on('answer', (msg: SignalingMessage) => {
      if (msg.to === this.localPlayerId) {
        this.handleAnswer(msg.from, msg.sdp!)
      }
    })

    channel.on('ice_candidate', (msg: SignalingMessage) => {
      if (msg.to === this.localPlayerId) {
        this.handleIceCandidate(msg.from, msg.candidate!)
      }
    })

    channel.on('peer_joined', (payload: { player_id: string }) => {
      // New peer joined, initiate connection if we have higher ID
      if (this.shouldInitiate(payload.player_id)) {
        this.connectToPeer(payload.player_id)
      }
    })

    channel.on('peer_left', (payload: { player_id: string }) => {
      this.disconnectPeer(payload.player_id)
    })
  }

  /**
   * Initiate connections to a list of players
   */
  async connectToPlayers(playerIds: string[]): Promise<void> {
    for (const playerId of playerIds) {
      if (playerId !== this.localPlayerId && this.shouldInitiate(playerId)) {
        await this.connectToPeer(playerId)
      }
    }
  }

  /**
   * Determine if we should initiate the connection
   * Use lexicographic comparison for determinism
   */
  private shouldInitiate(otherPlayerId: string): boolean {
    return this.localPlayerId > otherPlayerId
  }

  /**
   * Create peer connection and initiate handshake
   */
  private async connectToPeer(playerId: string): Promise<void> {
    if (this.peers.has(playerId)) return

    console.log(`P2P: Connecting to ${playerId}`)

    const connection = this.createPeerConnection(playerId)
    const dataChannel = connection.createDataChannel('game', {
      ordered: false,
      maxRetransmits: 0,
    })

    this.setupDataChannel(playerId, dataChannel)

    const peer: PeerConnection = {
      playerId,
      connection,
      dataChannel,
      state: 'connecting',
    }
    this.peers.set(playerId, peer)

    // Create and send offer
    const offer = await connection.createOffer()
    await connection.setLocalDescription(offer)

    this.sendSignaling('offer', playerId, { sdp: offer })
  }

  private createPeerConnection(playerId: string): RTCPeerConnection {
    const connection = new RTCPeerConnection({
      iceServers: this.iceServers,
    })

    connection.onicecandidate = (event) => {
      if (event.candidate) {
        this.sendSignaling('ice_candidate', playerId, {
          candidate: event.candidate,
        })
      }
    }

    connection.onconnectionstatechange = () => {
      const state = connection.connectionState
      console.log(`P2P: Connection to ${playerId} is ${state}`)

      if (state === 'disconnected' || state === 'failed') {
        this.disconnectPeer(playerId)
      }
    }

    connection.ondatachannel = (event) => {
      // Handle incoming data channel (when we're the answerer)
      this.setupDataChannel(playerId, event.channel)

      const peer = this.peers.get(playerId)
      if (peer) {
        peer.dataChannel = event.channel
      }
    }

    return connection
  }

  private setupDataChannel(playerId: string, channel: RTCDataChannel): void {
    channel.binaryType = 'arraybuffer'

    channel.onopen = () => {
      console.log(`P2P: DataChannel to ${playerId} open`)

      const peer = this.peers.get(playerId)
      if (peer) {
        peer.state = 'connected'
        this.onPeerConnected?.(playerId, channel)
      }
    }

    channel.onclose = () => {
      console.log(`P2P: DataChannel to ${playerId} closed`)
      this.disconnectPeer(playerId)
    }

    channel.onerror = (error) => {
      console.error(`P2P: DataChannel error with ${playerId}`, error)
    }
  }

  private async handleOffer(
    fromPlayerId: string,
    sdp: RTCSessionDescriptionInit
  ): Promise<void> {
    console.log(`P2P: Received offer from ${fromPlayerId}`)

    let peer = this.peers.get(fromPlayerId)

    if (!peer) {
      const connection = this.createPeerConnection(fromPlayerId)
      peer = {
        playerId: fromPlayerId,
        connection,
        dataChannel: null,
        state: 'connecting',
      }
      this.peers.set(fromPlayerId, peer)
    }

    await peer.connection.setRemoteDescription(new RTCSessionDescription(sdp))
    const answer = await peer.connection.createAnswer()
    await peer.connection.setLocalDescription(answer)

    this.sendSignaling('answer', fromPlayerId, { sdp: answer })
  }

  private async handleAnswer(
    fromPlayerId: string,
    sdp: RTCSessionDescriptionInit
  ): Promise<void> {
    console.log(`P2P: Received answer from ${fromPlayerId}`)

    const peer = this.peers.get(fromPlayerId)
    if (peer) {
      await peer.connection.setRemoteDescription(new RTCSessionDescription(sdp))
    }
  }

  private async handleIceCandidate(
    fromPlayerId: string,
    candidate: RTCIceCandidateInit
  ): Promise<void> {
    const peer = this.peers.get(fromPlayerId)
    if (peer) {
      await peer.connection.addIceCandidate(new RTCIceCandidate(candidate))
    }
  }

  private sendSignaling(
    type: 'offer' | 'answer' | 'ice_candidate',
    toPlayerId: string,
    data: { sdp?: RTCSessionDescriptionInit; candidate?: RTCIceCandidateInit }
  ): void {
    this.signalingChannel?.push(type, {
      to: toPlayerId,
      ...data,
    })
  }

  private disconnectPeer(playerId: string): void {
    const peer = this.peers.get(playerId)
    if (peer) {
      peer.dataChannel?.close()
      peer.connection.close()
      peer.state = 'disconnected'
      this.peers.delete(playerId)
      this.onPeerDisconnected?.(playerId)
    }
  }

  // Event handlers
  onConnected(handler: ConnectionHandler): void {
    this.onPeerConnected = handler
  }

  onDisconnected(handler: DisconnectHandler): void {
    this.onPeerDisconnected = handler
  }

  // Getters
  getPeers(): Map<string, PeerConnection> {
    return this.peers
  }

  getConnectedPeers(): string[] {
    return Array.from(this.peers.entries())
      .filter(([, peer]) => peer.state === 'connected')
      .map(([id]) => id)
  }

  isFullyConnected(expectedPlayerCount: number): boolean {
    // We need connections to all other players
    const connectedCount = this.getConnectedPeers().length
    return connectedCount >= expectedPlayerCount - 1
  }

  // Cleanup
  disconnect(): void {
    for (const [playerId] of this.peers) {
      this.disconnectPeer(playerId)
    }
    this.signalingChannel = null
  }
}
