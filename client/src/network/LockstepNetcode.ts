/**
 * Lockstep Netcode for P2P multiplayer
 *
 * This is the main orchestrator that coordinates:
 * - InputBuffer: Frame input management
 * - LocalEventQueue: Owner-authoritative event buffering
 * - StateSyncManager: Periodic state synchronization
 * - LeaderElection: Raft-inspired leader election
 *
 * How it works:
 * 1. Each player runs the same deterministic simulation
 * 2. Players exchange inputs for each frame
 * 3. Game only advances when all inputs are received
 * 4. Input delay hides network latency
 * 5. Leader sends periodic state syncs to correct drift
 * 6. If leader disconnects, election chooses new leader
 */

import type {
  PlayerInput,
  GameEvent,
  FrameInput,
  LockstepConfig,
  NetMessage,
  StateSyncMessage,
  InputHandler,
  DesyncHandler,
  StateSyncHandler,
  LeaderChangeHandler,
  PeerDisconnectHandler,
} from './types.ts'
import {
  emptyInput,
  isStateSyncMessage,
  isElectionMessage,
  isHeartbeatMessage,
  isFrameInput,
  DEFAULT_CONFIG,
} from './types.ts'
import { InputBuffer } from './InputBuffer.ts'
import { LocalEventQueue } from './LocalEventQueue.ts'
import { StateSyncManager } from './StateSyncManager.ts'
import { LeaderElection } from './LeaderElection.ts'

// Re-export types for backwards compatibility
export type { PlayerInput, GameEvent, FrameInput, LockstepConfig, StateSyncMessage }
export { emptyInput }

/**
 * Compare two inputs for equality
 */
export function inputsEqual(a: PlayerInput, b: PlayerInput): boolean {
  return (
    a.up === b.up &&
    a.down === b.down &&
    a.left === b.left &&
    a.right === b.right &&
    a.fire === b.fire &&
    a.special === b.special
  )
}

export class LockstepNetcode {
  private config: LockstepConfig

  // Extracted components
  private inputBuffer: InputBuffer
  private eventQueue: LocalEventQueue
  private syncManager: StateSyncManager
  private election: LeaderElection

  // Frame tracking
  private currentFrame = 0
  private confirmedFrame = -1

  // Peers
  private peers: Map<string, RTCDataChannel> = new Map()

  // Callbacks
  private onInputsReady: InputHandler | null = null
  private onDesync: DesyncHandler | null = null
  private onStateSync: StateSyncHandler | null = null
  private onLeaderChange: LeaderChangeHandler | null = null
  private onPeerDisconnect: PeerDisconnectHandler | null = null

  // State
  private running = false
  private waitingForInputs = false

  constructor(config: LockstepConfig) {
    this.config = {
      inputDelay: config.inputDelay ?? DEFAULT_CONFIG.inputDelay,
      maxRollbackFrames: config.maxRollbackFrames ?? DEFAULT_CONFIG.maxRollbackFrames,
      playerCount: config.playerCount,
      localPlayerId: config.localPlayerId,
      playerOrder: config.playerOrder,
      stateSyncInterval: config.stateSyncInterval ?? DEFAULT_CONFIG.stateSyncInterval,
      eventBufferSize: config.eventBufferSize ?? DEFAULT_CONFIG.eventBufferSize,
      electionTimeout: config.electionTimeout ?? DEFAULT_CONFIG.electionTimeout,
      heartbeatInterval: config.heartbeatInterval ?? DEFAULT_CONFIG.heartbeatInterval,
    }

    // Initialize components
    this.inputBuffer = new InputBuffer({
      inputDelay: this.config.inputDelay,
      playerCount: this.config.playerCount,
      playerOrder: this.config.playerOrder,
    })

    this.eventQueue = new LocalEventQueue({
      bufferSize: this.config.eventBufferSize!,
      localPlayerId: this.config.localPlayerId,
    })

    this.syncManager = new StateSyncManager({
      syncInterval: this.config.stateSyncInterval!,
      localPlayerId: this.config.localPlayerId,
    })
    this.syncManager.setEventQueue(this.eventQueue)

    this.election = new LeaderElection({
      localPlayerId: this.config.localPlayerId,
      playerOrder: this.config.playerOrder,
      electionTimeout: this.config.electionTimeout!,
      heartbeatInterval: this.config.heartbeatInterval!,
    })

    // Wire up election message sending
    this.election.setSendMessage((peerId, message) => {
      this.sendToPeer(peerId, message)
    })

    // Wire up election callbacks
    this.election.setLeaderChangeHandler((leaderId, term) => {
      console.log(`LockstepNetcode: Leader changed to ${leaderId} (term ${term})`)
      this.syncManager.setCurrentTerm(term)
      this.onLeaderChange?.(leaderId, term)
    })

    this.election.setPeerDisconnectHandler((peerId) => {
      console.log(`LockstepNetcode: Peer ${peerId} disconnected`)
      this.onPeerDisconnect?.(peerId)
    })
  }

  start(): void {
    this.running = true
    this.currentFrame = 0
    this.confirmedFrame = -1

    // Reset all components
    this.inputBuffer.reset()
    this.eventQueue.reset()
    this.syncManager.reset()
    this.election.reset()

    // Start election system
    this.election.start()

    console.log('LockstepNetcode: Started', {
      playerCount: this.config.playerCount,
      inputDelay: this.config.inputDelay,
      localPlayerId: this.config.localPlayerId,
      isLeader: this.election.isLeader(),
      peers: Array.from(this.peers.keys()),
    })
  }

  stop(): void {
    this.running = false
    this.election.stop()
  }

  /**
   * Add a peer connection
   */
  addPeer(playerId: string, dataChannel: RTCDataChannel): void {
    console.log(`LockstepNetcode: Adding peer ${playerId}`)
    this.peers.set(playerId, dataChannel)
    this.election.addPeer(playerId)

    dataChannel.onmessage = (event) => {
      const data = JSON.parse(event.data as string) as NetMessage
      this.handleMessage(data, playerId)
    }
  }

  removePeer(playerId: string): void {
    this.peers.delete(playerId)
    this.election.removePeer(playerId)
  }

  /**
   * Handle incoming network message
   */
  private handleMessage(data: NetMessage, fromPeerId: string): void {
    // Handle state sync messages
    if (isStateSyncMessage(data)) {
      console.log(`LockstepNetcode: Received state sync for frame ${data.frame}`)
      this.receiveStateSync(data)
      return
    }

    // Handle election messages
    if (isElectionMessage(data) || isHeartbeatMessage(data)) {
      this.election.handleMessage(data, fromPeerId)
      return
    }

    // Handle input messages
    if (isFrameInput(data)) {
      console.log(`LockstepNetcode: Received input from ${data.playerId} for frame ${data.frame}`)
      this.receiveInput(data)
      return
    }
  }

  /**
   * Called each game tick with local input
   * @param localInput - The local player's input
   * @param events - Owner-authoritative events detected this frame
   * @param checksum - Optional checksum of current game state for desync detection
   * Returns true if simulation should advance
   */
  tick(localInput: PlayerInput, events?: GameEvent[], checksum?: number): boolean {
    if (!this.running) return false

    // Store local checksum
    if (checksum !== undefined) {
      this.inputBuffer.setLocalChecksum(checksum)
    }

    // Buffer local events
    if (events && events.length > 0) {
      this.eventQueue.addEvents(events, this.currentFrame)
    }

    // Create input for future frame (with input delay)
    const targetFrame = this.currentFrame + this.config.inputDelay
    const frameInput: FrameInput = {
      frame: targetFrame,
      playerId: this.config.localPlayerId,
      input: localInput,
      events: events && events.length > 0 ? events : undefined,
      checksum,
    }

    // Store locally
    this.inputBuffer.storeInput(frameInput)

    // Send to all peers
    this.broadcastInput(frameInput)

    // Update frame trackers
    this.syncManager.setCurrentFrame(this.currentFrame)
    this.eventQueue.setCurrentFrame(this.currentFrame)
    this.election.setCurrentFrame(this.currentFrame)

    // Try to advance
    return this.tryAdvanceFrame()
  }

  /**
   * Try to advance to next frame if all inputs received
   */
  private tryAdvanceFrame(): boolean {
    if (!this.inputBuffer.hasAllInputs(this.currentFrame)) {
      console.log(`LockstepNetcode: Frame ${this.currentFrame} has ${this.inputBuffer.getInputCount(this.currentFrame)}/${this.config.playerCount} inputs`)
      this.waitingForInputs = true
      return false
    }

    this.waitingForInputs = false

    // Check for desync
    const checksumFrame = this.currentFrame - this.config.inputDelay
    if (checksumFrame >= 0) {
      this.checkForDesync(checksumFrame)
    }

    // Get ordered inputs and events
    const result = this.inputBuffer.getOrderedInputs(this.currentFrame)
    if (!result) return false

    // Notify game to simulate
    this.onInputsReady?.(result.inputs, result.events)

    // Advance frame
    this.confirmedFrame = this.currentFrame
    this.currentFrame++

    // Cleanup
    this.inputBuffer.cleanup(this.confirmedFrame)

    return true
  }

  /**
   * Check for checksum mismatches
   */
  private checkForDesync(frame: number): void {
    const mismatches = this.inputBuffer.checkDesync(frame, this.config.localPlayerId)

    for (const mismatch of mismatches) {
      console.error(`DESYNC DETECTED at frame ${frame}!`)
      console.error(`  Local checksum: ${mismatch.localChecksum}`)
      console.error(`  Remote (${mismatch.playerId}) checksum: ${mismatch.remoteChecksum}`)
      this.syncManager.markDesync()
      this.onDesync?.(frame, mismatch.localChecksum, mismatch.remoteChecksum)
    }
  }

  private receiveInput(frameInput: FrameInput): void {
    // Ignore inputs for frames we've already processed
    if (frameInput.frame <= this.confirmedFrame) {
      return
    }

    this.inputBuffer.storeInput(frameInput)

    // Try to advance if we were waiting
    if (this.waitingForInputs) {
      this.tryAdvanceFrame()
    }
  }

  private broadcastInput(frameInput: FrameInput): void {
    const message = JSON.stringify(frameInput)
    for (const [, channel] of this.peers) {
      if (channel.readyState === 'open') {
        channel.send(message)
      }
    }
  }

  private sendToPeer(peerId: string, message: NetMessage): void {
    const channel = this.peers.get(peerId)
    if (channel && channel.readyState === 'open') {
      channel.send(JSON.stringify(message))
    }
  }

  // ===========================================================================
  // State Sync
  // ===========================================================================

  /**
   * Broadcast state sync to all peers.
   * Should only be called by the leader.
   */
  broadcastStateSync(state: unknown, checksum: number): void {
    if (!this.isHost()) {
      console.warn('LockstepNetcode: Non-leader tried to broadcast state sync')
      return
    }

    const message = this.syncManager.createSyncMessage(state, checksum)
    const json = JSON.stringify(message)

    for (const [, channel] of this.peers) {
      if (channel.readyState === 'open') {
        channel.send(json)
      }
    }

    this.syncManager.onSyncSent()
    console.log(`LockstepNetcode: Broadcast state sync at frame ${this.currentFrame}`)
  }

  /**
   * Handle received state sync from leader
   */
  private receiveStateSync(message: StateSyncMessage): void {
    // Only non-leaders should apply state sync
    if (this.isHost()) {
      console.warn('LockstepNetcode: Leader received state sync (ignoring)')
      return
    }

    const pendingEvents = this.syncManager.receiveSyncMessage(message)
    this.onStateSync?.(message.state, message.frame, pendingEvents)
  }

  /**
   * Check if it's time to send a state sync.
   */
  shouldSendStateSync(): boolean {
    if (!this.isHost()) return false
    return this.syncManager.shouldSendSync()
  }

  /**
   * Clear desync flag after sending sync
   */
  clearDesyncFlag(): void {
    this.syncManager.clearDesync()
  }

  /**
   * Check if this client is the leader.
   */
  isHost(): boolean {
    return this.election.isLeader()
  }

  // ===========================================================================
  // Event handlers
  // ===========================================================================

  setInputHandler(handler: InputHandler): void {
    this.onInputsReady = handler
  }

  setDesyncHandler(handler: DesyncHandler): void {
    this.onDesync = handler
  }

  setStateSyncHandler(handler: StateSyncHandler): void {
    this.onStateSync = handler
    this.syncManager.setStateSyncHandler(handler)
  }

  setLeaderChangeHandler(handler: LeaderChangeHandler): void {
    this.onLeaderChange = handler
  }

  setPeerDisconnectHandler(handler: PeerDisconnectHandler): void {
    this.onPeerDisconnect = handler
  }

  // ===========================================================================
  // Getters
  // ===========================================================================

  getCurrentFrame(): number {
    return this.currentFrame
  }

  getConfirmedFrame(): number {
    return this.confirmedFrame
  }

  isWaitingForInputs(): boolean {
    return this.waitingForInputs
  }

  getInputDelay(): number {
    return this.config.inputDelay
  }

  /**
   * Get the local player index for deterministic spawning
   */
  getLocalPlayerIndex(): number {
    return this.election.getLocalPlayerIndex()
  }

  /**
   * Get current election term
   */
  getCurrentTerm(): number {
    return this.election.getCurrentTerm()
  }

  /**
   * Get current leader ID
   */
  getCurrentLeader(): string | null {
    return this.election.getCurrentLeader()
  }

  /**
   * Get debug info for all components
   */
  getDebugInfo(): {
    frame: number
    confirmedFrame: number
    waiting: boolean
    isLeader: boolean
    election: ReturnType<LeaderElection['getDebugInfo']>
    sync: ReturnType<StateSyncManager['getDebugInfo']>
    events: ReturnType<LocalEventQueue['getDebugInfo']>
    inputBufferSize: number
  } {
    return {
      frame: this.currentFrame,
      confirmedFrame: this.confirmedFrame,
      waiting: this.waitingForInputs,
      isLeader: this.isHost(),
      election: this.election.getDebugInfo(),
      sync: this.syncManager.getDebugInfo(),
      events: this.eventQueue.getDebugInfo(),
      inputBufferSize: this.inputBuffer.size(),
    }
  }
}
