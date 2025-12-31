/**
 * Lockstep Netcode for P2P multiplayer
 *
 * TLA+ Models:
 * - LockstepState.tla: Complete model with election, events, state sync
 * - LockstepNetwork.tla: Network reliability, connection states, desync detection
 * - LeaderElection.tla: Raft-inspired leader election (focused model)
 * - LockstepSimple.tla: Simplified model for fast iteration
 *
 * Key TLA+ Variables (mapped to this class and components):
 * - frame[p]: currentFrame (per-peer simulation progress)
 * - inputsReceived: InputBuffer tracks which peers submitted
 * - currentTerm[p]: LeaderElection.currentTerm
 * - state[p]: LeaderElection.state ("Leader" | "Follower" | "Candidate")
 * - pendingEvents[p]: LocalEventQueue.pendingEvents
 * - syncTerm[p]: StateSyncManager.lastAcceptedSyncTerm
 * - inSync[p]: StateSyncManager.desyncDetected (inverted)
 *
 * Key TLA+ Actions (mapped to methods):
 * - SubmitInput(p): tick() -> inputBuffer.storeInput()
 * - AdvanceFrame(p): tryAdvanceFrame()
 * - GenerateEvent(p): eventQueue.addEvents()
 * - SendStateSync(leader): broadcastStateSync()
 * - ReceiveStateSync(f,l): receiveStateSync() -> syncManager.receiveSyncMessage()
 * - Desync(p): checkForDesync() -> syncManager.markDesync()
 * - ForceLeaderChange: handleForceLeaderChange() (external trigger)
 *
 * Safety Invariants (verified by TLC and runtime assertions):
 * - NoTwoLeadersInSameTerm: At most one leader per election term
 * - FrameBoundedDrift: |frame[i] - frame[j]| <= 1
 * - LocalEventsPreserved: After sync, only local events remain
 * - SyncTermBounded: syncTerm[p] <= currentTerm[p]
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
  inputsEqual,
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
import { SafeConsole } from '../core/SafeConsole.ts'

// Re-export types for backwards compatibility
export type { PlayerInput, GameEvent, FrameInput, LockstepConfig, StateSyncMessage }
export { emptyInput, inputsEqual }

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
      SafeConsole.log(`LockstepNetcode: Leader changed to ${leaderId} (term ${term})`)
      this.syncManager.setCurrentTerm(term)
      this.onLeaderChange?.(leaderId, term)
    })

    this.election.setPeerDisconnectHandler((peerId) => {
      SafeConsole.log(`LockstepNetcode: Peer ${peerId} disconnected`)
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

    SafeConsole.log('LockstepNetcode: Started', {
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
    SafeConsole.log(`LockstepNetcode: Adding peer ${playerId}`)
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
      SafeConsole.log(`LockstepNetcode: Received state sync for frame ${data.frame}`)
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
      SafeConsole.log(`LockstepNetcode: Received input from ${data.playerId} for frame ${data.frame}`)
      this.receiveInput(data)
      return
    }
  }

  /**
   * Called each game tick with local input.
   * TLA+ model: SubmitInput(p) action - submits input and tries to advance frame.
   *
   * @param localInput - The local player's input
   * @param events - Owner-authoritative events detected this frame
   * @param checksum - Optional checksum of current game state for desync detection
   * @returns true if simulation should advance
   */
  tick(localInput: PlayerInput, events?: GameEvent[], checksum?: number): boolean {
    if (!this.running) return false

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
   * Try to advance to next frame if all inputs received.
   * TLA+ model: AdvanceFrame(p) action - advances when inputsReceived = Peer.
   */
  private tryAdvanceFrame(): boolean {
    if (!this.inputBuffer.hasAllInputs(this.currentFrame)) {
      SafeConsole.log(`LockstepNetcode: Frame ${this.currentFrame} has ${this.inputBuffer.getInputCount(this.currentFrame)}/${this.config.playerCount} inputs`)
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
   * Check for checksum mismatches.
   * TLA+ model: Desync(p) action in LockstepState.tla
   * - Compares checksums across peers at completed frame
   * - Sets inSync[p] = FALSE if mismatch found (triggers state sync)
   * - Only followers can desync (leader is authoritative)
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

  /**
   * Process received input from a peer.
   * TLA+ model: DeliverMessage(msg) action in LockstepNetwork.tla
   * - Stores input in buffer for the specified frame
   * - Triggers frame advance check if we were waiting
   */
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
    if (!this.isLeader()) {
      SafeConsole.warn('LockstepNetcode: Non-leader tried to broadcast state sync')
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
    SafeConsole.log(`LockstepNetcode: Broadcast state sync at frame ${this.currentFrame}`)
  }

  /**
   * Handle received state sync from leader
   */
  private receiveStateSync(message: StateSyncMessage): void {
    // Only non-leaders should apply state sync
    if (this.isLeader()) {
      SafeConsole.warn('LockstepNetcode: Leader received state sync (ignoring)')
      return
    }

    const pendingEvents = this.syncManager.receiveSyncMessage(message)
    this.onStateSync?.(message.state, message.frame, pendingEvents)
  }

  /**
   * Check if it's time to send a state sync.
   */
  shouldSendStateSync(): boolean {
    if (!this.isLeader()) return false
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
   * TLA+ model: state[p] = "Leader"
   */
  isLeader(): boolean {
    return this.election.isLeader()
  }

  /**
   * Force a leader change from external trigger (e.g., server authority).
   * TLA+ model: ForceLeaderChange(oldLeader, newLeader) action in LockstepState.tla
   *
   * This handles scenarios like:
   * - Server-side authority override
   * - Network partition recovery where server picks canonical leader
   * - Manual operator intervention
   *
   * After leader change:
   * - All peers move to new term (term bump)
   * - Old leader steps down to follower
   * - New leader starts sending heartbeats
   * - Followers may be out of sync (inSync = FALSE) until state sync
   *
   * @param newLeaderId The peer ID to become the new leader
   * @param newTerm The new election term (must be > current term)
   */
  forceLeaderChange(newLeaderId: string, newTerm: number): void {
    if (newTerm <= this.election.getCurrentTerm()) {
      SafeConsole.warn(
        `LockstepNetcode: Ignoring forceLeaderChange with stale term ${newTerm} <= ${this.election.getCurrentTerm()}`
      )
      return
    }

    SafeConsole.log(
      `LockstepNetcode: Force leader change to ${newLeaderId} at term ${newTerm}`
    )

    // Simulate receiving a heartbeat from the new leader with the new term
    // This will cause the election module to step down and accept the new leader
    this.election.handleMessage(
      {
        type: 'heartbeat',
        term: newTerm,
        leaderId: newLeaderId,
        frame: this.currentFrame,
      },
      newLeaderId
    )

    // Mark potential desync - new leader's state may differ
    if (!this.isLeader()) {
      this.syncManager.markDesync()
    }
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
      isLeader: this.isLeader(),
      election: this.election.getDebugInfo(),
      sync: this.syncManager.getDebugInfo(),
      events: this.eventQueue.getDebugInfo(),
      inputBufferSize: this.inputBuffer.size(),
    }
  }
}
