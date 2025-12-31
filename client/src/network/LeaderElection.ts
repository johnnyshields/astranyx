/**
 * LeaderElection - Raft-inspired leader election for lockstep netcode
 *
 * Key Concepts (from Raft/TLA+ model):
 * - Term: Monotonically increasing election epoch
 * - State: follower | candidate | leader
 * - Voting: Each peer votes once per term, majority wins
 * - Heartbeat: Leader sends periodic heartbeats to maintain authority
 * - Timeout: Follower becomes candidate if no heartbeat received
 *
 * Safety Properties:
 * - At most one leader per term
 * - Leader only changes via election with majority
 * - Term always increases
 */

import type {
  PeerState,
  RequestVoteMessage,
  VoteResponseMessage,
  HeartbeatMessage,
  HeartbeatAckMessage,
  LeaderChangeHandler,
  PeerDisconnectHandler,
} from './types.ts'

export interface LeaderElectionConfig {
  localPlayerId: string
  playerOrder: Map<string, number>  // player_id -> index
  electionTimeout: number           // Ms before timeout (default: 1500)
  heartbeatInterval: number         // Ms between heartbeats (default: 500)
}

type ElectionMessage = RequestVoteMessage | VoteResponseMessage | HeartbeatMessage | HeartbeatAckMessage

export class LeaderElection {
  private config: LeaderElectionConfig

  // Raft state
  private currentTerm = 0
  private state: PeerState = 'follower'
  private votedFor: string | null = null
  private currentLeader: string | null = null

  // Election tracking
  private votesReceived: Set<string> = new Set()
  private lastHeartbeat: number = 0
  private electionTimer: ReturnType<typeof setTimeout> | null = null
  private heartbeatTimer: ReturnType<typeof setInterval> | null = null

  // Peer tracking
  private connectedPeers: Set<string> = new Set()
  private peerLastSeen: Map<string, number> = new Map()

  // Current frame (for log comparison)
  private currentFrame = 0

  // Callbacks
  private onLeaderChange: LeaderChangeHandler | null = null
  private onPeerDisconnect: PeerDisconnectHandler | null = null
  private sendMessage: ((peerId: string, message: ElectionMessage) => void) | null = null

  // Running state
  private running = false

  constructor(config: LeaderElectionConfig) {
    this.config = config
    // Initial leader is player with index 0
    this.currentLeader = this.getInitialLeader()
    if (this.currentLeader === config.localPlayerId) {
      this.state = 'leader'
    }
  }

  /**
   * Get the initial leader (player with lowest index)
   */
  private getInitialLeader(): string {
    let minIndex = Infinity
    let leaderId: string | null = null

    for (const [playerId, index] of this.config.playerOrder) {
      if (index < minIndex) {
        minIndex = index
        leaderId = playerId
      }
    }

    return leaderId!
  }

  /**
   * Get majority count for voting
   */
  private getMajority(): number {
    const totalPeers = this.config.playerOrder.size
    return Math.floor(totalPeers / 2) + 1
  }

  /**
   * Reset election state
   */
  reset(): void {
    this.stop()
    this.currentTerm = 0
    this.votedFor = null
    this.votesReceived.clear()
    this.lastHeartbeat = Date.now()
    this.connectedPeers.clear()
    this.peerLastSeen.clear()

    // Re-initialize leader
    this.currentLeader = this.getInitialLeader()
    this.state = this.currentLeader === this.config.localPlayerId ? 'leader' : 'follower'
  }

  /**
   * Start the election system
   */
  start(): void {
    if (this.running) return
    this.running = true
    this.lastHeartbeat = Date.now()

    if (this.isLeader()) {
      this.startHeartbeat()
    } else {
      this.startElectionTimer()
    }
  }

  /**
   * Stop the election system
   */
  stop(): void {
    this.running = false
    this.stopElectionTimer()
    this.stopHeartbeat()
  }

  // ===========================================================================
  // Peer Management
  // ===========================================================================

  /**
   * Add a connected peer
   */
  addPeer(peerId: string): void {
    this.connectedPeers.add(peerId)
    this.peerLastSeen.set(peerId, Date.now())
  }

  /**
   * Remove a peer (disconnected)
   */
  removePeer(peerId: string): void {
    this.connectedPeers.delete(peerId)
    this.peerLastSeen.delete(peerId)

    // If leader disconnected, start election
    if (peerId === this.currentLeader && this.state !== 'leader') {
      console.log(`LeaderElection: Leader ${peerId} disconnected, starting election`)
      this.startElection()
    }

    this.onPeerDisconnect?.(peerId)
  }

  /**
   * Get connected peer count
   */
  getConnectedPeerCount(): number {
    return this.connectedPeers.size
  }

  // ===========================================================================
  // Timer Management
  // ===========================================================================

  /**
   * Start election timeout timer
   */
  private startElectionTimer(): void {
    this.stopElectionTimer()

    // Randomize timeout to avoid split votes (Raft technique)
    const timeout = this.config.electionTimeout + Math.random() * this.config.electionTimeout * 0.5

    this.electionTimer = setTimeout(() => {
      if (!this.running) return

      const now = Date.now()
      const timeSinceHeartbeat = now - this.lastHeartbeat

      if (timeSinceHeartbeat >= this.config.electionTimeout) {
        console.log(`LeaderElection: Election timeout (${timeSinceHeartbeat}ms since last heartbeat)`)
        this.startElection()
      } else {
        // Restart timer for remaining time
        this.startElectionTimer()
      }
    }, timeout)
  }

  /**
   * Stop election timer
   */
  private stopElectionTimer(): void {
    if (this.electionTimer) {
      clearTimeout(this.electionTimer)
      this.electionTimer = null
    }
  }

  /**
   * Start heartbeat (leader only)
   */
  private startHeartbeat(): void {
    this.stopHeartbeat()

    this.heartbeatTimer = setInterval(() => {
      if (!this.running || this.state !== 'leader') {
        this.stopHeartbeat()
        return
      }
      this.broadcastHeartbeat()
    }, this.config.heartbeatInterval)

    // Send immediate heartbeat
    this.broadcastHeartbeat()
  }

  /**
   * Stop heartbeat
   */
  private stopHeartbeat(): void {
    if (this.heartbeatTimer) {
      clearInterval(this.heartbeatTimer)
      this.heartbeatTimer = null
    }
  }

  // ===========================================================================
  // Election Protocol
  // ===========================================================================

  /**
   * Start an election (become candidate)
   */
  private startElection(): void {
    if (!this.running) return

    // Increment term and become candidate
    this.currentTerm++
    this.state = 'candidate'
    this.votedFor = this.config.localPlayerId
    this.votesReceived.clear()
    this.votesReceived.add(this.config.localPlayerId) // Vote for self
    this.currentLeader = null

    console.log(`LeaderElection: Starting election for term ${this.currentTerm}`)

    // Request votes from all peers
    const requestVote: RequestVoteMessage = {
      type: 'request_vote',
      term: this.currentTerm,
      candidateId: this.config.localPlayerId,
      lastFrame: this.currentFrame,
    }

    for (const peerId of this.connectedPeers) {
      this.sendMessage?.(peerId, requestVote)
    }

    // Check if we already have majority (single player)
    this.checkElectionResult()

    // Restart election timer in case we don't win
    this.startElectionTimer()
  }

  /**
   * Handle incoming vote request
   */
  private handleRequestVote(message: RequestVoteMessage, fromPeerId: string): void {
    let voteGranted = false

    // Update term if needed
    if (message.term > this.currentTerm) {
      this.stepDown(message.term)
    }

    // Grant vote if:
    // 1. Message term >= current term
    // 2. Haven't voted or already voted for this candidate
    // 3. Candidate's log is at least as up-to-date
    if (
      message.term >= this.currentTerm &&
      (this.votedFor === null || this.votedFor === message.candidateId) &&
      message.lastFrame >= this.currentFrame
    ) {
      voteGranted = true
      this.votedFor = message.candidateId
      this.currentTerm = message.term
      this.lastHeartbeat = Date.now() // Reset election timer
    }

    // Send vote response - always send even if vote not granted
    const response: VoteResponseMessage = {
      type: 'vote_response',
      term: this.currentTerm,
      voteGranted,
      voterId: this.config.localPlayerId,
    }

    if (this.sendMessage) {
      this.sendMessage(fromPeerId, response)
    }
  }

  /**
   * Handle incoming vote response
   */
  private handleVoteResponse(message: VoteResponseMessage): void {
    // Ignore if not candidate or old term
    if (this.state !== 'candidate' || message.term !== this.currentTerm) {
      return
    }

    // Update term if higher
    if (message.term > this.currentTerm) {
      this.stepDown(message.term)
      return
    }

    if (message.voteGranted) {
      this.votesReceived.add(message.voterId)
      console.log(`LeaderElection: Received vote from ${message.voterId} (${this.votesReceived.size}/${this.getMajority()} needed)`)
      this.checkElectionResult()
    }
  }

  /**
   * Check if we've won the election
   */
  private checkElectionResult(): void {
    if (this.state !== 'candidate') return

    if (this.votesReceived.size >= this.getMajority()) {
      this.becomeLeader()
    }
  }

  /**
   * Become leader after winning election
   */
  private becomeLeader(): void {
    console.log(`LeaderElection: Became leader for term ${this.currentTerm}`)

    this.state = 'leader'
    this.currentLeader = this.config.localPlayerId
    this.stopElectionTimer()
    this.startHeartbeat()

    this.onLeaderChange?.(this.config.localPlayerId, this.currentTerm)
  }

  /**
   * Step down to follower (discovered higher term)
   */
  private stepDown(newTerm: number): void {
    console.log(`LeaderElection: Stepping down, term ${this.currentTerm} -> ${newTerm}`)

    this.currentTerm = newTerm
    this.state = 'follower'
    this.votedFor = null
    this.votesReceived.clear()

    this.stopHeartbeat()
    this.startElectionTimer()
  }

  // ===========================================================================
  // Heartbeat Protocol
  // ===========================================================================

  /**
   * Broadcast heartbeat to all peers (leader only)
   */
  private broadcastHeartbeat(): void {
    if (this.state !== 'leader') return

    const heartbeat: HeartbeatMessage = {
      type: 'heartbeat',
      term: this.currentTerm,
      leaderId: this.config.localPlayerId,
      frame: this.currentFrame,
    }

    for (const peerId of this.connectedPeers) {
      this.sendMessage?.(peerId, heartbeat)
    }
  }

  /**
   * Handle incoming heartbeat
   */
  private handleHeartbeat(message: HeartbeatMessage, fromPeerId: string): void {
    // Ignore heartbeats from old terms
    if (message.term < this.currentTerm) {
      return
    }

    // Update term and step down if needed
    if (message.term > this.currentTerm) {
      this.stepDown(message.term)
    }

    // Track previous leader for change notification
    const previousLeader = this.currentLeader

    // Accept this peer as leader
    this.state = 'follower'
    this.currentLeader = message.leaderId
    this.currentTerm = message.term  // Ensure term is updated
    this.lastHeartbeat = Date.now()
    this.peerLastSeen.set(fromPeerId, Date.now())

    // Notify of leader change if different
    if (previousLeader !== message.leaderId) {
      this.onLeaderChange?.(message.leaderId, message.term)
    }

    // Restart election timer (only if running)
    if (this.running) {
      this.startElectionTimer()
    }

    // Send ack
    const ack: HeartbeatAckMessage = {
      type: 'heartbeat_ack',
      term: this.currentTerm,
      peerId: this.config.localPlayerId,
      frame: this.currentFrame,
    }

    this.sendMessage?.(fromPeerId, ack)
  }

  /**
   * Handle heartbeat acknowledgment (leader only)
   */
  private handleHeartbeatAck(message: HeartbeatAckMessage): void {
    if (this.state !== 'leader') return

    this.peerLastSeen.set(message.peerId, Date.now())
  }

  // ===========================================================================
  // Message Handling
  // ===========================================================================

  /**
   * Handle incoming election message
   * Note: Messages are processed even when not "running" to support testing
   * and handling messages received during startup
   */
  handleMessage(message: ElectionMessage, fromPeerId: string): void {
    switch (message.type) {
      case 'request_vote':
        this.handleRequestVote(message, fromPeerId)
        break
      case 'vote_response':
        this.handleVoteResponse(message)
        break
      case 'heartbeat':
        this.handleHeartbeat(message, fromPeerId)
        break
      case 'heartbeat_ack':
        this.handleHeartbeatAck(message)
        break
    }
  }

  // ===========================================================================
  // Callbacks and Getters
  // ===========================================================================

  /**
   * Set message send function
   */
  setSendMessage(fn: (peerId: string, message: ElectionMessage) => void): void {
    this.sendMessage = fn
  }

  /**
   * Set leader change handler
   */
  setLeaderChangeHandler(handler: LeaderChangeHandler): void {
    this.onLeaderChange = handler
  }

  /**
   * Set peer disconnect handler
   */
  setPeerDisconnectHandler(handler: PeerDisconnectHandler): void {
    this.onPeerDisconnect = handler
  }

  /**
   * Update current frame (for log comparison)
   */
  setCurrentFrame(frame: number): void {
    this.currentFrame = frame
  }

  /**
   * Check if this peer is the leader
   */
  isLeader(): boolean {
    return this.state === 'leader'
  }

  /**
   * Get current state
   */
  getState(): PeerState {
    return this.state
  }

  /**
   * Get current term
   */
  getCurrentTerm(): number {
    return this.currentTerm
  }

  /**
   * Get current leader ID
   */
  getCurrentLeader(): string | null {
    return this.currentLeader
  }

  /**
   * Get local player index
   */
  getLocalPlayerIndex(): number {
    return this.config.playerOrder.get(this.config.localPlayerId) ?? 0
  }

  /**
   * Get debug info
   */
  getDebugInfo(): {
    state: PeerState
    term: number
    leader: string | null
    votedFor: string | null
    votes: number
    connectedPeers: number
    timeSinceHeartbeat: number
  } {
    return {
      state: this.state,
      term: this.currentTerm,
      leader: this.currentLeader,
      votedFor: this.votedFor,
      votes: this.votesReceived.size,
      connectedPeers: this.connectedPeers.size,
      timeSinceHeartbeat: Date.now() - this.lastHeartbeat,
    }
  }
}
