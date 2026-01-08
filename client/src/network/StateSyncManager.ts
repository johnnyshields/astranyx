/**
 * StateSyncManager - Manages state synchronization for lockstep netcode
 *
 * TLA+ Model: LockstepState.tla
 * - syncTerm variable: term of last accepted sync (for validation)
 * - inSync variable: whether peer matches leader state
 * - SendStateSync action: leader broadcasts state
 * - ReceiveStateSync action: follower applies sync, preserves local events
 * - Desync action: models checksum mismatch detection
 *
 * Key invariant: syncTerm[p] <= currentTerm[p] (no time travel)
 *
 * Responsibilities:
 * - Track when state syncs should be sent (leader only)
 * - Handle incoming state syncs (followers only)
 * - Detect desync via checksum comparison
 * - Coordinate with LocalEventQueue for event re-application
 */

import type { StateSyncMessage, GameEvent } from './types.ts'
import type { LocalEventQueue } from './LocalEventQueue.ts'
import { SafeConsole } from '../core/SafeConsole.ts'

export interface StateSyncManagerConfig {
  syncInterval: number        // Frames between syncs (default: 300 = 5 seconds)
}

export type StateSyncCallback = (
  state: unknown,
  frame: number,
  pendingEvents: GameEvent[]
) => void

export class StateSyncManager {
  private config: StateSyncManagerConfig

  // Last frame when state sync was sent/received
  private lastSyncFrame = 0

  // Flag for immediate sync on desync detection
  private desyncDetected = false

  // Current frame tracker
  private currentFrame = 0

  // Reference to event queue for coordinating re-application
  private eventQueue: LocalEventQueue | null = null

  // Callback when state sync is received
  private onSyncReceived: StateSyncCallback | null = null

  // Current election term (for validating syncs)
  private currentTerm = 0

  constructor(config: StateSyncManagerConfig) {
    this.config = config
  }

  /**
   * Reset the manager state
   */
  reset(): void {
    this.lastSyncFrame = 0
    this.desyncDetected = false
    this.currentFrame = 0
    this.currentTerm = 0
  }

  /**
   * Set reference to event queue
   */
  setEventQueue(queue: LocalEventQueue): void {
    this.eventQueue = queue
  }

  /**
   * Set callback for when state sync is received
   */
  setStateSyncHandler(handler: StateSyncCallback): void {
    this.onSyncReceived = handler
  }

  /**
   * Update current frame
   */
  setCurrentFrame(frame: number): void {
    this.currentFrame = frame
  }

  /**
   * Update current term
   */
  setCurrentTerm(term: number): void {
    this.currentTerm = term
  }

  /**
   * Mark that a desync was detected (triggers immediate sync)
   * TLA+: Desync action sets inSync[p] = FALSE
   */
  markDesync(): void {
    this.desyncDetected = true
  }

  /**
   * Clear desync flag (called after sync is sent)
   */
  clearDesync(): void {
    this.desyncDetected = false
  }

  /**
   * Check if desync was detected
   */
  hasDesync(): boolean {
    return this.desyncDetected
  }

  /**
   * Check if it's time to send a state sync (leader only)
   */
  shouldSendSync(): boolean {
    // Immediate sync on desync
    if (this.desyncDetected) {
      return true
    }

    // Periodic sync
    return this.currentFrame - this.lastSyncFrame >= this.config.syncInterval
  }

  /**
   * Create a state sync message
   * TLA+: SendStateSync action (leader only)
   */
  createSyncMessage(state: unknown, checksum: number): StateSyncMessage {
    return {
      type: 'state_sync',
      frame: this.currentFrame,
      state,
      checksum,
      term: this.currentTerm,
    }
  }

  /**
   * Record that a sync was sent
   */
  onSyncSent(): void {
    this.lastSyncFrame = this.currentFrame
    this.desyncDetected = false
  }

  /**
   * Handle incoming state sync (follower only)
   * Returns events that should be re-applied after sync
   * TLA+: ReceiveStateSync action - validates term AND frame freshness, preserves local events
   */
  receiveSyncMessage(message: StateSyncMessage): GameEvent[] {
    // Validate term - only accept syncs from current or higher term
    if (message.term < this.currentTerm) {
      SafeConsole.warn(`StateSyncManager: Ignoring sync from old term ${message.term} (current: ${this.currentTerm})`)
      return []
    }

    // Reject out-of-order syncs: don't regress to an older sync frame
    // This handles the edge case of delayed/reordered sync messages
    if (message.frame < this.lastSyncFrame) {
      SafeConsole.warn(`StateSyncManager: Ignoring out-of-order sync at frame ${message.frame} (last sync: ${this.lastSyncFrame})`)
      return []
    }

    // Update term if higher
    if (message.term > this.currentTerm) {
      this.currentTerm = message.term
    }

    SafeConsole.log(`StateSyncManager: Applying sync from frame ${message.frame}, term ${message.term}`)

    // Get pending events to re-apply from event queue
    let pendingEvents: GameEvent[] = []
    if (this.eventQueue) {
      pendingEvents = this.eventQueue.onStateSync(message.frame)
    }

    this.lastSyncFrame = message.frame
    this.desyncDetected = false

    // Notify handler
    this.onSyncReceived?.(message.state, message.frame, pendingEvents)

    return pendingEvents
  }

  /**
   * Get last sync frame
   */
  getLastSyncFrame(): number {
    return this.lastSyncFrame
  }

  /**
   * Get current term
   */
  getCurrentTerm(): number {
    return this.currentTerm
  }

  /**
   * Get sync interval
   */
  getSyncInterval(): number {
    return this.config.syncInterval
  }

  /**
   * Get frames since last sync
   */
  getFramesSinceSync(): number {
    return this.currentFrame - this.lastSyncFrame
  }

  /**
   * Get debug info
   */
  getDebugInfo(): {
    lastSyncFrame: number
    currentFrame: number
    framesSinceSync: number
    desyncDetected: boolean
    currentTerm: number
  } {
    return {
      lastSyncFrame: this.lastSyncFrame,
      currentFrame: this.currentFrame,
      framesSinceSync: this.getFramesSinceSync(),
      desyncDetected: this.desyncDetected,
      currentTerm: this.currentTerm,
    }
  }

  // ===========================================================================
  // Runtime Invariant Checks (TLA+ verification at runtime)
  // ===========================================================================

  // Track last accepted sync term for validation
  private lastAcceptedSyncTerm = 0

  /**
   * Check TLA+ invariants at runtime.
   *
   * TLA+ Invariants checked:
   * - SyncTermBounded: syncTerm[p] <= currentTerm[p] (no time travel)
   * - TypeInvariant: term >= 0
   */
  assertInvariants(): void {
    // TypeInvariant: term >= 0
    if (this.currentTerm < 0) {
      throw new Error(`TLA+ TypeInvariant violated: term ${this.currentTerm} < 0`)
    }

    // SyncTermBounded: accepted sync term should not exceed current term
    if (this.lastAcceptedSyncTerm > this.currentTerm) {
      throw new Error(
        `TLA+ SyncTermBounded violated: lastAcceptedSyncTerm ${this.lastAcceptedSyncTerm} > currentTerm ${this.currentTerm}`
      )
    }
  }

  /**
   * Record accepted sync term (for invariant checking)
   */
  recordAcceptedSyncTerm(term: number): void {
    this.lastAcceptedSyncTerm = term
  }
}
