/**
 * LocalEventQueue - Manages pending local events for lockstep netcode
 *
 * TLA+ Model: LockstepState.tla
 * - pendingEvents variable: set of <<owner, frame>> tuples
 * - GenerateEvent action: adds event tuple to pending set
 * - ReceiveStateSync action: clears remote events, preserves local
 *
 * Key TLA+ Invariant:
 * - LocalEventsPreserved: after sync, only local events remain
 *   \A p \in Peer : \A e \in pendingEvents[p] : e[1] = p
 *
 * Runtime check: assertLocalEventsOnly() verifies this invariant
 *
 * Responsibilities:
 * - Buffer local events before they're confirmed by the network
 * - Track events by frame for efficient retrieval
 * - Preserve events across state syncs for re-application
 * - Cleanup old events beyond buffer size
 * - Support event filtering (e.g., by player, by type)
 */

import type { GameEvent } from './types.ts'
import { getEventOwnerId } from './types.ts'

export interface LocalEventQueueConfig {
  bufferSize: number         // Max frames to buffer (default: 900 = 15 seconds)
  localPlayerId: string
}

interface BufferedEvent {
  event: GameEvent
  frame: number
  timestamp: number          // When the event was created (for debugging)
  confirmed: boolean         // Whether event has been confirmed by leader
}

export class LocalEventQueue {
  private config: LocalEventQueueConfig

  // All pending events (not yet confirmed)
  private pendingEvents: BufferedEvent[] = []

  // Current frame tracker
  private currentFrame = 0

  // Last synced frame (events before this are confirmed)
  private lastSyncedFrame = -1

  constructor(config: LocalEventQueueConfig) {
    this.config = config
  }

  /**
   * Reset the queue
   */
  reset(): void {
    this.pendingEvents = []
    this.currentFrame = 0
    this.lastSyncedFrame = -1
  }

  /**
   * Add a local event to the pending queue
   */
  addEvent(event: GameEvent, frame: number): void {
    this.pendingEvents.push({
      event,
      frame,
      timestamp: Date.now(),
      confirmed: false,
    })

    // Cleanup if buffer exceeds size
    this.cleanup()
  }

  /**
   * Add multiple events at once
   */
  addEvents(events: GameEvent[], frame: number): void {
    const timestamp = Date.now()
    for (const event of events) {
      this.pendingEvents.push({
        event,
        frame,
        timestamp,
        confirmed: false,
      })
    }
    this.cleanup()
  }

  /**
   * Get all pending events (not yet confirmed)
   */
  getPendingEvents(): GameEvent[] {
    return this.pendingEvents
      .filter(e => !e.confirmed)
      .map(e => e.event)
  }

  /**
   * Get all local events that should be re-applied after state sync
   * These are events owned by the local player that may not be reflected in the sync
   */
  getEventsForReapply(): GameEvent[] {
    return this.pendingEvents
      .filter(e => {
        const ownerId = getEventOwnerId(e.event)
        return ownerId === this.config.localPlayerId
      })
      .map(e => e.event)
  }

  /**
   * Called when state sync is received
   * Clears events up to the sync frame, preserves local events for re-application
   */
  onStateSync(syncFrame: number): GameEvent[] {
    // Get local events that need to be re-applied
    const eventsToReapply = this.getEventsForReapply()

    // Clear all pending events (they're now in the synced state or will be re-applied)
    this.pendingEvents = []
    this.lastSyncedFrame = syncFrame

    return eventsToReapply
  }

  /**
   * Update current frame
   */
  setCurrentFrame(frame: number): void {
    this.currentFrame = frame
  }

  /**
   * Get current frame
   */
  getCurrentFrame(): number {
    return this.currentFrame
  }

  /**
   * Get last synced frame
   */
  getLastSyncedFrame(): number {
    return this.lastSyncedFrame
  }

  /**
   * Filter out local events (for applying remote events only)
   */
  filterRemoteEvents(events: GameEvent[]): GameEvent[] {
    return events.filter(e => getEventOwnerId(e) !== this.config.localPlayerId)
  }

  /**
   * Get count of pending events
   */
  pendingCount(): number {
    return this.pendingEvents.filter(e => !e.confirmed).length
  }

  /**
   * Get total buffer size
   */
  size(): number {
    return this.pendingEvents.length
  }

  /**
   * Cleanup old events beyond buffer size
   */
  private cleanup(): void {
    const minFrame = this.currentFrame - this.config.bufferSize
    this.pendingEvents = this.pendingEvents.filter(e => e.frame >= minFrame)
  }

  /**
   * Get debug info
   */
  getDebugInfo(): {
    pendingCount: number
    oldestPendingFrame: number | null
    newestPendingFrame: number | null
  } {
    const pending = this.pendingEvents.filter(e => !e.confirmed)
    return {
      pendingCount: pending.length,
      oldestPendingFrame: pending.length > 0 ? Math.min(...pending.map(e => e.frame)) : null,
      newestPendingFrame: pending.length > 0 ? Math.max(...pending.map(e => e.frame)) : null,
    }
  }

  // ===========================================================================
  // Runtime Invariant Checks (TLA+ verification at runtime)
  // ===========================================================================

  /**
   * Check TLA+ LocalEventsPreserved invariant.
   * Call this after onStateSync() to verify only local events remain.
   *
   * TLA+ Invariant: \A e \in pendingEvents[p] : e[1] = p
   */
  assertLocalEventsOnly(): void {
    for (const buffered of this.pendingEvents) {
      const ownerId = getEventOwnerId(buffered.event)
      if (ownerId !== this.config.localPlayerId) {
        throw new Error(
          `TLA+ LocalEventsPreserved violated: found event owned by ${ownerId}, expected ${this.config.localPlayerId}`
        )
      }
    }
  }
}
