/**
 * LocalEventQueue - Manages pending local events for lockstep netcode
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

  // Confirmed events by frame for deterministic replay
  private confirmedByFrame: Map<number, GameEvent[]> = new Map()

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
    this.confirmedByFrame.clear()
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
   * Get pending events for a specific frame
   */
  getPendingEventsForFrame(frame: number): GameEvent[] {
    return this.pendingEvents
      .filter(e => !e.confirmed && e.frame === frame)
      .map(e => e.event)
  }

  /**
   * Get pending events after a specific frame (inclusive)
   */
  getPendingEventsAfterFrame(frame: number): GameEvent[] {
    return this.pendingEvents
      .filter(e => !e.confirmed && e.frame >= frame)
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
   * Mark events as confirmed up to a frame
   */
  confirmEventsUpToFrame(frame: number): void {
    for (const buffered of this.pendingEvents) {
      if (buffered.frame <= frame) {
        buffered.confirmed = true

        // Store in confirmed map for replay
        let frameEvents = this.confirmedByFrame.get(buffered.frame)
        if (!frameEvents) {
          frameEvents = []
          this.confirmedByFrame.set(buffered.frame, frameEvents)
        }
        frameEvents.push(buffered.event)
      }
    }

    // Remove confirmed events from pending
    this.pendingEvents = this.pendingEvents.filter(e => !e.confirmed)
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
   * Filter events by type
   */
  filterByType<T extends GameEvent['type']>(
    events: GameEvent[],
    type: T
  ): Array<Extract<GameEvent, { type: T }>> {
    return events.filter(e => e.type === type) as Array<Extract<GameEvent, { type: T }>>
  }

  /**
   * Filter events by owner (for remote events)
   */
  filterByOwner(events: GameEvent[], ownerId: string): GameEvent[] {
    return events.filter(e => getEventOwnerId(e) === ownerId)
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

    // Remove old pending events
    this.pendingEvents = this.pendingEvents.filter(e => e.frame >= minFrame)

    // Remove old confirmed events
    for (const frame of this.confirmedByFrame.keys()) {
      if (frame < minFrame) {
        this.confirmedByFrame.delete(frame)
      }
    }
  }

  /**
   * Get debug info
   */
  getDebugInfo(): {
    pendingCount: number
    confirmedFrames: number
    oldestPendingFrame: number | null
    newestPendingFrame: number | null
  } {
    const pending = this.pendingEvents.filter(e => !e.confirmed)
    return {
      pendingCount: pending.length,
      confirmedFrames: this.confirmedByFrame.size,
      oldestPendingFrame: pending.length > 0 ? Math.min(...pending.map(e => e.frame)) : null,
      newestPendingFrame: pending.length > 0 ? Math.max(...pending.map(e => e.frame)) : null,
    }
  }
}
