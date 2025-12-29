/**
 * NetworkManager - High-level multiplayer networking
 *
 * Handles:
 * - Sending player inputs to server
 * - Receiving game state updates
 * - Client-side prediction and reconciliation
 * - Entity interpolation for smooth remote player rendering
 */

import { WebRTCClient, type GameMessage } from './WebRTCClient.ts'

export interface PlayerInput {
  up: boolean
  down: boolean
  left: boolean
  right: boolean
  fire: boolean
  special: boolean
  timestamp: number
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
  playerId?: string
}

export interface GameStateSnapshot {
  tick: number
  timestamp: number
  entities: EntityState[]
  events: GameEvent[]
}

export interface GameEvent {
  type: 'spawn' | 'destroy' | 'damage' | 'powerup' | 'score'
  entityId: string
  data?: unknown
}

interface InputBuffer {
  input: PlayerInput
  tick: number
}

export class NetworkManager {
  private client: WebRTCClient
  private playerId: string = ''
  private roomId: string = ''

  // State
  private currentTick = 0
  private serverTick = 0

  // Input buffering for reconciliation
  private inputBuffer: InputBuffer[] = []
  private readonly MAX_INPUT_BUFFER = 120 // 2 seconds at 60Hz

  // State interpolation
  private stateBuffer: GameStateSnapshot[] = []
  private readonly INTERPOLATION_DELAY = 100 // ms

  // Callbacks
  private onStateUpdate: ((state: GameStateSnapshot) => void) | null = null
  private onEvent: ((event: GameEvent) => void) | null = null

  constructor(signalingUrl: string) {
    this.client = new WebRTCClient({ signalingUrl })

    this.client.onMessage((message) => {
      this.handleMessage(message)
    })
  }

  async joinGame(roomId: string): Promise<string> {
    this.roomId = roomId
    this.playerId = this.generatePlayerId()

    await this.client.connect(roomId, this.playerId)

    return this.playerId
  }

  private generatePlayerId(): string {
    return `player_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`
  }

  // Send player input to server
  sendInput(input: PlayerInput): void {
    if (!this.client.isConnected()) return

    const tick = this.currentTick++

    // Buffer input for reconciliation
    this.inputBuffer.push({ input, tick })

    // Trim old inputs
    if (this.inputBuffer.length > this.MAX_INPUT_BUFFER) {
      this.inputBuffer.shift()
    }

    // Send to server
    this.client.send('input', {
      tick,
      input,
    })
  }

  private handleMessage(message: GameMessage): void {
    switch (message.type) {
      case 'state':
        this.handleStateUpdate(message.data as GameStateSnapshot)
        break
      case 'event':
        this.handleEvent(message.data as GameEvent)
        break
    }
  }

  private handleStateUpdate(snapshot: GameStateSnapshot): void {
    // Update server tick
    this.serverTick = snapshot.tick

    // Buffer state for interpolation
    this.stateBuffer.push(snapshot)

    // Keep only recent states
    const now = performance.now()
    this.stateBuffer = this.stateBuffer.filter(
      (s) => now - s.timestamp < 1000
    )

    // Reconciliation: remove acknowledged inputs
    this.inputBuffer = this.inputBuffer.filter(
      (i) => i.tick > snapshot.tick
    )

    // Notify listeners
    this.onStateUpdate?.(snapshot)
  }

  private handleEvent(event: GameEvent): void {
    this.onEvent?.(event)
  }

  // Get interpolated state for rendering
  getInterpolatedState(): GameStateSnapshot | null {
    if (this.stateBuffer.length < 2) {
      return this.stateBuffer[0] ?? null
    }

    const renderTime = performance.now() - this.INTERPOLATION_DELAY

    // Find the two states to interpolate between
    let before: GameStateSnapshot | null = null
    let after: GameStateSnapshot | null = null

    for (let i = 0; i < this.stateBuffer.length - 1; i++) {
      const a = this.stateBuffer[i]!
      const b = this.stateBuffer[i + 1]!

      if (a.timestamp <= renderTime && b.timestamp >= renderTime) {
        before = a
        after = b
        break
      }
    }

    if (!before || !after) {
      // Fall back to latest state
      return this.stateBuffer[this.stateBuffer.length - 1] ?? null
    }

    // Calculate interpolation factor
    const range = after.timestamp - before.timestamp
    const t = range > 0 ? (renderTime - before.timestamp) / range : 0

    // Interpolate entities
    return this.interpolateSnapshots(before, after, t)
  }

  private interpolateSnapshots(
    a: GameStateSnapshot,
    b: GameStateSnapshot,
    t: number
  ): GameStateSnapshot {
    const interpolatedEntities: EntityState[] = []

    for (const entityB of b.entities) {
      const entityA = a.entities.find((e) => e.id === entityB.id)

      if (entityA) {
        // Interpolate existing entity
        interpolatedEntities.push({
          ...entityB,
          x: this.lerp(entityA.x, entityB.x, t),
          y: this.lerp(entityA.y, entityB.y, t),
          rotation: this.lerpAngle(entityA.rotation, entityB.rotation, t),
        })
      } else {
        // New entity, no interpolation
        interpolatedEntities.push(entityB)
      }
    }

    return {
      tick: b.tick,
      timestamp: performance.now(),
      entities: interpolatedEntities,
      events: b.events,
    }
  }

  private lerp(a: number, b: number, t: number): number {
    return a + (b - a) * t
  }

  private lerpAngle(a: number, b: number, t: number): number {
    // Handle angle wrapping
    let diff = b - a
    while (diff > Math.PI) diff -= Math.PI * 2
    while (diff < -Math.PI) diff += Math.PI * 2
    return a + diff * t
  }

  // Get pending inputs for client-side prediction
  getPendingInputs(): InputBuffer[] {
    return [...this.inputBuffer]
  }

  // Callbacks
  setStateHandler(handler: (state: GameStateSnapshot) => void): void {
    this.onStateUpdate = handler
  }

  setEventHandler(handler: (event: GameEvent) => void): void {
    this.onEvent = handler
  }

  // Stats
  getLatency(): number {
    return this.client.getLatency()
  }

  getServerTick(): number {
    return this.serverTick
  }

  isConnected(): boolean {
    return this.client.isConnected()
  }

  getPlayerId(): string {
    return this.playerId
  }

  disconnect(): void {
    this.client.disconnect()
  }
}
