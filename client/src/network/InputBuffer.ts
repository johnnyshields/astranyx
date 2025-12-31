/**
 * InputBuffer - Manages frame inputs for lockstep netcode
 *
 * Responsibilities:
 * - Store inputs per frame per player
 * - Track which frames have all inputs ready
 * - Pre-seed initial frames with empty inputs
 * - Cleanup old frames to prevent memory leaks
 * - Compare checksums for desync detection
 */

import type { PlayerInput, FrameInput, GameEvent } from './types.ts'
import { emptyInput } from './types.ts'

export interface InputBufferConfig {
  inputDelay: number
  playerCount: number
  playerOrder: Map<string, number>
  retentionFrames?: number  // How many frames to keep (default: 60)
}

export class InputBuffer {
  private config: InputBufferConfig

  // frame -> player_id -> input
  private buffer: Map<number, Map<string, FrameInput>> = new Map()

  // Checksum storage for desync detection
  // frame -> player_id -> checksum
  private checksumBuffer: Map<number, Map<string, number>> = new Map()

  // Last known checksum for local player
  private lastLocalChecksum = 0

  constructor(config: InputBufferConfig) {
    this.config = {
      ...config,
      retentionFrames: config.retentionFrames ?? 60,
    }
  }

  /**
   * Reset buffer and pre-seed with empty inputs for initial frames
   */
  reset(): void {
    this.buffer.clear()
    this.checksumBuffer.clear()
    this.lastLocalChecksum = 0

    // Pre-seed frames 0 to inputDelay-1 with empty inputs
    const empty = emptyInput()
    for (let frame = 0; frame < this.config.inputDelay; frame++) {
      const frameInputs = new Map<string, FrameInput>()
      for (const [playerId] of this.config.playerOrder) {
        frameInputs.set(playerId, {
          frame,
          playerId,
          input: empty,
        })
      }
      this.buffer.set(frame, frameInputs)
    }
  }

  /**
   * Store an input for a specific frame and player
   */
  storeInput(frameInput: FrameInput): void {
    let frameInputs = this.buffer.get(frameInput.frame)
    if (!frameInputs) {
      frameInputs = new Map()
      this.buffer.set(frameInput.frame, frameInputs)
    }
    frameInputs.set(frameInput.playerId, frameInput)

    // Store checksum if present
    if (frameInput.checksum !== undefined) {
      let checksums = this.checksumBuffer.get(frameInput.frame)
      if (!checksums) {
        checksums = new Map()
        this.checksumBuffer.set(frameInput.frame, checksums)
      }
      checksums.set(frameInput.playerId, frameInput.checksum)
    }
  }

  /**
   * Get all inputs for a frame
   */
  getFrameInputs(frame: number): Map<string, FrameInput> | undefined {
    return this.buffer.get(frame)
  }

  /**
   * Check if a frame has inputs from all players
   */
  hasAllInputs(frame: number): boolean {
    const frameInputs = this.buffer.get(frame)
    if (!frameInputs) return false
    return frameInputs.size >= this.config.playerCount
  }

  /**
   * Get inputs and events for a frame in deterministic order
   * Returns null if not all inputs are ready
   */
  getOrderedInputs(frame: number): { inputs: Map<string, PlayerInput>; events: GameEvent[] } | null {
    if (!this.hasAllInputs(frame)) return null

    const frameInputs = this.buffer.get(frame)!
    const orderedInputs = new Map<string, PlayerInput>()
    const allEvents: GameEvent[] = []

    // Iterate in player order for determinism
    for (const [playerId] of this.config.playerOrder) {
      const input = frameInputs.get(playerId)
      if (input) {
        orderedInputs.set(playerId, input.input)
        if (input.events) {
          allEvents.push(...input.events)
        }
      }
    }

    return { inputs: orderedInputs, events: allEvents }
  }

  /**
   * Check for checksum mismatches at a frame
   * Returns array of mismatches: { playerId, localChecksum, remoteChecksum }
   */
  checkDesync(frame: number, localPlayerId: string): Array<{
    playerId: string
    localChecksum: number
    remoteChecksum: number
  }> {
    const checksums = this.checksumBuffer.get(frame)
    if (!checksums) return []

    const localChecksum = checksums.get(localPlayerId)
    if (localChecksum === undefined) return []

    const mismatches: Array<{
      playerId: string
      localChecksum: number
      remoteChecksum: number
    }> = []

    for (const [playerId, checksum] of checksums) {
      if (playerId === localPlayerId) continue
      if (checksum !== localChecksum) {
        mismatches.push({
          playerId,
          localChecksum,
          remoteChecksum: checksum,
        })
      }
    }

    return mismatches
  }

  /**
   * Update local checksum
   */
  setLocalChecksum(checksum: number): void {
    this.lastLocalChecksum = checksum
  }

  /**
   * Get last local checksum
   */
  getLocalChecksum(): number {
    return this.lastLocalChecksum
  }

  /**
   * Cleanup frames older than confirmedFrame - retentionFrames
   */
  cleanup(confirmedFrame: number): void {
    const minFrame = confirmedFrame - this.config.retentionFrames!

    for (const frame of this.buffer.keys()) {
      if (frame < minFrame) {
        this.buffer.delete(frame)
      }
    }

    for (const frame of this.checksumBuffer.keys()) {
      if (frame < minFrame) {
        this.checksumBuffer.delete(frame)
      }
    }
  }

  /**
   * Check if an input exists for a frame and player
   */
  hasInput(frame: number, playerId: string): boolean {
    const frameInputs = this.buffer.get(frame)
    return frameInputs?.has(playerId) ?? false
  }

  /**
   * Get count of inputs for a frame
   */
  getInputCount(frame: number): number {
    return this.buffer.get(frame)?.size ?? 0
  }

  /**
   * Get the input delay configuration
   */
  getInputDelay(): number {
    return this.config.inputDelay
  }

  /**
   * Get all buffered frame numbers
   */
  getBufferedFrames(): number[] {
    return Array.from(this.buffer.keys()).sort((a, b) => a - b)
  }

  /**
   * Get buffer size (number of frames stored)
   */
  size(): number {
    return this.buffer.size
  }
}
