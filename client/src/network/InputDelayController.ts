/**
 * InputDelayController - Dynamic input delay based on RTT
 *
 * SC2-style optimization: Adjust input delay (command latency hiding)
 * based on measured round-trip time to peers.
 *
 * Formula: delay = ceil(avgRtt / tickMs) + 1
 * - Min: 2 ticks (66ms at 30Hz)
 * - Max: 6 ticks (200ms at 30Hz)
 * - Changes by max 1 tick per second (smooth transitions)
 */

import { SIM_TICK_MS } from './types.ts'

export interface InputDelayConfig {
  /** Minimum delay in ticks (default: 2) */
  minDelayTicks?: number
  /** Maximum delay in ticks (default: 6) */
  maxDelayTicks?: number
  /** Number of RTT samples to average (default: 10) */
  sampleCount?: number
  /** How often delay can change, in ms (default: 1000) */
  adjustIntervalMs?: number
  /** Simulation tick duration in ms (default: SIM_TICK_MS) */
  tickMs?: number
}

export class InputDelayController {
  private rttSamples: number[] = []
  private currentDelay: number
  private targetDelay: number
  private lastAdjustTime = 0

  private readonly minDelayTicks: number
  private readonly maxDelayTicks: number
  private readonly sampleCount: number
  private readonly adjustIntervalMs: number
  private readonly tickMs: number

  constructor(config: InputDelayConfig = {}) {
    this.minDelayTicks = config.minDelayTicks ?? 2
    this.maxDelayTicks = config.maxDelayTicks ?? 6
    this.sampleCount = config.sampleCount ?? 10
    this.adjustIntervalMs = config.adjustIntervalMs ?? 1000
    this.tickMs = config.tickMs ?? SIM_TICK_MS

    // Start with minimum delay
    this.currentDelay = this.minDelayTicks
    this.targetDelay = this.minDelayTicks
  }

  /**
   * Add an RTT sample from a peer.
   */
  addRttSample(rttMs: number): void {
    this.rttSamples.push(rttMs)

    // Keep only recent samples
    if (this.rttSamples.length > this.sampleCount) {
      this.rttSamples.shift()
    }

    // Recalculate target delay
    this.updateTargetDelay()
  }

  /**
   * Get the current input delay in ticks.
   * Call this in tick() to get delay for scheduling inputs.
   */
  getDelayTicks(): number {
    return this.currentDelay
  }

  /**
   * Get the current input delay in milliseconds.
   */
  getDelayMs(): number {
    return this.currentDelay * this.tickMs
  }

  /**
   * Update the delay smoothly over time.
   * Call this periodically (e.g., every tick).
   */
  update(currentTime: number): boolean {
    // Only adjust once per interval
    if (currentTime - this.lastAdjustTime < this.adjustIntervalMs) {
      return false
    }

    this.lastAdjustTime = currentTime

    // Gradually move toward target (max 1 tick per adjustment)
    if (this.currentDelay < this.targetDelay) {
      this.currentDelay++
      return true
    } else if (this.currentDelay > this.targetDelay) {
      this.currentDelay--
      return true
    }

    return false
  }

  /**
   * Get the average RTT from samples.
   */
  getAverageRtt(): number {
    if (this.rttSamples.length === 0) return 0
    const sum = this.rttSamples.reduce((a, b) => a + b, 0)
    return sum / this.rttSamples.length
  }

  /**
   * Get the maximum RTT from recent samples.
   * Useful for worst-case planning.
   */
  getMaxRtt(): number {
    if (this.rttSamples.length === 0) return 0
    return Math.max(...this.rttSamples)
  }

  /**
   * Get jitter (RTT variance).
   */
  getJitter(): number {
    if (this.rttSamples.length < 2) return 0
    const avg = this.getAverageRtt()
    const variance =
      this.rttSamples.reduce((sum, rtt) => sum + Math.pow(rtt - avg, 2), 0) /
      this.rttSamples.length
    return Math.sqrt(variance)
  }

  /**
   * Get number of RTT samples collected.
   */
  getSampleCount(): number {
    return this.rttSamples.length
  }

  /**
   * Reset the controller.
   */
  reset(): void {
    this.rttSamples = []
    this.currentDelay = this.minDelayTicks
    this.targetDelay = this.minDelayTicks
    this.lastAdjustTime = 0
  }

  /**
   * Force set delay (for testing or manual override).
   */
  setDelay(ticks: number): void {
    this.currentDelay = Math.max(
      this.minDelayTicks,
      Math.min(this.maxDelayTicks, ticks)
    )
    this.targetDelay = this.currentDelay
  }

  /**
   * Calculate target delay from RTT.
   */
  private updateTargetDelay(): void {
    const avgRtt = this.getAverageRtt()
    if (avgRtt === 0) return

    // Add 1 tick buffer for jitter
    const jitterBuffer = 1
    const ticksNeeded = Math.ceil(avgRtt / this.tickMs) + jitterBuffer

    // Clamp to valid range
    this.targetDelay = Math.max(
      this.minDelayTicks,
      Math.min(this.maxDelayTicks, ticksNeeded)
    )
  }

  /**
   * Get debug info.
   */
  getDebugInfo(): {
    currentDelay: number
    targetDelay: number
    avgRtt: number
    maxRtt: number
    jitter: number
    samples: number
  } {
    return {
      currentDelay: this.currentDelay,
      targetDelay: this.targetDelay,
      avgRtt: this.getAverageRtt(),
      maxRtt: this.getMaxRtt(),
      jitter: this.getJitter(),
      samples: this.rttSamples.length,
    }
  }
}
