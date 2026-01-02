/**
 * InputBatcher - Adaptive input batching based on network latency
 *
 * SC2-style optimization: Accumulate inputs and send in batches
 * to reduce packet overhead at high latencies.
 *
 * Batch size rules (based on RTT):
 * - < 30ms: batch 1 (send every tick)
 * - 30-60ms: batch 2
 * - 60-100ms: batch 3
 * - > 100ms: batch 4 (max)
 *
 * Max batch delay: ~33ms (1 tick at 30Hz)
 */

import type { FrameInput } from './types.ts'

export interface InputBatcherConfig {
  /** Maximum inputs to batch (default: 4) */
  maxBatchSize?: number
  /** Force flush after this many ms (default: 33ms = 1 tick) */
  maxBatchDelayMs?: number
}

export class InputBatcher {
  private pending: FrameInput[] = []
  private batchSize = 1
  private maxBatchSize: number
  private maxBatchDelayMs: number
  private lastFlushTime = 0

  constructor(config: InputBatcherConfig = {}) {
    this.maxBatchSize = config.maxBatchSize ?? 4
    this.maxBatchDelayMs = config.maxBatchDelayMs ?? 33
  }

  /**
   * Add an input to the batch.
   * Returns inputs to send if batch is ready, otherwise null.
   */
  add(input: FrameInput, currentTime: number): FrameInput[] | null {
    this.pending.push(input)

    // Check if we should flush
    if (this.shouldFlush(currentTime)) {
      return this.flush(currentTime)
    }

    return null
  }

  /**
   * Force flush all pending inputs.
   */
  flush(currentTime: number): FrameInput[] {
    const inputs = this.pending
    this.pending = []
    this.lastFlushTime = currentTime
    return inputs
  }

  /**
   * Check if there are pending inputs.
   */
  hasPending(): boolean {
    return this.pending.length > 0
  }

  /**
   * Get number of pending inputs.
   */
  getPendingCount(): number {
    return this.pending.length
  }

  /**
   * Update batch size based on RTT.
   */
  updateBatchSize(rttMs: number): void {
    if (rttMs < 30) {
      this.batchSize = 1
    } else if (rttMs < 60) {
      this.batchSize = 2
    } else if (rttMs < 100) {
      this.batchSize = 3
    } else {
      this.batchSize = this.maxBatchSize
    }
  }

  /**
   * Get current batch size.
   */
  getBatchSize(): number {
    return this.batchSize
  }

  /**
   * Check if batch is ready to send.
   */
  private shouldFlush(currentTime: number): boolean {
    // Flush if we've reached batch size
    if (this.pending.length >= this.batchSize) {
      return true
    }

    // Flush if max delay exceeded
    if (this.lastFlushTime > 0) {
      const elapsed = currentTime - this.lastFlushTime
      if (elapsed >= this.maxBatchDelayMs) {
        return true
      }
    }

    return false
  }

  /**
   * Reset batcher state.
   */
  reset(): void {
    this.pending = []
    this.batchSize = 1
    this.lastFlushTime = 0
  }
}
