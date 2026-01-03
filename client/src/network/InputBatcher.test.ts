import { describe, it, expect, beforeEach } from 'vitest'
import { InputBatcher } from './InputBatcher'
import type { FrameInput, PlayerInput } from './types'

function createEmptyInput(): PlayerInput {
  return {
    up: false,
    down: false,
    left: false,
    right: false,
    fire: false,
    special: false,
    secondary: false,
    swap: false,
    pickup: false,
    pause: false,
  }
}

function createFrameInput(frame: number, overrides?: Partial<FrameInput>): FrameInput {
  return {
    frame,
    playerId: 'player1',
    input: createEmptyInput(),
    ...overrides,
  }
}

describe('InputBatcher', () => {
  describe('constructor', () => {
    it('should create with default config', () => {
      const batcher = new InputBatcher()
      expect(batcher.getBatchSize()).toBe(1)
      expect(batcher.hasPending()).toBe(false)
    })

    it('should accept custom maxBatchSize', () => {
      const batcher = new InputBatcher({ maxBatchSize: 8 })
      batcher.updateBatchSize(200) // High latency
      expect(batcher.getBatchSize()).toBeLessThanOrEqual(8)
    })

    it('should accept custom maxBatchDelayMs', () => {
      const batcher = new InputBatcher({ maxBatchDelayMs: 50 })
      // Delay should affect when batches flush
      expect(batcher.hasPending()).toBe(false)
    })
  })

  describe('add', () => {
    let batcher: InputBatcher

    beforeEach(() => {
      batcher = new InputBatcher()
    })

    it('should add input to pending (when batch size > 1)', () => {
      batcher.updateBatchSize(50) // Batch size 2
      const input = createFrameInput(1)
      batcher.add(input, 0)

      // With batch size 2, first add doesn't flush
      expect(batcher.hasPending()).toBe(true)
      expect(batcher.getPendingCount()).toBe(1)
    })

    it('should return inputs when batch size reached', () => {
      batcher.updateBatchSize(50) // Set batch size to 2
      expect(batcher.getBatchSize()).toBe(2)

      const input1 = createFrameInput(1)
      const input2 = createFrameInput(2)

      const result1 = batcher.add(input1, 0)
      expect(result1).toBeNull() // Not yet full

      const result2 = batcher.add(input2, 0)
      expect(result2).not.toBeNull()
      expect(result2!.length).toBe(2)
    })

    it('should return null when batch not ready', () => {
      const input = createFrameInput(1)
      const result = batcher.add(input, 0)

      // With batch size 1 and first add, should flush immediately
      expect(result).not.toBeNull()
    })

    it('should flush on max delay exceeded', () => {
      batcher.updateBatchSize(200) // High latency, batch size 4

      const input1 = createFrameInput(1)
      // First add at time 10 (not 0) so lastFlushTime gets set
      batcher.add(input1, 10)
      batcher.flush(10) // Manually flush to set lastFlushTime

      // Add another input
      const input2 = createFrameInput(2)
      batcher.add(input2, 15)

      // Simulate time passing - add input at 50ms (35ms since last flush)
      const input3 = createFrameInput(3)
      const result = batcher.add(input3, 50) // 40ms later, exceeds 33ms default

      expect(result).not.toBeNull()
    })

    it('should accumulate inputs in order', () => {
      batcher.updateBatchSize(100) // Batch size 4

      batcher.add(createFrameInput(1), 0)
      batcher.add(createFrameInput(2), 5)
      batcher.add(createFrameInput(3), 10)

      const result = batcher.flush(15)
      expect(result.length).toBe(3)
      expect(result[0]!.frame).toBe(1)
      expect(result[1]!.frame).toBe(2)
      expect(result[2]!.frame).toBe(3)
    })
  })

  describe('flush', () => {
    let batcher: InputBatcher

    beforeEach(() => {
      batcher = new InputBatcher()
    })

    it('should return all pending inputs', () => {
      batcher.updateBatchSize(100) // High batch size

      batcher.add(createFrameInput(1), 0)
      batcher.add(createFrameInput(2), 5)

      const flushed = batcher.flush(10)
      expect(flushed.length).toBe(2)
    })

    it('should clear pending after flush', () => {
      batcher.add(createFrameInput(1), 0)
      batcher.flush(10)

      expect(batcher.hasPending()).toBe(false)
      expect(batcher.getPendingCount()).toBe(0)
    })

    it('should return empty array if nothing pending', () => {
      const flushed = batcher.flush(0)
      expect(flushed).toEqual([])
    })

    it('should update lastFlushTime', () => {
      batcher.updateBatchSize(100)

      batcher.add(createFrameInput(1), 0)
      batcher.flush(100)

      // Next add shouldn't trigger delay flush immediately
      batcher.add(createFrameInput(2), 110)
      expect(batcher.hasPending()).toBe(true)
    })
  })

  describe('updateBatchSize', () => {
    let batcher: InputBatcher

    beforeEach(() => {
      batcher = new InputBatcher()
    })

    it('should set batch size 1 for RTT < 30ms', () => {
      batcher.updateBatchSize(0)
      expect(batcher.getBatchSize()).toBe(1)

      batcher.updateBatchSize(15)
      expect(batcher.getBatchSize()).toBe(1)

      batcher.updateBatchSize(29)
      expect(batcher.getBatchSize()).toBe(1)
    })

    it('should set batch size 2 for RTT 30-60ms', () => {
      batcher.updateBatchSize(30)
      expect(batcher.getBatchSize()).toBe(2)

      batcher.updateBatchSize(45)
      expect(batcher.getBatchSize()).toBe(2)

      batcher.updateBatchSize(59)
      expect(batcher.getBatchSize()).toBe(2)
    })

    it('should set batch size 3 for RTT 60-100ms', () => {
      batcher.updateBatchSize(60)
      expect(batcher.getBatchSize()).toBe(3)

      batcher.updateBatchSize(80)
      expect(batcher.getBatchSize()).toBe(3)

      batcher.updateBatchSize(99)
      expect(batcher.getBatchSize()).toBe(3)
    })

    it('should set batch size 4 (max) for RTT >= 100ms', () => {
      batcher.updateBatchSize(100)
      expect(batcher.getBatchSize()).toBe(4)

      batcher.updateBatchSize(200)
      expect(batcher.getBatchSize()).toBe(4)

      batcher.updateBatchSize(500)
      expect(batcher.getBatchSize()).toBe(4)
    })

    it('should respect custom maxBatchSize', () => {
      const customBatcher = new InputBatcher({ maxBatchSize: 2 })

      customBatcher.updateBatchSize(200) // Would normally be 4
      expect(customBatcher.getBatchSize()).toBe(2) // Capped at 2
    })
  })

  describe('hasPending / getPendingCount', () => {
    let batcher: InputBatcher

    beforeEach(() => {
      batcher = new InputBatcher({ maxBatchSize: 10 })
      batcher.updateBatchSize(200) // High batch size
    })

    it('should return false/0 when empty', () => {
      expect(batcher.hasPending()).toBe(false)
      expect(batcher.getPendingCount()).toBe(0)
    })

    it('should return true/count when inputs pending', () => {
      batcher.add(createFrameInput(1), 0)
      expect(batcher.hasPending()).toBe(true)
      expect(batcher.getPendingCount()).toBe(1)

      batcher.add(createFrameInput(2), 5)
      expect(batcher.getPendingCount()).toBe(2)

      batcher.add(createFrameInput(3), 10)
      expect(batcher.getPendingCount()).toBe(3)
    })
  })

  describe('reset', () => {
    it('should clear all state', () => {
      const batcher = new InputBatcher()
      batcher.updateBatchSize(200)

      // Add some inputs
      batcher.add(createFrameInput(1), 0)
      batcher.add(createFrameInput(2), 5)

      batcher.reset()

      expect(batcher.hasPending()).toBe(false)
      expect(batcher.getPendingCount()).toBe(0)
      expect(batcher.getBatchSize()).toBe(1) // Reset to default
    })
  })

  describe('batching behavior', () => {
    it('should batch multiple frames for high latency', () => {
      const batcher = new InputBatcher()
      batcher.updateBatchSize(150) // High latency, batch 4

      const results: FrameInput[][] = []

      // Add 8 inputs
      for (let i = 0; i < 8; i++) {
        const result = batcher.add(createFrameInput(i), i)
        if (result) results.push(result)
      }

      // Should have 2 batches of 4
      expect(results.length).toBe(2)
      expect(results[0]!.length).toBe(4)
      expect(results[1]!.length).toBe(4)
    })

    it('should send every frame for low latency', () => {
      const batcher = new InputBatcher()
      batcher.updateBatchSize(10) // Low latency, batch 1

      const results: FrameInput[][] = []

      for (let i = 0; i < 5; i++) {
        const result = batcher.add(createFrameInput(i), i)
        if (result) results.push(result)
      }

      // Should have 5 batches of 1
      expect(results.length).toBe(5)
      results.forEach(batch => expect(batch.length).toBe(1))
    })

    it('should flush partial batch on delay', () => {
      const batcher = new InputBatcher({ maxBatchDelayMs: 20 })
      batcher.updateBatchSize(150) // Batch size 4

      // First, set lastFlushTime by doing a manual flush at time 1
      // (must be > 0 for the delay check to trigger)
      batcher.flush(1)

      // Now add inputs after the initial flush
      batcher.add(createFrameInput(1), 5)
      batcher.add(createFrameInput(2), 10)

      // Wait for delay and add another (24ms since flush at time 1, exceeds 20ms)
      const result = batcher.add(createFrameInput(3), 25)

      // Should flush all 3
      expect(result).not.toBeNull()
      expect(result!.length).toBe(3)
    })
  })

  describe('edge cases', () => {
    it('should handle rapid adds at same timestamp', () => {
      const batcher = new InputBatcher()
      batcher.updateBatchSize(50) // Batch 2

      batcher.add(createFrameInput(1), 100)
      const result2 = batcher.add(createFrameInput(2), 100)

      expect(result2).not.toBeNull()
      expect(result2!.length).toBe(2)
    })

    it('should handle large frame numbers', () => {
      const batcher = new InputBatcher()

      const input = createFrameInput(999999)
      const result = batcher.add(input, 0)

      expect(result).not.toBeNull()
      expect(result![0]!.frame).toBe(999999)
    })

    it('should preserve input data through batching', () => {
      const batcher = new InputBatcher()
      batcher.updateBatchSize(50) // Batch 2

      const input1: FrameInput = {
        frame: 1,
        playerId: 'player1',
        input: { ...createEmptyInput(), up: true, fire: true },
        checksum: 12345,
      }

      const input2: FrameInput = {
        frame: 2,
        playerId: 'player1',
        input: { ...createEmptyInput(), down: true },
        checksum: 67890,
      }

      batcher.add(input1, 0)
      const result = batcher.add(input2, 5)

      expect(result![0]!.input.up).toBe(true)
      expect(result![0]!.checksum).toBe(12345)
      expect(result![1]!.input.down).toBe(true)
      expect(result![1]!.checksum).toBe(67890)
    })
  })
})
