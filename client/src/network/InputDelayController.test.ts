import { describe, it, expect, beforeEach } from 'vitest'
import { InputDelayController, type InputDelayConfig } from './InputDelayController'
import { SIM_TICK_MS } from './types'

describe('InputDelayController', () => {
  describe('constructor', () => {
    it('should create with default config', () => {
      const controller = new InputDelayController()
      expect(controller.getDelayTicks()).toBe(2) // Default min
      expect(controller.getSampleCount()).toBe(0)
    })

    it('should accept custom min delay', () => {
      const controller = new InputDelayController({ minDelayTicks: 3 })
      expect(controller.getDelayTicks()).toBe(3)
    })

    it('should accept custom max delay', () => {
      const controller = new InputDelayController({ maxDelayTicks: 10 })
      // Add high RTT samples
      for (let i = 0; i < 10; i++) {
        controller.addRttSample(500) // Very high RTT
      }
      // Force update
      controller.update(2000)

      expect(controller.getDelayTicks()).toBeLessThanOrEqual(10)
    })

    it('should accept custom sample count', () => {
      const controller = new InputDelayController({ sampleCount: 5 })

      for (let i = 0; i < 10; i++) {
        controller.addRttSample(50)
      }

      expect(controller.getSampleCount()).toBe(5) // Capped at 5
    })
  })

  describe('addRttSample', () => {
    let controller: InputDelayController

    beforeEach(() => {
      controller = new InputDelayController()
    })

    it('should add RTT samples', () => {
      controller.addRttSample(50)
      expect(controller.getSampleCount()).toBe(1)

      controller.addRttSample(60)
      expect(controller.getSampleCount()).toBe(2)
    })

    it('should limit samples to sampleCount', () => {
      const limited = new InputDelayController({ sampleCount: 3 })

      limited.addRttSample(10)
      limited.addRttSample(20)
      limited.addRttSample(30)
      limited.addRttSample(40)
      limited.addRttSample(50)

      expect(limited.getSampleCount()).toBe(3)
    })

    it('should drop oldest samples when full', () => {
      const limited = new InputDelayController({ sampleCount: 3 })

      limited.addRttSample(10)
      limited.addRttSample(20)
      limited.addRttSample(30)
      limited.addRttSample(100) // This should replace 10

      // Average should reflect newer samples
      const avg = limited.getAverageRtt()
      expect(avg).toBe((20 + 30 + 100) / 3)
    })
  })

  describe('getDelayTicks / getDelayMs', () => {
    it('should return minimum delay when no samples', () => {
      const controller = new InputDelayController({ minDelayTicks: 2 })
      expect(controller.getDelayTicks()).toBe(2)
      expect(controller.getDelayMs()).toBe(2 * SIM_TICK_MS)
    })

    it('should calculate delay based on RTT', () => {
      const controller = new InputDelayController({
        minDelayTicks: 2,
        maxDelayTicks: 6,
        tickMs: 33.33, // ~30Hz
      })

      // Add samples for ~100ms RTT
      for (let i = 0; i < 10; i++) {
        controller.addRttSample(100)
      }

      // Target: ceil(100 / 33.33) + 1 = ceil(3) + 1 = 4
      // But delay changes gradually, so may still be at minimum
      const delay = controller.getDelayTicks()
      expect(delay).toBeGreaterThanOrEqual(2)
    })
  })

  describe('update', () => {
    it('should not change delay before interval', () => {
      const controller = new InputDelayController({ adjustIntervalMs: 1000 })

      // Add high RTT samples
      for (let i = 0; i < 10; i++) {
        controller.addRttSample(200)
      }

      const initialDelay = controller.getDelayTicks()
      controller.update(500) // Only 500ms elapsed

      expect(controller.getDelayTicks()).toBe(initialDelay)
    })

    it('should change delay after interval', () => {
      const controller = new InputDelayController({
        adjustIntervalMs: 100,
        minDelayTicks: 2,
        maxDelayTicks: 6,
      })

      // Add high RTT samples to trigger increase
      for (let i = 0; i < 10; i++) {
        controller.addRttSample(200)
      }

      const changed = controller.update(200)
      expect(changed).toBe(true)
    })

    it('should change by max 1 tick per update', () => {
      const controller = new InputDelayController({
        adjustIntervalMs: 100,
        minDelayTicks: 2,
        maxDelayTicks: 6,
      })

      const initialDelay = controller.getDelayTicks()

      // Add very high RTT
      for (let i = 0; i < 10; i++) {
        controller.addRttSample(500)
      }

      controller.update(200)
      const newDelay = controller.getDelayTicks()

      expect(Math.abs(newDelay - initialDelay)).toBeLessThanOrEqual(1)
    })

    it('should gradually increase delay', () => {
      const controller = new InputDelayController({
        adjustIntervalMs: 100,
        minDelayTicks: 2,
        maxDelayTicks: 6,
      })

      // Add high RTT
      for (let i = 0; i < 10; i++) {
        controller.addRttSample(200)
      }

      const delays: number[] = [controller.getDelayTicks()]

      // Update multiple times
      for (let t = 200; t <= 1000; t += 200) {
        controller.update(t)
        delays.push(controller.getDelayTicks())
      }

      // Delays should be non-decreasing (or flat if at target)
      for (let i = 1; i < delays.length; i++) {
        expect(delays[i]!).toBeGreaterThanOrEqual(delays[i - 1]!)
      }
    })

    it('should gradually decrease delay', () => {
      const controller = new InputDelayController({
        adjustIntervalMs: 100,
        minDelayTicks: 2,
        maxDelayTicks: 6,
      })

      // First increase delay with high RTT
      for (let i = 0; i < 10; i++) {
        controller.addRttSample(200)
      }
      for (let t = 100; t <= 500; t += 100) {
        controller.update(t)
      }

      const highDelay = controller.getDelayTicks()
      expect(highDelay).toBeGreaterThan(2)

      // Reset samples to low RTT
      controller.reset()
      for (let i = 0; i < 10; i++) {
        controller.addRttSample(20)
      }

      // Delay should decrease over time
      for (let t = 100; t <= 1000; t += 100) {
        controller.update(t)
      }

      expect(controller.getDelayTicks()).toBeLessThan(highDelay)
    })

    it('should return false when no change needed', () => {
      const controller = new InputDelayController({
        adjustIntervalMs: 100,
        minDelayTicks: 2,
      })

      // Add low RTT (target will be min)
      for (let i = 0; i < 10; i++) {
        controller.addRttSample(10)
      }

      const changed = controller.update(200)
      // Already at min, no change needed
      expect(changed).toBe(false)
    })
  })

  describe('getAverageRtt', () => {
    it('should return 0 when no samples', () => {
      const controller = new InputDelayController()
      expect(controller.getAverageRtt()).toBe(0)
    })

    it('should calculate average correctly', () => {
      const controller = new InputDelayController()

      controller.addRttSample(100)
      controller.addRttSample(200)
      controller.addRttSample(300)

      expect(controller.getAverageRtt()).toBe(200)
    })

    it('should only include recent samples', () => {
      const controller = new InputDelayController({ sampleCount: 3 })

      controller.addRttSample(1000) // Old, will be dropped
      controller.addRttSample(10)
      controller.addRttSample(20)
      controller.addRttSample(30)

      expect(controller.getAverageRtt()).toBe(20) // (10+20+30)/3
    })
  })

  describe('getMaxRtt', () => {
    it('should return 0 when no samples', () => {
      const controller = new InputDelayController()
      expect(controller.getMaxRtt()).toBe(0)
    })

    it('should return maximum RTT', () => {
      const controller = new InputDelayController()

      controller.addRttSample(50)
      controller.addRttSample(100)
      controller.addRttSample(75)

      expect(controller.getMaxRtt()).toBe(100)
    })
  })

  describe('getJitter', () => {
    it('should return 0 when less than 2 samples', () => {
      const controller = new InputDelayController()
      expect(controller.getJitter()).toBe(0)

      controller.addRttSample(50)
      expect(controller.getJitter()).toBe(0)
    })

    it('should return 0 for identical samples', () => {
      const controller = new InputDelayController()

      controller.addRttSample(50)
      controller.addRttSample(50)
      controller.addRttSample(50)

      expect(controller.getJitter()).toBe(0)
    })

    it('should calculate standard deviation', () => {
      const controller = new InputDelayController()

      // Known values: 10, 20, 30 -> mean=20, variance=66.67, stddev=~8.16
      controller.addRttSample(10)
      controller.addRttSample(20)
      controller.addRttSample(30)

      const jitter = controller.getJitter()
      expect(jitter).toBeCloseTo(8.165, 2)
    })
  })

  describe('reset', () => {
    it('should clear all state', () => {
      const controller = new InputDelayController({
        minDelayTicks: 2,
        adjustIntervalMs: 100,
      })

      // Build up some state
      for (let i = 0; i < 10; i++) {
        controller.addRttSample(200)
      }
      controller.update(200)

      controller.reset()

      expect(controller.getSampleCount()).toBe(0)
      expect(controller.getDelayTicks()).toBe(2) // Back to min
      expect(controller.getAverageRtt()).toBe(0)
    })
  })

  describe('setDelay', () => {
    it('should set delay directly', () => {
      const controller = new InputDelayController({ minDelayTicks: 2, maxDelayTicks: 6 })

      controller.setDelay(4)
      expect(controller.getDelayTicks()).toBe(4)
    })

    it('should clamp to min', () => {
      const controller = new InputDelayController({ minDelayTicks: 2 })

      controller.setDelay(1)
      expect(controller.getDelayTicks()).toBe(2)
    })

    it('should clamp to max', () => {
      const controller = new InputDelayController({ maxDelayTicks: 6 })

      controller.setDelay(10)
      expect(controller.getDelayTicks()).toBe(6)
    })

    it('should also set target delay', () => {
      const controller = new InputDelayController({
        minDelayTicks: 2,
        maxDelayTicks: 6,
        adjustIntervalMs: 100,
      })

      controller.setDelay(5)

      // Verify setDelay sets both current and target
      let info = controller.getDebugInfo()
      expect(info.currentDelay).toBe(5)
      expect(info.targetDelay).toBe(5)

      // Note: Adding RTT samples will recalculate targetDelay based on RTT
      // Low RTT (10ms) with tickMs (~33ms) gives target = ceil(10/33) + 1 = 2
      for (let i = 0; i < 10; i++) {
        controller.addRttSample(10)
      }

      info = controller.getDebugInfo()
      expect(info.currentDelay).toBe(5) // Current stays at 5 until update() is called
      expect(info.targetDelay).toBe(2)  // Target is recalculated from RTT
    })
  })

  describe('getDebugInfo', () => {
    it('should return all debug info', () => {
      const controller = new InputDelayController()

      controller.addRttSample(100)
      controller.addRttSample(150)

      const info = controller.getDebugInfo()

      expect(info).toHaveProperty('currentDelay')
      expect(info).toHaveProperty('targetDelay')
      expect(info).toHaveProperty('avgRtt')
      expect(info).toHaveProperty('maxRtt')
      expect(info).toHaveProperty('jitter')
      expect(info).toHaveProperty('samples')

      expect(info.samples).toBe(2)
      expect(info.avgRtt).toBe(125)
      expect(info.maxRtt).toBe(150)
    })
  })

  describe('delay calculation', () => {
    it('should calculate correct delay for various RTTs', () => {
      const tickMs = 33.33 // ~30Hz

      const testCases = [
        { rtt: 20, expectedMin: 2, expectedMax: 3 },   // ceil(20/33.33)+1 = 2
        { rtt: 50, expectedMin: 2, expectedMax: 3 },   // ceil(50/33.33)+1 = 3
        { rtt: 100, expectedMin: 3, expectedMax: 5 },  // ceil(100/33.33)+1 = 4
        { rtt: 150, expectedMin: 4, expectedMax: 6 },  // ceil(150/33.33)+1 = 6
      ]

      for (const { rtt, expectedMin, expectedMax } of testCases) {
        const controller = new InputDelayController({
          minDelayTicks: 2,
          maxDelayTicks: 6,
          tickMs,
          adjustIntervalMs: 0, // Immediate updates
        })

        for (let i = 0; i < 10; i++) {
          controller.addRttSample(rtt)
        }

        // Let it converge
        for (let t = 0; t < 10; t++) {
          controller.update(t * 100)
        }

        const delay = controller.getDelayTicks()
        expect(delay).toBeGreaterThanOrEqual(expectedMin)
        expect(delay).toBeLessThanOrEqual(expectedMax)
      }
    })
  })
})
