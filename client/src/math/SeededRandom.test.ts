import { describe, it, expect } from 'vitest'
import { SeededRandom } from './SeededRandom.ts'

describe('SeededRandom', () => {
  describe('constructor', () => {
    it('should initialize with seed', () => {
      const rng = new SeededRandom(12345)
      expect(rng.getSeed()).toBe(12345)
    })

    it('should default to seed 1 if given 0', () => {
      const rng = new SeededRandom(0)
      expect(rng.getSeed()).toBe(1)
    })
  })

  describe('determinism', () => {
    it('should produce identical sequences for same seed', () => {
      const rng1 = new SeededRandom(42)
      const rng2 = new SeededRandom(42)

      for (let i = 0; i < 100; i++) {
        expect(rng1.next()).toBe(rng2.next())
      }
    })

    it('should produce different sequences for different seeds', () => {
      const rng1 = new SeededRandom(42)
      const rng2 = new SeededRandom(43)

      const seq1 = Array.from({ length: 10 }, () => rng1.next())
      const seq2 = Array.from({ length: 10 }, () => rng2.next())

      expect(seq1).not.toEqual(seq2)
    })
  })

  describe('next', () => {
    it('should return values between 0 and 1', () => {
      const rng = new SeededRandom(12345)

      for (let i = 0; i < 1000; i++) {
        const value = rng.next()
        expect(value).toBeGreaterThanOrEqual(0)
        expect(value).toBeLessThan(1)
      }
    })

    it('should update internal state', () => {
      const rng = new SeededRandom(12345)
      const initialSeed = rng.getSeed()
      rng.next()
      expect(rng.getSeed()).not.toBe(initialSeed)
    })
  })

  describe('nextInt', () => {
    it('should return integers in range [0, max)', () => {
      const rng = new SeededRandom(12345)

      for (let i = 0; i < 1000; i++) {
        const value = rng.nextInt(10)
        expect(value).toBeGreaterThanOrEqual(0)
        expect(value).toBeLessThan(10)
        expect(Number.isInteger(value)).toBe(true)
      }
    })

    it('should return 0 when max is 1', () => {
      const rng = new SeededRandom(12345)

      for (let i = 0; i < 100; i++) {
        expect(rng.nextInt(1)).toBe(0)
      }
    })
  })

  describe('nextRange', () => {
    it('should return values in range [min, max)', () => {
      const rng = new SeededRandom(12345)

      for (let i = 0; i < 1000; i++) {
        const value = rng.nextRange(5, 15)
        expect(value).toBeGreaterThanOrEqual(5)
        expect(value).toBeLessThan(15)
      }
    })

    it('should work with negative ranges', () => {
      const rng = new SeededRandom(12345)

      for (let i = 0; i < 100; i++) {
        const value = rng.nextRange(-10, -5)
        expect(value).toBeGreaterThanOrEqual(-10)
        expect(value).toBeLessThan(-5)
      }
    })
  })

  describe('nextBool', () => {
    it('should return boolean values', () => {
      const rng = new SeededRandom(12345)

      for (let i = 0; i < 100; i++) {
        const value = rng.nextBool()
        expect(typeof value).toBe('boolean')
      }
    })

    it('should respect probability parameter', () => {
      const rng = new SeededRandom(12345)
      let trueCount = 0
      const iterations = 10000

      for (let i = 0; i < iterations; i++) {
        if (rng.nextBool(0.7)) trueCount++
      }

      // Should be roughly 70% true (with some variance)
      const ratio = trueCount / iterations
      expect(ratio).toBeGreaterThan(0.65)
      expect(ratio).toBeLessThan(0.75)
    })
  })

  describe('pick', () => {
    it('should return element from array', () => {
      const rng = new SeededRandom(12345)
      const array = ['a', 'b', 'c', 'd', 'e']

      for (let i = 0; i < 100; i++) {
        const picked = rng.pick(array)
        expect(array).toContain(picked)
      }
    })

    it('should return undefined for empty array', () => {
      const rng = new SeededRandom(12345)
      expect(rng.pick([])).toBeUndefined()
    })

    it('should be deterministic', () => {
      const array = ['a', 'b', 'c', 'd', 'e']
      const rng1 = new SeededRandom(42)
      const rng2 = new SeededRandom(42)

      for (let i = 0; i < 50; i++) {
        expect(rng1.pick(array)).toBe(rng2.pick(array))
      }
    })
  })

  describe('shuffle', () => {
    it('should shuffle array in place', () => {
      const rng = new SeededRandom(12345)
      const array = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
      const original = [...array]
      rng.shuffle(array)

      // Should have same elements
      expect(array.sort()).toEqual(original.sort())
    })

    it('should return the same array instance', () => {
      const rng = new SeededRandom(12345)
      const array = [1, 2, 3]
      const result = rng.shuffle(array)
      expect(result).toBe(array)
    })

    it('should be deterministic', () => {
      const rng1 = new SeededRandom(42)
      const rng2 = new SeededRandom(42)
      const array1 = [1, 2, 3, 4, 5]
      const array2 = [1, 2, 3, 4, 5]

      rng1.shuffle(array1)
      rng2.shuffle(array2)

      expect(array1).toEqual(array2)
    })
  })

  describe('clone', () => {
    it('should create independent copy with same state', () => {
      const rng = new SeededRandom(12345)
      rng.next()
      rng.next()

      const clone = rng.clone()

      expect(clone.getSeed()).toBe(rng.getSeed())

      // Advancing one should not affect the other
      const originalValue = rng.next()
      const cloneValue = clone.next()

      expect(originalValue).toBe(cloneValue)
    })
  })
})
