import { describe, it, expect } from 'vitest'
import { FixedPoint, toFixed, fromFixed } from './FixedPoint.ts'

describe('FixedPoint', () => {
  describe('constants', () => {
    it('should have correct SHIFT value', () => {
      expect(FixedPoint.SHIFT).toBe(16)
    })

    it('should have correct ONE value', () => {
      expect(FixedPoint.ONE).toBe(65536) // 2^16
    })

    it('should have correct HALF value', () => {
      expect(FixedPoint.HALF).toBe(32768) // 2^15
    })
  })

  describe('fromFloat / toFloat', () => {
    it('should convert float to fixed and back', () => {
      const values = [0, 1, -1, 0.5, -0.5, 100.25, -100.75, 0.001]

      for (const value of values) {
        const fixed = FixedPoint.fromFloat(value)
        const back = FixedPoint.toFloat(fixed)
        expect(back).toBeCloseTo(value, 4)
      }
    })

    it('should preserve integers exactly', () => {
      for (let i = -100; i <= 100; i++) {
        const fixed = FixedPoint.fromFloat(i)
        const back = FixedPoint.toFloat(fixed)
        expect(back).toBe(i)
      }
    })
  })

  describe('fromInt / toInt', () => {
    it('should convert integer to fixed and back', () => {
      for (let i = -100; i <= 100; i++) {
        const fixed = FixedPoint.fromInt(i)
        const back = FixedPoint.toInt(fixed)
        expect(back).toBe(i)
      }
    })

    it('should truncate fractional parts', () => {
      const fixed = FixedPoint.fromFloat(3.9)
      expect(FixedPoint.toInt(fixed)).toBe(3)
    })

    it('should handle negative values correctly', () => {
      const fixed = FixedPoint.fromFloat(-3.9)
      expect(FixedPoint.toInt(fixed)).toBe(-4) // Right shift preserves sign
    })
  })

  describe('round / floor / ceil', () => {
    it('should round correctly', () => {
      expect(FixedPoint.toFloat(FixedPoint.round(FixedPoint.fromFloat(1.4)))).toBe(1)
      expect(FixedPoint.toFloat(FixedPoint.round(FixedPoint.fromFloat(1.6)))).toBe(2)
      expect(FixedPoint.toFloat(FixedPoint.round(FixedPoint.fromFloat(1.5)))).toBe(2)
    })

    it('should floor correctly', () => {
      expect(FixedPoint.toFloat(FixedPoint.floor(FixedPoint.fromFloat(1.9)))).toBe(1)
      expect(FixedPoint.toFloat(FixedPoint.floor(FixedPoint.fromFloat(-1.1)))).toBe(-2)
    })

    it('should ceil correctly', () => {
      expect(FixedPoint.toFloat(FixedPoint.ceil(FixedPoint.fromFloat(1.1)))).toBe(2)
      expect(FixedPoint.toFloat(FixedPoint.ceil(FixedPoint.fromFloat(-1.9)))).toBe(-1)
    })
  })

  describe('frac', () => {
    it('should return fractional part', () => {
      const fixed = FixedPoint.fromFloat(3.75)
      const frac = FixedPoint.frac(fixed)
      expect(FixedPoint.toFloat(frac)).toBeCloseTo(0.75, 4)
    })

    it('should return 0 for integers', () => {
      const fixed = FixedPoint.fromFloat(5)
      expect(FixedPoint.frac(fixed)).toBe(0)
    })
  })

  describe('arithmetic', () => {
    describe('add', () => {
      it('should add two fixed-point numbers', () => {
        const a = FixedPoint.fromFloat(3.5)
        const b = FixedPoint.fromFloat(2.25)
        const result = FixedPoint.add(a, b)
        expect(FixedPoint.toFloat(result)).toBeCloseTo(5.75, 4)
      })
    })

    describe('sub', () => {
      it('should subtract two fixed-point numbers', () => {
        const a = FixedPoint.fromFloat(5.5)
        const b = FixedPoint.fromFloat(2.25)
        const result = FixedPoint.sub(a, b)
        expect(FixedPoint.toFloat(result)).toBeCloseTo(3.25, 4)
      })
    })

    describe('mul', () => {
      it('should multiply two fixed-point numbers', () => {
        const a = FixedPoint.fromFloat(3)
        const b = FixedPoint.fromFloat(4)
        const result = FixedPoint.mul(a, b)
        expect(FixedPoint.toFloat(result)).toBeCloseTo(12, 4)
      })

      it('should handle fractional multiplication', () => {
        const a = FixedPoint.fromFloat(2.5)
        const b = FixedPoint.fromFloat(4)
        const result = FixedPoint.mul(a, b)
        expect(FixedPoint.toFloat(result)).toBeCloseTo(10, 4)
      })

      it('should handle negative numbers', () => {
        const a = FixedPoint.fromFloat(-3)
        const b = FixedPoint.fromFloat(4)
        const result = FixedPoint.mul(a, b)
        expect(FixedPoint.toFloat(result)).toBeCloseTo(-12, 4)
      })
    })

    describe('div', () => {
      it('should divide two fixed-point numbers', () => {
        const a = FixedPoint.fromFloat(10)
        const b = FixedPoint.fromFloat(4)
        const result = FixedPoint.div(a, b)
        expect(FixedPoint.toFloat(result)).toBeCloseTo(2.5, 4)
      })

      it('should handle division by zero', () => {
        const a = FixedPoint.fromFloat(10)
        const b = FixedPoint.fromFloat(0)
        const result = FixedPoint.div(a, b)
        expect(result).toBe(Number.MAX_SAFE_INTEGER)
      })

      it('should handle negative division by zero', () => {
        const a = FixedPoint.fromFloat(-10)
        const b = FixedPoint.fromFloat(0)
        const result = FixedPoint.div(a, b)
        expect(result).toBe(Number.MIN_SAFE_INTEGER)
      })
    })
  })

  describe('abs', () => {
    it('should return absolute value', () => {
      expect(FixedPoint.toFloat(FixedPoint.abs(FixedPoint.fromFloat(-5)))).toBe(5)
      expect(FixedPoint.toFloat(FixedPoint.abs(FixedPoint.fromFloat(5)))).toBe(5)
      expect(FixedPoint.toFloat(FixedPoint.abs(FixedPoint.fromFloat(0)))).toBe(0)
    })
  })

  describe('min / max', () => {
    it('should return minimum value', () => {
      const a = FixedPoint.fromFloat(3)
      const b = FixedPoint.fromFloat(5)
      expect(FixedPoint.toFloat(FixedPoint.min(a, b))).toBe(3)
    })

    it('should return maximum value', () => {
      const a = FixedPoint.fromFloat(3)
      const b = FixedPoint.fromFloat(5)
      expect(FixedPoint.toFloat(FixedPoint.max(a, b))).toBe(5)
    })
  })

  describe('clamp', () => {
    it('should clamp value within range', () => {
      const min = FixedPoint.fromFloat(0)
      const max = FixedPoint.fromFloat(10)

      expect(FixedPoint.toFloat(FixedPoint.clamp(FixedPoint.fromFloat(-5), min, max))).toBe(0)
      expect(FixedPoint.toFloat(FixedPoint.clamp(FixedPoint.fromFloat(5), min, max))).toBe(5)
      expect(FixedPoint.toFloat(FixedPoint.clamp(FixedPoint.fromFloat(15), min, max))).toBe(10)
    })
  })

  describe('lerp', () => {
    it('should interpolate between two values', () => {
      const a = FixedPoint.fromFloat(0)
      const b = FixedPoint.fromFloat(10)
      const t = FixedPoint.fromFloat(0.5)

      expect(FixedPoint.toFloat(FixedPoint.lerp(a, b, t))).toBeCloseTo(5, 2)
    })

    it('should return start value at t=0', () => {
      const a = FixedPoint.fromFloat(5)
      const b = FixedPoint.fromFloat(15)
      const t = FixedPoint.fromFloat(0)

      expect(FixedPoint.toFloat(FixedPoint.lerp(a, b, t))).toBeCloseTo(5, 4)
    })

    it('should return end value at t=1', () => {
      const a = FixedPoint.fromFloat(5)
      const b = FixedPoint.fromFloat(15)
      const t = FixedPoint.fromFloat(1)

      expect(FixedPoint.toFloat(FixedPoint.lerp(a, b, t))).toBeCloseTo(15, 2)
    })
  })

  describe('sign', () => {
    it('should return sign of number', () => {
      expect(FixedPoint.sign(FixedPoint.fromFloat(5))).toBe(1)
      expect(FixedPoint.sign(FixedPoint.fromFloat(-5))).toBe(-1)
      expect(FixedPoint.sign(FixedPoint.fromFloat(0))).toBe(0)
    })
  })

  describe('sqrt', () => {
    it('should calculate square root', () => {
      expect(FixedPoint.toFloat(FixedPoint.sqrt(FixedPoint.fromFloat(4)))).toBeCloseTo(2, 2)
      expect(FixedPoint.toFloat(FixedPoint.sqrt(FixedPoint.fromFloat(9)))).toBeCloseTo(3, 2)
      expect(FixedPoint.toFloat(FixedPoint.sqrt(FixedPoint.fromFloat(2)))).toBeCloseTo(1.414, 2)
    })

    it('should return 0 for negative numbers', () => {
      expect(FixedPoint.sqrt(FixedPoint.fromFloat(-4))).toBe(0)
    })
  })

  describe('backwards compatibility', () => {
    it('should export toFixed function', () => {
      expect(toFixed(5)).toBe(FixedPoint.fromFloat(5))
    })

    it('should export fromFixed function', () => {
      expect(fromFixed(FixedPoint.ONE)).toBe(1)
    })
  })
})
