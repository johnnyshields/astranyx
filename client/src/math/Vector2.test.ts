import { describe, it, expect } from 'vitest'
import { Vector2 } from './Vector2.ts'

describe('Vector2', () => {
  describe('constructor', () => {
    it('should create vector with given components', () => {
      const v = new Vector2(3, 4)
      expect(v.x).toBe(3)
      expect(v.y).toBe(4)
    })

    it('should default to zero', () => {
      const v = new Vector2()
      expect(v.x).toBe(0)
      expect(v.y).toBe(0)
    })
  })

  describe('static factories', () => {
    it('should create vector from angle', () => {
      const v = Vector2.fromAngle(0, 1)
      expect(v.x).toBeCloseTo(1, 5)
      expect(v.y).toBeCloseTo(0, 5)

      const v2 = Vector2.fromAngle(Math.PI / 2, 2)
      expect(v2.x).toBeCloseTo(0, 5)
      expect(v2.y).toBeCloseTo(2, 5)
    })

    it('should create zero vector', () => {
      const v = Vector2.zero()
      expect(v.x).toBe(0)
      expect(v.y).toBe(0)
    })

    it('should create right vector', () => {
      const v = Vector2.right()
      expect(v.x).toBe(1)
      expect(v.y).toBe(0)
    })

    it('should create up vector', () => {
      const v = Vector2.up()
      expect(v.x).toBe(0)
      expect(v.y).toBe(1)
    })

    it('should create from array', () => {
      const v = Vector2.fromArray([5, 7])
      expect(v.x).toBe(5)
      expect(v.y).toBe(7)
    })
  })

  describe('clone', () => {
    it('should create independent copy', () => {
      const v1 = new Vector2(3, 4)
      const v2 = v1.clone()
      v1.x = 10
      expect(v2.x).toBe(3)
    })
  })

  describe('set / copy', () => {
    it('should set components', () => {
      const v = new Vector2()
      v.set(5, 6)
      expect(v.x).toBe(5)
      expect(v.y).toBe(6)
    })

    it('should copy from another vector', () => {
      const v1 = new Vector2()
      const v2 = new Vector2(3, 4)
      v1.copy(v2)
      expect(v1.x).toBe(3)
      expect(v1.y).toBe(4)
    })
  })

  describe('addition', () => {
    it('should add in place (mutating)', () => {
      const v = new Vector2(1, 2)
      v.add(new Vector2(3, 4))
      expect(v.x).toBe(4)
      expect(v.y).toBe(6)
    })

    it('should return new vector with plus()', () => {
      const v1 = new Vector2(1, 2)
      const v2 = new Vector2(3, 4)
      const v3 = v1.plus(v2)
      expect(v1.x).toBe(1) // Original unchanged
      expect(v3.x).toBe(4)
      expect(v3.y).toBe(6)
    })
  })

  describe('subtraction', () => {
    it('should subtract in place (mutating)', () => {
      const v = new Vector2(5, 6)
      v.sub(new Vector2(3, 4))
      expect(v.x).toBe(2)
      expect(v.y).toBe(2)
    })

    it('should return new vector with minus()', () => {
      const v1 = new Vector2(5, 6)
      const v2 = new Vector2(3, 4)
      const v3 = v1.minus(v2)
      expect(v1.x).toBe(5) // Original unchanged
      expect(v3.x).toBe(2)
      expect(v3.y).toBe(2)
    })
  })

  describe('scaling', () => {
    it('should scale in place (mutating)', () => {
      const v = new Vector2(3, 4)
      v.scale(2)
      expect(v.x).toBe(6)
      expect(v.y).toBe(8)
    })

    it('should return new vector with scaled()', () => {
      const v1 = new Vector2(3, 4)
      const v2 = v1.scaled(2)
      expect(v1.x).toBe(3) // Original unchanged
      expect(v2.x).toBe(6)
      expect(v2.y).toBe(8)
    })

    it('should divide by scalar', () => {
      const v = new Vector2(6, 8)
      v.divideScalar(2)
      expect(v.x).toBe(3)
      expect(v.y).toBe(4)
    })

    it('should handle division by zero gracefully', () => {
      const v = new Vector2(6, 8)
      v.divideScalar(0)
      expect(v.x).toBe(6) // Unchanged
      expect(v.y).toBe(8)
    })
  })

  describe('multiplication', () => {
    it('should multiply component-wise (mutating)', () => {
      const v = new Vector2(2, 3)
      v.multiply(new Vector2(4, 5))
      expect(v.x).toBe(8)
      expect(v.y).toBe(15)
    })

    it('should return new vector with multiplied()', () => {
      const v1 = new Vector2(2, 3)
      const v2 = v1.multiplied(new Vector2(4, 5))
      expect(v1.x).toBe(2) // Original unchanged
      expect(v2.x).toBe(8)
      expect(v2.y).toBe(15)
    })
  })

  describe('negation', () => {
    it('should negate in place (mutating)', () => {
      const v = new Vector2(3, -4)
      v.negate()
      expect(v.x).toBe(-3)
      expect(v.y).toBe(4)
    })

    it('should return new vector with negated()', () => {
      const v1 = new Vector2(3, -4)
      const v2 = v1.negated()
      expect(v1.x).toBe(3) // Original unchanged
      expect(v2.x).toBe(-3)
      expect(v2.y).toBe(4)
    })
  })

  describe('length', () => {
    it('should calculate length squared', () => {
      const v = new Vector2(3, 4)
      expect(v.lengthSquared()).toBe(25)
    })

    it('should calculate length', () => {
      const v = new Vector2(3, 4)
      expect(v.length()).toBe(5)
    })
  })

  describe('normalization', () => {
    it('should normalize in place (mutating)', () => {
      const v = new Vector2(3, 4)
      v.normalize()
      expect(v.length()).toBeCloseTo(1, 5)
      expect(v.x).toBeCloseTo(0.6, 5)
      expect(v.y).toBeCloseTo(0.8, 5)
    })

    it('should return new vector with normalized()', () => {
      const v1 = new Vector2(3, 4)
      const v2 = v1.normalized()
      expect(v1.length()).toBe(5) // Original unchanged
      expect(v2.length()).toBeCloseTo(1, 5)
    })

    it('should handle zero vector', () => {
      const v = new Vector2(0, 0)
      v.normalize()
      expect(v.x).toBe(0)
      expect(v.y).toBe(0)
    })

    it('should set length', () => {
      const v = new Vector2(3, 4)
      v.setLength(10)
      expect(v.length()).toBeCloseTo(10, 5)
    })

    it('should limit length', () => {
      const v = new Vector2(30, 40) // length 50
      v.limit(10)
      expect(v.length()).toBeCloseTo(10, 5)
    })

    it('should not change if under limit', () => {
      const v = new Vector2(3, 4) // length 5
      v.limit(10)
      expect(v.length()).toBeCloseTo(5, 5)
    })
  })

  describe('dot product', () => {
    it('should calculate dot product', () => {
      const v1 = new Vector2(1, 2)
      const v2 = new Vector2(3, 4)
      expect(v1.dot(v2)).toBe(11) // 1*3 + 2*4
    })

    it('should return 0 for perpendicular vectors', () => {
      const v1 = new Vector2(1, 0)
      const v2 = new Vector2(0, 1)
      expect(v1.dot(v2)).toBe(0)
    })
  })

  describe('cross product', () => {
    it('should calculate cross product (scalar)', () => {
      const v1 = new Vector2(1, 0)
      const v2 = new Vector2(0, 1)
      expect(v1.cross(v2)).toBe(1)
    })

    it('should return 0 for parallel vectors', () => {
      const v1 = new Vector2(2, 4)
      const v2 = new Vector2(1, 2)
      expect(v1.cross(v2)).toBeCloseTo(0, 5)
    })
  })

  describe('angles', () => {
    it('should get angle of vector', () => {
      expect(new Vector2(1, 0).angle()).toBeCloseTo(0, 5)
      expect(new Vector2(0, 1).angle()).toBeCloseTo(Math.PI / 2, 5)
      expect(new Vector2(-1, 0).angle()).toBeCloseTo(Math.PI, 5)
      expect(new Vector2(0, -1).angle()).toBeCloseTo(-Math.PI / 2, 5)
    })

    it('should get angle between vectors', () => {
      const v1 = new Vector2(1, 0)
      const v2 = new Vector2(0, 1)
      expect(v1.angleTo(v2)).toBeCloseTo(Math.PI / 2, 5)
    })
  })

  describe('rotation', () => {
    it('should rotate in place (mutating)', () => {
      const v = new Vector2(1, 0)
      v.rotate(Math.PI / 2)
      expect(v.x).toBeCloseTo(0, 5)
      expect(v.y).toBeCloseTo(1, 5)
    })

    it('should return new vector with rotated()', () => {
      const v1 = new Vector2(1, 0)
      const v2 = v1.rotated(Math.PI / 2)
      expect(v1.x).toBeCloseTo(1, 5) // Original unchanged
      expect(v2.x).toBeCloseTo(0, 5)
      expect(v2.y).toBeCloseTo(1, 5)
    })

    it('should get perpendicular vector', () => {
      const v = new Vector2(3, 4)
      const p = v.perpendicular()
      expect(p.dot(v)).toBeCloseTo(0, 5) // Should be perpendicular
    })
  })

  describe('distance', () => {
    it('should calculate distance to another vector', () => {
      const v1 = new Vector2(0, 0)
      const v2 = new Vector2(3, 4)
      expect(v1.distanceTo(v2)).toBe(5)
    })

    it('should calculate squared distance', () => {
      const v1 = new Vector2(0, 0)
      const v2 = new Vector2(3, 4)
      expect(v1.distanceSquaredTo(v2)).toBe(25)
    })
  })

  describe('lerp', () => {
    it('should interpolate between vectors', () => {
      const v1 = new Vector2(0, 0)
      const v2 = new Vector2(10, 20)
      const v3 = v1.lerp(v2, 0.5)
      expect(v3.x).toBe(5)
      expect(v3.y).toBe(10)
    })

    it('should lerp in place (mutating)', () => {
      const v1 = new Vector2(0, 0)
      const v2 = new Vector2(10, 20)
      v1.lerpTo(v2, 0.5)
      expect(v1.x).toBe(5)
      expect(v1.y).toBe(10)
    })
  })

  describe('reflect', () => {
    it('should reflect off surface', () => {
      const v = new Vector2(1, -1).normalized()
      const normal = new Vector2(0, 1) // Horizontal surface
      const reflected = v.reflect(normal)
      expect(reflected.x).toBeCloseTo(v.x, 5)
      expect(reflected.y).toBeCloseTo(-v.y, 5)
    })
  })

  describe('equality', () => {
    it('should check exact equality', () => {
      const v1 = new Vector2(3, 4)
      const v2 = new Vector2(3, 4)
      const v3 = new Vector2(3, 5)
      expect(v1.equals(v2)).toBe(true)
      expect(v1.equals(v3)).toBe(false)
    })

    it('should check equality with epsilon', () => {
      const v1 = new Vector2(3, 4)
      const v2 = new Vector2(3.0001, 4.0001)
      expect(v1.equals(v2, 0.001)).toBe(true)
      expect(v1.equals(v2, 0.00001)).toBe(false)
    })

    it('should check if zero', () => {
      expect(new Vector2(0, 0).isZero()).toBe(true)
      expect(new Vector2(0.001, 0).isZero()).toBe(false)
    })
  })

  describe('conversion', () => {
    it('should convert to array', () => {
      const v = new Vector2(3, 4)
      expect(v.toArray()).toEqual([3, 4])
    })

    it('should convert to string', () => {
      const v = new Vector2(3, 4)
      expect(v.toString()).toBe('Vector2(3, 4)')
    })
  })
})
