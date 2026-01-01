import { describe, it, expect } from 'vitest'
import { Matrix4 } from './Matrix4.ts'

describe('Matrix4', () => {
  describe('constructor', () => {
    it('should create identity matrix by default', () => {
      const m = new Matrix4()
      const d = m.getData()
      expect(d[0]).toBe(1)
      expect(d[5]).toBe(1)
      expect(d[10]).toBe(1)
      expect(d[15]).toBe(1)
      expect(d[1]).toBe(0)
      expect(d[4]).toBe(0)
    })

    it('should create from Float32Array', () => {
      const data = new Float32Array([
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
      ])
      const m = new Matrix4(data)
      expect(m.getData()[0]).toBe(1)
      expect(m.getData()[15]).toBe(16)
    })
  })

  describe('static factories', () => {
    it('should create identity matrix', () => {
      const m = Matrix4.identity()
      expect(m.get(0, 0)).toBe(1)
      expect(m.get(1, 1)).toBe(1)
      expect(m.get(2, 2)).toBe(1)
      expect(m.get(3, 3)).toBe(1)
      expect(m.get(0, 1)).toBe(0)
    })

    it('should create zero matrix', () => {
      const m = Matrix4.zero()
      for (let i = 0; i < 16; i++) {
        expect(m.getData()[i]).toBe(0)
      }
    })
  })

  describe('get / set', () => {
    it('should get elements by row and column', () => {
      const m = new Matrix4()
      m.getData()[4] = 5 // Column 1, row 0
      expect(m.get(0, 1)).toBe(5)
    })

    it('should set elements by row and column', () => {
      const m = new Matrix4()
      m.set(0, 1, 7)
      expect(m.getData()[4]).toBe(7)
    })
  })

  describe('clone / copy', () => {
    it('should create independent clone', () => {
      const m1 = new Matrix4()
      m1.set(0, 0, 5)
      const m2 = m1.clone()
      m1.set(0, 0, 10)
      expect(m2.get(0, 0)).toBe(5)
    })

    it('should copy values from another matrix', () => {
      const m1 = new Matrix4()
      m1.set(0, 0, 5)
      const m2 = new Matrix4()
      m2.copy(m1)
      expect(m2.get(0, 0)).toBe(5)
    })
  })

  describe('translation', () => {
    it('should set translation', () => {
      const m = new Matrix4()
      m.setTranslation(3, 4, 5)
      expect(m.getData()[12]).toBe(3)
      expect(m.getData()[13]).toBe(4)
      expect(m.getData()[14]).toBe(5)
    })

    it('should get translation', () => {
      const m = new Matrix4()
      m.setTranslation(3, 4, 5)
      const t = m.getTranslation()
      expect(t.x).toBe(3)
      expect(t.y).toBe(4)
      expect(t.z).toBe(5)
    })

    it('should translate correctly', () => {
      const m = new Matrix4()
      m.translate(3, 4, 5)
      const t = m.getTranslation()
      expect(t.x).toBe(3)
      expect(t.y).toBe(4)
      expect(t.z).toBe(5)
    })
  })

  describe('scale', () => {
    it('should scale uniformly', () => {
      const m = new Matrix4()
      m.scale(2)
      expect(m.get(0, 0)).toBe(2)
      expect(m.get(1, 1)).toBe(2)
      expect(m.get(2, 2)).toBe(2)
    })

    it('should scale non-uniformly', () => {
      const m = new Matrix4()
      m.scaleXYZ(2, 3, 4)
      expect(m.get(0, 0)).toBe(2)
      expect(m.get(1, 1)).toBe(3)
      expect(m.get(2, 2)).toBe(4)
    })
  })

  describe('rotation', () => {
    it('should rotate around X axis', () => {
      const m = new Matrix4()
      m.rotateX(Math.PI / 2)
      // Rotating (0, 1, 0) around X by 90 degrees should give (0, 0, 1)
      const result = m.transformDirection(0, 1, 0)
      expect(result.x).toBeCloseTo(0, 5)
      expect(result.y).toBeCloseTo(0, 5)
      expect(result.z).toBeCloseTo(1, 5)
    })

    it('should rotate around Y axis', () => {
      const m = new Matrix4()
      m.rotateY(Math.PI / 2)
      // Rotating (1, 0, 0) around Y by 90 degrees should give (0, 0, -1)
      const result = m.transformDirection(1, 0, 0)
      expect(result.x).toBeCloseTo(0, 5)
      expect(result.y).toBeCloseTo(0, 5)
      expect(result.z).toBeCloseTo(-1, 5)
    })

    it('should rotate around Z axis', () => {
      const m = new Matrix4()
      m.rotateZ(Math.PI / 2)
      // Rotating (1, 0, 0) around Z by 90 degrees should give (0, 1, 0)
      const result = m.transformDirection(1, 0, 0)
      expect(result.x).toBeCloseTo(0, 5)
      expect(result.y).toBeCloseTo(1, 5)
      expect(result.z).toBeCloseTo(0, 5)
    })
  })

  describe('multiply', () => {
    it('should multiply with identity', () => {
      const m = new Matrix4()
      m.setTranslation(3, 4, 5)
      const identity = Matrix4.identity()
      m.multiply(identity)
      const t = m.getTranslation()
      expect(t.x).toBe(3)
      expect(t.y).toBe(4)
      expect(t.z).toBe(5)
    })

    it('should combine translations', () => {
      const m1 = new Matrix4()
      m1.translate(1, 0, 0)
      const m2 = new Matrix4()
      m2.translate(0, 2, 0)
      m1.multiply(m2)
      const t = m1.getTranslation()
      expect(t.x).toBeCloseTo(1, 5)
      expect(t.y).toBeCloseTo(2, 5)
    })

    it('should return new matrix with multiplied()', () => {
      const m1 = new Matrix4()
      m1.translate(1, 0, 0)
      const m2 = new Matrix4()
      m2.translate(0, 2, 0)
      const m3 = m1.multiplied(m2)
      // Original should be unchanged
      expect(m1.getTranslation().x).toBe(1)
      expect(m1.getTranslation().y).toBe(0)
      // Result should have both
      expect(m3.getTranslation().x).toBeCloseTo(1, 5)
      expect(m3.getTranslation().y).toBeCloseTo(2, 5)
    })
  })

  describe('projection matrices', () => {
    it('should create perspective matrix', () => {
      const m = new Matrix4()
      m.setPerspective(Math.PI / 4, 16 / 9, 0.1, 1000)
      // Should have valid perspective elements
      expect(m.get(0, 0)).toBeGreaterThan(0)
      expect(m.get(1, 1)).toBeGreaterThan(0)
      expect(m.get(3, 2)).toBe(-1) // Perspective divide
    })

    it('should create orthographic matrix', () => {
      const m = new Matrix4()
      m.setOrthographic(-1, 1, -1, 1, 0.1, 100)
      expect(m.get(0, 0)).toBe(1) // 2 / (1 - -1)
      expect(m.get(1, 1)).toBe(1) // 2 / (1 - -1)
      expect(m.get(3, 3)).toBe(1)
    })
  })

  describe('lookAt', () => {
    it('should create view matrix looking along -Z', () => {
      const m = new Matrix4()
      m.setLookAt(0, 0, 5, 0, 0, 0, 0, 1, 0)
      // Should be able to transform origin to camera space
      const result = m.transformPoint(0, 0, 0)
      expect(result.z).toBeCloseTo(-5, 5) // Origin is 5 units in front of camera
    })
  })

  describe('invert', () => {
    it('should invert identity to identity', () => {
      const m = Matrix4.identity()
      m.invert()
      expect(m.get(0, 0)).toBeCloseTo(1, 5)
      expect(m.get(1, 1)).toBeCloseTo(1, 5)
      expect(m.get(0, 1)).toBeCloseTo(0, 5)
    })

    it('should invert translation', () => {
      const m = new Matrix4()
      m.translate(3, 4, 5)
      m.invert()
      const t = m.getTranslation()
      expect(t.x).toBeCloseTo(-3, 5)
      expect(t.y).toBeCloseTo(-4, 5)
      expect(t.z).toBeCloseTo(-5, 5)
    })

    it('should return new matrix with inverted()', () => {
      const m = new Matrix4()
      m.translate(3, 4, 5)
      const inv = m.inverted()
      // Original unchanged
      expect(m.getTranslation().x).toBe(3)
      // Inverse is negated
      expect(inv.getTranslation().x).toBeCloseTo(-3, 5)
    })

    it('M * M^-1 should be identity', () => {
      const m = new Matrix4()
      m.translate(3, 4, 5)
      m.rotateX(0.5)
      m.rotateY(0.3)
      m.scale(2)

      const inv = m.inverted()
      const result = m.multiplied(inv)

      expect(result.equals(Matrix4.identity())).toBe(true)
    })
  })

  describe('transpose', () => {
    it('should transpose matrix', () => {
      const m = new Matrix4()
      m.set(0, 1, 5)
      m.transpose()
      expect(m.get(1, 0)).toBe(5)
      expect(m.get(0, 1)).toBe(0)
    })

    it('should return new matrix with transposed()', () => {
      const m = new Matrix4()
      m.set(0, 1, 5)
      const t = m.transposed()
      expect(m.get(0, 1)).toBe(5) // Original unchanged
      expect(t.get(1, 0)).toBe(5)
    })
  })

  describe('transform', () => {
    it('should transform point with translation', () => {
      const m = new Matrix4()
      m.translate(10, 20, 30)
      const result = m.transformPoint(0, 0, 0)
      expect(result.x).toBeCloseTo(10, 5)
      expect(result.y).toBeCloseTo(20, 5)
      expect(result.z).toBeCloseTo(30, 5)
    })

    it('should transform direction ignoring translation', () => {
      const m = new Matrix4()
      m.translate(10, 20, 30)
      const result = m.transformDirection(1, 0, 0)
      expect(result.x).toBeCloseTo(1, 5)
      expect(result.y).toBeCloseTo(0, 5)
      expect(result.z).toBeCloseTo(0, 5)
    })

    it('should transform direction with rotation', () => {
      const m = new Matrix4()
      m.rotateZ(Math.PI / 2)
      const result = m.transformDirection(1, 0, 0)
      expect(result.x).toBeCloseTo(0, 5)
      expect(result.y).toBeCloseTo(1, 5)
    })
  })

  describe('extractMatrix3', () => {
    it('should extract upper-left 3x3', () => {
      const m = new Matrix4()
      m.rotateZ(Math.PI / 2)
      const m3 = m.extractMatrix3()
      expect(m3.length).toBe(9)
      expect(m3[0]).toBeCloseTo(0, 5)
      expect(m3[3]).toBeCloseTo(-1, 5)
    })
  })

  describe('determinant', () => {
    it('should calculate determinant of identity as 1', () => {
      const m = Matrix4.identity()
      expect(m.determinant()).toBeCloseTo(1, 5)
    })

    it('should calculate determinant of scaled matrix', () => {
      const m = new Matrix4()
      m.scale(2)
      expect(m.determinant()).toBeCloseTo(8, 5) // 2^3
    })
  })

  describe('equals', () => {
    it('should compare matrices', () => {
      const m1 = new Matrix4()
      const m2 = new Matrix4()
      expect(m1.equals(m2)).toBe(true)

      m1.set(0, 0, 5)
      expect(m1.equals(m2)).toBe(false)
    })

    it('should use epsilon for comparison', () => {
      const m1 = new Matrix4()
      const m2 = new Matrix4()
      m2.set(0, 0, 1.00001)
      expect(m1.equals(m2, 0.0001)).toBe(true)
      expect(m1.equals(m2, 0.000001)).toBe(false)
    })
  })
})
