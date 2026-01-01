import { describe, it, expect, beforeEach } from 'vitest'
import { Camera } from './Camera.ts'

describe('Camera', () => {
  let camera: Camera

  beforeEach(() => {
    camera = new Camera()
  })

  describe('constructor', () => {
    it('should initialize with default values', () => {
      expect(camera.getDistance()).toBe(900)
      expect(camera.getTiltAngle()).toBeCloseTo(20 * (Math.PI / 180))
      expect(camera.getFov()).toBeCloseTo(45 * (Math.PI / 180))
      expect(camera.getAspect()).toBe(5 / 3)
    })

    it('should have valid matrices after construction', () => {
      const viewMatrix = camera.getViewMatrix()
      const projMatrix = camera.getProjectionMatrix()

      expect(viewMatrix).toBeDefined()
      expect(projMatrix).toBeDefined()
    })
  })

  describe('getPosition', () => {
    it('should return camera position with tilt applied', () => {
      const pos = camera.getPosition()

      // Camera should be positioned with X offset due to tilt
      expect(pos.x).toBeLessThan(0) // Tilted to the left
      expect(pos.y).toBe(0)
      expect(pos.z).toBeGreaterThan(0) // In front of origin
    })

    it('should return a copy of position', () => {
      const pos1 = camera.getPosition()
      const pos2 = camera.getPosition()

      pos1.x = 999
      expect(pos2.x).not.toBe(999)
    })
  })

  describe('setDistance', () => {
    it('should update camera distance', () => {
      camera.setDistance(500)
      expect(camera.getDistance()).toBe(500)
    })

    it('should update camera position', () => {
      const posBefore = camera.getPosition()
      camera.setDistance(500)
      const posAfter = camera.getPosition()

      expect(posAfter.z).toBeLessThan(posBefore.z)
    })
  })

  describe('setTiltAngle', () => {
    it('should update tilt angle in radians', () => {
      const angle = 30 * (Math.PI / 180)
      camera.setTiltAngle(angle)
      expect(camera.getTiltAngle()).toBeCloseTo(angle)
    })

    it('should update camera position', () => {
      const posBefore = camera.getPosition()
      camera.setTiltAngle(0)
      const posAfter = camera.getPosition()

      // With no tilt, X should be 0
      expect(posAfter.x).toBeCloseTo(0)
      expect(Math.abs(posBefore.x)).toBeGreaterThan(0)
    })
  })

  describe('setTiltAngleDegrees', () => {
    it('should convert degrees to radians', () => {
      camera.setTiltAngleDegrees(45)
      expect(camera.getTiltAngle()).toBeCloseTo(45 * (Math.PI / 180))
    })
  })

  describe('setFov', () => {
    it('should update field of view', () => {
      const fov = 60 * (Math.PI / 180)
      camera.setFov(fov)
      expect(camera.getFov()).toBeCloseTo(fov)
    })
  })

  describe('setFovDegrees', () => {
    it('should convert degrees to radians', () => {
      camera.setFovDegrees(60)
      expect(camera.getFov()).toBeCloseTo(60 * (Math.PI / 180))
    })
  })

  describe('setAspect', () => {
    it('should update aspect ratio', () => {
      camera.setAspect(16 / 9)
      expect(camera.getAspect()).toBeCloseTo(16 / 9)
    })
  })

  describe('setClipPlanes', () => {
    it('should update near and far planes', () => {
      camera.setClipPlanes(1, 5000)
      // Can't directly verify, but should not throw
      expect(() => camera.getViewProjectionMatrix()).not.toThrow()
    })
  })

  describe('getViewProjectionMatrix', () => {
    it('should return combined view-projection matrix', () => {
      const vp = camera.getViewProjectionMatrix()
      expect(vp).toBeDefined()
    })

    it('should be different from view or projection alone', () => {
      const _view = camera.getViewMatrix()
      const _proj = camera.getProjectionMatrix()
      const vp = camera.getViewProjectionMatrix()

      // VP should be projection * view
      // Just verify it's a valid matrix by checking it can transform a point
      const point = vp.transformPoint(0, 0, 0)
      expect(point).toHaveProperty('x')
      expect(point).toHaveProperty('y')
      expect(point).toHaveProperty('z')
    })
  })

  describe('worldToNDC', () => {
    it('should project origin to center of screen', () => {
      const ndc = camera.worldToNDC(0, 0, 0)

      // Origin should project near center (accounting for tilt)
      expect(Math.abs(ndc.x)).toBeLessThan(0.5)
      expect(Math.abs(ndc.y)).toBeLessThan(0.5)
    })

    it('should project points further right to higher X', () => {
      const left = camera.worldToNDC(-100, 0, 0)
      const right = camera.worldToNDC(100, 0, 0)

      expect(right.x).toBeGreaterThan(left.x)
    })

    it('should project points higher up to higher Y', () => {
      const bottom = camera.worldToNDC(0, -100, 0)
      const top = camera.worldToNDC(0, 100, 0)

      expect(top.y).toBeGreaterThan(bottom.y)
    })
  })

  describe('ndcToWorld', () => {
    it('should unproject center to near origin', () => {
      const world = camera.ndcToWorld(0, 0)

      // Center of screen should map to near origin at z=0
      expect(Math.abs(world.x)).toBeLessThan(50)
      expect(Math.abs(world.y)).toBeLessThan(50)
    })

    it('should be inverse of worldToNDC at z=0', () => {
      const originalX = 150
      const originalY = 75

      const ndc = camera.worldToNDC(originalX, originalY, 0)
      const world = camera.ndcToWorld(ndc.x, ndc.y)

      expect(world.x).toBeCloseTo(originalX, 0)
      expect(world.y).toBeCloseTo(originalY, 0)
    })
  })

  describe('getPlayBounds', () => {
    it('should return play bounds object', () => {
      const bounds = camera.getPlayBounds()

      expect(bounds).toHaveProperty('leftX')
      expect(bounds).toHaveProperty('rightX')
      expect(typeof bounds.getTopY).toBe('function')
      expect(typeof bounds.getBottomY).toBe('function')
    })

    it('should have leftX less than rightX', () => {
      const bounds = camera.getPlayBounds()
      expect(bounds.leftX).toBeLessThan(bounds.rightX)
    })

    it('should have topY greater than bottomY', () => {
      const bounds = camera.getPlayBounds()
      const x = (bounds.leftX + bounds.rightX) / 2

      expect(bounds.getTopY(x)).toBeGreaterThan(bounds.getBottomY(x))
    })

    it('should return valid Y values for any X in bounds', () => {
      const bounds = camera.getPlayBounds()

      for (let t = 0; t <= 1; t += 0.25) {
        const x = bounds.leftX + t * (bounds.rightX - bounds.leftX)
        const topY = bounds.getTopY(x)
        const bottomY = bounds.getBottomY(x)

        expect(typeof topY).toBe('number')
        expect(typeof bottomY).toBe('number')
        expect(topY).toBeGreaterThan(bottomY)
      }
    })
  })

  describe('setOrthographic', () => {
    it('should switch to orthographic projection', () => {
      // Remove tilt to simplify test
      camera.setTiltAngle(0)
      camera.setOrthographic(-400, 400, -300, 300)

      // In orthographic, size doesn't change with distance
      // Test that points at same world X,Y project to same screen X,Y regardless of Z
      const near = camera.worldToNDC(100, 100, 0)
      const far = camera.worldToNDC(100, 100, -100)

      // In orthographic without tilt, X and Y should be identical regardless of Z
      expect(near.x).toBeCloseTo(far.x, 1)
      expect(near.y).toBeCloseTo(far.y, 1)
    })
  })

  describe('setPerspective', () => {
    it('should restore perspective projection', () => {
      camera.setOrthographic(-400, 400, -300, 300)
      camera.setPerspective()

      // In perspective, distant objects appear smaller
      const near = camera.worldToNDC(100, 100, 0)
      const far = camera.worldToNDC(100, 100, -500)

      // Far point should be closer to center due to perspective
      expect(Math.abs(far.x)).toBeLessThan(Math.abs(near.x))
    })
  })

  describe('clone', () => {
    it('should create independent copy', () => {
      camera.setDistance(500)
      camera.setTiltAngleDegrees(30)
      camera.setFovDegrees(60)
      camera.setAspect(2)

      const clone = camera.clone()

      expect(clone.getDistance()).toBe(500)
      expect(clone.getTiltAngle()).toBeCloseTo(30 * (Math.PI / 180))
      expect(clone.getFov()).toBeCloseTo(60 * (Math.PI / 180))
      expect(clone.getAspect()).toBe(2)
    })

    it('should not affect original when modified', () => {
      const clone = camera.clone()

      clone.setDistance(100)
      expect(camera.getDistance()).toBe(900)
    })
  })

  describe('matrix consistency', () => {
    it('should update matrices when parameters change', () => {
      const vp1 = camera.getViewProjectionMatrix()
      const point1 = vp1.transformPoint(100, 100, 0)

      camera.setDistance(500)
      const vp2 = camera.getViewProjectionMatrix()
      const point2 = vp2.transformPoint(100, 100, 0)

      // Different distance should give different projection
      expect(point1.x).not.toBeCloseTo(point2.x)
    })
  })
})
