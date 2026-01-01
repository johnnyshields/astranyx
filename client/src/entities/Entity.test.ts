import { describe, it, expect } from 'vitest'
import { Entity, DamageableEntity, checkCircleCollision } from './Entity'
import { Vector2 } from '../math/Vector2'

// Concrete implementation for testing abstract Entity class
class TestEntity extends Entity {
  private dead = false

  constructor(id: number, x: number = 0, y: number = 0) {
    super(id, x, y)
  }

  update(dt: number): void {
    this.move(dt)
    this.frame++
  }

  isDead(): boolean {
    return this.dead
  }

  kill(): void {
    this.dead = true
  }
}

describe('Entity', () => {
  describe('constructor', () => {
    it('should create entity with id and position', () => {
      const entity = new TestEntity(1, 100, 200)
      expect(entity.id).toBe(1)
      expect(entity.x).toBe(100)
      expect(entity.y).toBe(200)
    })

    it('should default position to 0,0', () => {
      const entity = new TestEntity(1)
      expect(entity.x).toBe(0)
      expect(entity.y).toBe(0)
    })

    it('should initialize velocity to 0,0', () => {
      const entity = new TestEntity(1, 100, 200)
      expect(entity.vx).toBe(0)
      expect(entity.vy).toBe(0)
    })

    it('should initialize frame to 0', () => {
      const entity = new TestEntity(1)
      expect(entity.frame).toBe(0)
    })
  })

  describe('position accessors', () => {
    it('should get and set x', () => {
      const entity = new TestEntity(1)
      entity.x = 50
      expect(entity.x).toBe(50)
    })

    it('should get and set y', () => {
      const entity = new TestEntity(1)
      entity.y = 75
      expect(entity.y).toBe(75)
    })
  })

  describe('velocity accessors', () => {
    it('should get and set vx', () => {
      const entity = new TestEntity(1)
      entity.vx = 10
      expect(entity.vx).toBe(10)
    })

    it('should get and set vy', () => {
      const entity = new TestEntity(1)
      entity.vy = -5
      expect(entity.vy).toBe(-5)
    })
  })

  describe('getPosition', () => {
    it('should return a clone of position', () => {
      const entity = new TestEntity(1, 100, 200)
      const pos = entity.getPosition()
      expect(pos.x).toBe(100)
      expect(pos.y).toBe(200)

      // Modifying returned position should not affect entity
      pos.x = 999
      expect(entity.x).toBe(100)
    })
  })

  describe('setPosition', () => {
    it('should set position from Vector2', () => {
      const entity = new TestEntity(1)
      entity.setPosition(new Vector2(50, 75))
      expect(entity.x).toBe(50)
      expect(entity.y).toBe(75)
    })
  })

  describe('getVelocity', () => {
    it('should return a clone of velocity', () => {
      const entity = new TestEntity(1)
      entity.vx = 10
      entity.vy = 20
      const vel = entity.getVelocity()
      expect(vel.x).toBe(10)
      expect(vel.y).toBe(20)

      // Modifying returned velocity should not affect entity
      vel.x = 999
      expect(entity.vx).toBe(10)
    })
  })

  describe('setVelocity', () => {
    it('should set velocity from Vector2', () => {
      const entity = new TestEntity(1)
      entity.setVelocity(new Vector2(15, -10))
      expect(entity.vx).toBe(15)
      expect(entity.vy).toBe(-10)
    })
  })

  describe('getSpeed', () => {
    it('should return velocity magnitude', () => {
      const entity = new TestEntity(1)
      entity.vx = 3
      entity.vy = 4
      expect(entity.getSpeed()).toBe(5)
    })

    it('should return 0 for stationary entity', () => {
      const entity = new TestEntity(1)
      expect(entity.getSpeed()).toBe(0)
    })
  })

  describe('move', () => {
    it('should move entity by velocity with default dt=1', () => {
      const entity = new TestEntity(1, 100, 100)
      entity.vx = 10
      entity.vy = -5
      entity.move()
      expect(entity.x).toBe(110)
      expect(entity.y).toBe(95)
    })

    it('should move entity by velocity with custom dt', () => {
      const entity = new TestEntity(1, 100, 100)
      entity.vx = 10
      entity.vy = -5
      entity.move(2)
      expect(entity.x).toBe(120)
      expect(entity.y).toBe(90)
    })

    it('should not move stationary entity', () => {
      const entity = new TestEntity(1, 100, 100)
      entity.move()
      expect(entity.x).toBe(100)
      expect(entity.y).toBe(100)
    })
  })

  describe('distanceTo', () => {
    it('should calculate distance to another entity', () => {
      const entity1 = new TestEntity(1, 0, 0)
      const entity2 = new TestEntity(2, 3, 4)
      expect(entity1.distanceTo(entity2)).toBe(5)
    })

    it('should return 0 for overlapping entities', () => {
      const entity1 = new TestEntity(1, 100, 100)
      const entity2 = new TestEntity(2, 100, 100)
      expect(entity1.distanceTo(entity2)).toBe(0)
    })
  })

  describe('distanceSquaredTo', () => {
    it('should calculate squared distance to another entity', () => {
      const entity1 = new TestEntity(1, 0, 0)
      const entity2 = new TestEntity(2, 3, 4)
      expect(entity1.distanceSquaredTo(entity2)).toBe(25)
    })

    it('should return 0 for overlapping entities', () => {
      const entity1 = new TestEntity(1, 100, 100)
      const entity2 = new TestEntity(2, 100, 100)
      expect(entity1.distanceSquaredTo(entity2)).toBe(0)
    })
  })

  describe('directionTo', () => {
    it('should calculate normalized direction to another entity', () => {
      const entity1 = new TestEntity(1, 0, 0)
      const entity2 = new TestEntity(2, 100, 0)
      const dir = entity1.directionTo(entity2)
      expect(dir.x).toBeCloseTo(1, 5)
      expect(dir.y).toBeCloseTo(0, 5)
    })

    it('should handle diagonal direction', () => {
      const entity1 = new TestEntity(1, 0, 0)
      const entity2 = new TestEntity(2, 10, 10)
      const dir = entity1.directionTo(entity2)
      const sqrt2over2 = Math.sqrt(2) / 2
      expect(dir.x).toBeCloseTo(sqrt2over2, 5)
      expect(dir.y).toBeCloseTo(sqrt2over2, 5)
    })
  })

  describe('angleTo', () => {
    it('should calculate angle to another entity (right)', () => {
      const entity1 = new TestEntity(1, 0, 0)
      const entity2 = new TestEntity(2, 100, 0)
      expect(entity1.angleTo(entity2)).toBeCloseTo(0, 5)
    })

    it('should calculate angle to another entity (up)', () => {
      const entity1 = new TestEntity(1, 0, 0)
      const entity2 = new TestEntity(2, 0, 100)
      expect(entity1.angleTo(entity2)).toBeCloseTo(Math.PI / 2, 5)
    })

    it('should calculate angle to another entity (left)', () => {
      const entity1 = new TestEntity(1, 0, 0)
      const entity2 = new TestEntity(2, -100, 0)
      expect(entity1.angleTo(entity2)).toBeCloseTo(Math.PI, 5)
    })

    it('should calculate angle to another entity (down)', () => {
      const entity1 = new TestEntity(1, 0, 0)
      const entity2 = new TestEntity(2, 0, -100)
      expect(entity1.angleTo(entity2)).toBeCloseTo(-Math.PI / 2, 5)
    })
  })

  describe('isInBounds', () => {
    it('should return true when inside bounds', () => {
      const entity = new TestEntity(1, 50, 50)
      expect(entity.isInBounds(0, 100, 0, 100)).toBe(true)
    })

    it('should return true when on boundary', () => {
      const entity = new TestEntity(1, 0, 100)
      expect(entity.isInBounds(0, 100, 0, 100)).toBe(true)
    })

    it('should return false when outside bounds', () => {
      const entity = new TestEntity(1, 150, 50)
      expect(entity.isInBounds(0, 100, 0, 100)).toBe(false)
    })

    it('should return false when below minX', () => {
      const entity = new TestEntity(1, -10, 50)
      expect(entity.isInBounds(0, 100, 0, 100)).toBe(false)
    })

    it('should return false when above maxY', () => {
      const entity = new TestEntity(1, 50, 150)
      expect(entity.isInBounds(0, 100, 0, 100)).toBe(false)
    })
  })

  describe('clampToBounds', () => {
    it('should not change position when inside bounds', () => {
      const entity = new TestEntity(1, 50, 50)
      entity.clampToBounds(0, 100, 0, 100)
      expect(entity.x).toBe(50)
      expect(entity.y).toBe(50)
    })

    it('should clamp x to minX', () => {
      const entity = new TestEntity(1, -50, 50)
      entity.clampToBounds(0, 100, 0, 100)
      expect(entity.x).toBe(0)
      expect(entity.y).toBe(50)
    })

    it('should clamp x to maxX', () => {
      const entity = new TestEntity(1, 150, 50)
      entity.clampToBounds(0, 100, 0, 100)
      expect(entity.x).toBe(100)
      expect(entity.y).toBe(50)
    })

    it('should clamp y to minY', () => {
      const entity = new TestEntity(1, 50, -50)
      entity.clampToBounds(0, 100, 0, 100)
      expect(entity.x).toBe(50)
      expect(entity.y).toBe(0)
    })

    it('should clamp y to maxY', () => {
      const entity = new TestEntity(1, 50, 150)
      entity.clampToBounds(0, 100, 0, 100)
      expect(entity.x).toBe(50)
      expect(entity.y).toBe(100)
    })

    it('should clamp both x and y', () => {
      const entity = new TestEntity(1, -50, 150)
      entity.clampToBounds(0, 100, 0, 100)
      expect(entity.x).toBe(0)
      expect(entity.y).toBe(100)
    })
  })

  describe('abstract methods', () => {
    it('should call update and increment frame', () => {
      const entity = new TestEntity(1, 0, 0)
      entity.vx = 10
      entity.vy = 5
      entity.update(1)
      expect(entity.x).toBe(10)
      expect(entity.y).toBe(5)
      expect(entity.frame).toBe(1)
    })

    it('should track dead state', () => {
      const entity = new TestEntity(1)
      expect(entity.isDead()).toBe(false)
      entity.kill()
      expect(entity.isDead()).toBe(true)
    })
  })
})

describe('DamageableEntity', () => {
  describe('constructor', () => {
    it('should initialize with default max health', () => {
      const entity = new DamageableEntity()
      expect(entity.maxHealth).toBe(100)
      expect(entity.health).toBe(100)
    })

    it('should initialize with custom max health', () => {
      const entity = new DamageableEntity(250)
      expect(entity.maxHealth).toBe(250)
      expect(entity.health).toBe(250)
    })
  })

  describe('takeDamage', () => {
    it('should reduce health by damage amount', () => {
      const entity = new DamageableEntity(100)
      entity.takeDamage(25)
      expect(entity.health).toBe(75)
    })

    it('should not reduce health below 0', () => {
      const entity = new DamageableEntity(100)
      entity.takeDamage(150)
      expect(entity.health).toBe(0)
    })

    it('should handle 0 damage', () => {
      const entity = new DamageableEntity(100)
      entity.takeDamage(0)
      expect(entity.health).toBe(100)
    })
  })

  describe('heal', () => {
    it('should increase health by heal amount', () => {
      const entity = new DamageableEntity(100)
      entity.takeDamage(50)
      entity.heal(25)
      expect(entity.health).toBe(75)
    })

    it('should not increase health above max', () => {
      const entity = new DamageableEntity(100)
      entity.takeDamage(10)
      entity.heal(50)
      expect(entity.health).toBe(100)
    })

    it('should heal to full health', () => {
      const entity = new DamageableEntity(100)
      entity.takeDamage(100)
      entity.heal(100)
      expect(entity.health).toBe(100)
    })
  })

  describe('getHealthPercent', () => {
    it('should return 1 at full health', () => {
      const entity = new DamageableEntity(100)
      expect(entity.getHealthPercent()).toBe(1)
    })

    it('should return 0.5 at half health', () => {
      const entity = new DamageableEntity(100)
      entity.takeDamage(50)
      expect(entity.getHealthPercent()).toBe(0.5)
    })

    it('should return 0 at zero health', () => {
      const entity = new DamageableEntity(100)
      entity.takeDamage(100)
      expect(entity.getHealthPercent()).toBe(0)
    })

    it('should handle 0 max health', () => {
      const entity = new DamageableEntity(0)
      expect(entity.getHealthPercent()).toBe(0)
    })
  })

  describe('isDead', () => {
    it('should return false at full health', () => {
      const entity = new DamageableEntity(100)
      expect(entity.isDead()).toBe(false)
    })

    it('should return false at partial health', () => {
      const entity = new DamageableEntity(100)
      entity.takeDamage(99)
      expect(entity.isDead()).toBe(false)
    })

    it('should return true at zero health', () => {
      const entity = new DamageableEntity(100)
      entity.takeDamage(100)
      expect(entity.isDead()).toBe(true)
    })
  })
})

describe('checkCircleCollision', () => {
  it('should return true for overlapping circles', () => {
    expect(checkCircleCollision(0, 0, 10, 15, 0, 10)).toBe(true)
  })

  it('should return false for non-overlapping circles', () => {
    expect(checkCircleCollision(0, 0, 10, 100, 0, 10)).toBe(false)
  })

  it('should return true for circles just touching', () => {
    // Two circles of radius 10, centers 19 units apart - should overlap
    expect(checkCircleCollision(0, 0, 10, 19, 0, 10)).toBe(true)
  })

  it('should return false for circles just not touching', () => {
    // Two circles of radius 10, centers 21 units apart - should not overlap
    expect(checkCircleCollision(0, 0, 10, 21, 0, 10)).toBe(false)
  })

  it('should return true for concentric circles', () => {
    expect(checkCircleCollision(50, 50, 10, 50, 50, 5)).toBe(true)
  })

  it('should handle diagonal collision', () => {
    // Two circles of radius 10 at diagonal
    expect(checkCircleCollision(0, 0, 10, 10, 10, 10)).toBe(true)
  })

  it('should handle zero radius circles', () => {
    expect(checkCircleCollision(0, 0, 0, 0, 0, 0)).toBe(false) // At same point but radius sum is 0
    expect(checkCircleCollision(0, 0, 0, 1, 0, 0)).toBe(false)
  })
})
