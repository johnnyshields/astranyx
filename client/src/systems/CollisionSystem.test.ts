import { describe, it, expect, beforeEach } from 'vitest'
import {
  CollisionSystem,
  type CollidableEntity,
  type CollisionShape,
  canCollide,
  circleVsCircle,
  boxVsBox,
  circleVsBox,
  pointInBox,
  beamHits,
  shapesCollide,
  HITBOX_SIZES,
  createPlayerShape,
  createEnemyShape,
  createBossShape,
  createBulletShape,
  createBeamShape,
  createOrbShape,
} from './CollisionSystem.ts'

describe('collision primitives', () => {
  describe('circleVsCircle', () => {
    it('should detect overlapping circles', () => {
      expect(circleVsCircle(0, 0, 10, 15, 0, 10)).toBe(true)
    })

    it('should detect touching circles', () => {
      expect(circleVsCircle(0, 0, 10, 20, 0, 10)).toBe(false) // Just touching
    })

    it('should detect non-overlapping circles', () => {
      expect(circleVsCircle(0, 0, 10, 25, 0, 10)).toBe(false)
    })

    it('should detect concentric circles', () => {
      expect(circleVsCircle(5, 5, 10, 5, 5, 5)).toBe(true)
    })

    it('should work with diagonal positions', () => {
      expect(circleVsCircle(0, 0, 10, 7, 7, 10)).toBe(true)
      expect(circleVsCircle(0, 0, 5, 10, 10, 5)).toBe(false)
    })
  })

  describe('boxVsBox', () => {
    it('should detect overlapping boxes', () => {
      expect(boxVsBox(0, 0, 10, 10, 15, 0, 10, 10)).toBe(true)
    })

    it('should detect non-overlapping boxes', () => {
      expect(boxVsBox(0, 0, 10, 10, 25, 0, 10, 10)).toBe(false)
    })

    it('should detect contained boxes', () => {
      expect(boxVsBox(0, 0, 20, 20, 5, 5, 5, 5)).toBe(true)
    })

    it('should detect corner overlaps', () => {
      expect(boxVsBox(0, 0, 10, 10, 15, 15, 10, 10)).toBe(true)
    })

    it('should handle different sizes', () => {
      expect(boxVsBox(0, 0, 5, 10, 4, 0, 5, 5)).toBe(true)
    })
  })

  describe('circleVsBox', () => {
    it('should detect circle inside box', () => {
      expect(circleVsBox(0, 0, 5, 0, 0, 20, 20)).toBe(true)
    })

    it('should detect circle overlapping box side', () => {
      expect(circleVsBox(15, 0, 10, 0, 0, 10, 10)).toBe(true)
    })

    it('should detect circle overlapping box corner', () => {
      expect(circleVsBox(15, 15, 10, 0, 0, 10, 10)).toBe(true)
    })

    it('should detect circle not touching box', () => {
      expect(circleVsBox(30, 0, 5, 0, 0, 10, 10)).toBe(false)
    })

    it('should handle circle near corner but not touching', () => {
      expect(circleVsBox(20, 20, 5, 0, 0, 10, 10)).toBe(false)
    })
  })

  describe('pointInBox', () => {
    it('should detect point inside box', () => {
      expect(pointInBox(5, 5, 0, 0, 10, 10)).toBe(true)
    })

    it('should detect point at box center', () => {
      expect(pointInBox(0, 0, 0, 0, 10, 10)).toBe(true)
    })

    it('should detect point outside box', () => {
      expect(pointInBox(15, 0, 0, 0, 10, 10)).toBe(false)
    })

    it('should handle negative coordinates', () => {
      expect(pointInBox(-5, -5, 0, 0, 10, 10)).toBe(true)
      expect(pointInBox(-15, 0, 0, 0, 10, 10)).toBe(false)
    })
  })

  describe('beamHits', () => {
    it('should hit target to the right', () => {
      expect(beamHits(0, 0, 25, 100, 0, 10)).toBe(true)
    })

    it('should not hit target to the left', () => {
      expect(beamHits(0, 0, 25, -100, 0, 10)).toBe(false)
    })

    it('should not hit target above beam', () => {
      expect(beamHits(0, 0, 25, 100, 50, 10)).toBe(false)
    })

    it('should not hit target below beam', () => {
      expect(beamHits(0, 0, 25, 100, -50, 10)).toBe(false)
    })

    it('should hit target at beam height boundary', () => {
      expect(beamHits(0, 0, 25, 100, 30, 10)).toBe(true) // 30 < 25 + 10
    })

    it('should hit target at beam origin', () => {
      expect(beamHits(0, 0, 25, 1, 0, 10)).toBe(true)
    })
  })
})

describe('shapesCollide', () => {
  it('should handle circle vs circle', () => {
    const circle1: CollisionShape = { type: 'circle', radius: 10 }
    const circle2: CollisionShape = { type: 'circle', radius: 10 }

    expect(shapesCollide(0, 0, circle1, 15, 0, circle2)).toBe(true)
    expect(shapesCollide(0, 0, circle1, 25, 0, circle2)).toBe(false)
  })

  it('should handle box vs box', () => {
    const box1: CollisionShape = { type: 'box', halfWidth: 10, halfHeight: 10 }
    const box2: CollisionShape = { type: 'box', halfWidth: 10, halfHeight: 10 }

    expect(shapesCollide(0, 0, box1, 15, 0, box2)).toBe(true)
    expect(shapesCollide(0, 0, box1, 25, 0, box2)).toBe(false)
  })

  it('should handle circle vs box', () => {
    const circle: CollisionShape = { type: 'circle', radius: 10 }
    const box: CollisionShape = { type: 'box', halfWidth: 10, halfHeight: 10 }

    expect(shapesCollide(0, 0, circle, 15, 0, box)).toBe(true)
    expect(shapesCollide(0, 0, box, 15, 0, circle)).toBe(true)
    expect(shapesCollide(0, 0, circle, 30, 0, box)).toBe(false)
  })

  it('should handle beam vs circle', () => {
    const beam: CollisionShape = { type: 'beam', direction: 'right', height: 25 }
    const circle: CollisionShape = { type: 'circle', radius: 10 }

    expect(shapesCollide(0, 0, beam, 100, 0, circle)).toBe(true)
    expect(shapesCollide(0, 0, beam, -100, 0, circle)).toBe(false)
    expect(shapesCollide(0, 0, beam, 100, 50, circle)).toBe(false)
  })

  it('should handle beam vs box', () => {
    const beam: CollisionShape = { type: 'beam', direction: 'right', height: 25 }
    const box: CollisionShape = { type: 'box', halfWidth: 15, halfHeight: 15 }

    expect(shapesCollide(0, 0, beam, 100, 0, box)).toBe(true)
    expect(shapesCollide(0, 0, beam, -100, 0, box)).toBe(false)
  })

  it('should handle left-facing beam', () => {
    const beam: CollisionShape = { type: 'beam', direction: 'left', height: 25 }
    const circle: CollisionShape = { type: 'circle', radius: 10 }

    expect(shapesCollide(0, 0, beam, -100, 0, circle)).toBe(true)
    expect(shapesCollide(0, 0, beam, 100, 0, circle)).toBe(false)
  })
})

describe('canCollide', () => {
  it('should allow player bullets to hit enemies', () => {
    expect(canCollide('player_bullet', 'enemy')).toBe(true)
  })

  it('should allow player bullets to hit boss', () => {
    expect(canCollide('player_bullet', 'boss')).toBe(true)
  })

  it('should not allow player bullets to hit players', () => {
    expect(canCollide('player_bullet', 'player')).toBe(false)
  })

  it('should allow enemy bullets to hit players', () => {
    expect(canCollide('enemy_bullet', 'player')).toBe(true)
  })

  it('should not allow enemy bullets to hit enemies', () => {
    expect(canCollide('enemy_bullet', 'enemy')).toBe(false)
  })

  it('should allow orbs to hit enemies', () => {
    expect(canCollide('orb', 'enemy')).toBe(true)
  })

  it('should allow orbs to hit enemy bullets', () => {
    expect(canCollide('orb', 'enemy_bullet')).toBe(true)
  })

  it('should allow beams to hit enemies and boss', () => {
    expect(canCollide('beam', 'enemy')).toBe(true)
    expect(canCollide('beam', 'boss')).toBe(true)
  })

  it('should allow missiles to hit enemies and boss', () => {
    expect(canCollide('missile', 'enemy')).toBe(true)
    expect(canCollide('missile', 'boss')).toBe(true)
  })
})

describe('CollisionSystem', () => {
  let system: CollisionSystem

  beforeEach(() => {
    system = new CollisionSystem()
  })

  function createEntity(
    id: number,
    x: number,
    y: number,
    shape: CollisionShape,
    layer: 'player_bullet' | 'enemy_bullet' | 'player' | 'enemy' | 'boss' | 'orb' | 'beam' | 'missile'
  ): CollidableEntity {
    return { id, x, y, shape, layer }
  }

  describe('checkCollision', () => {
    it('should detect collision between compatible layers', () => {
      const bullet = createEntity(1, 0, 0, { type: 'circle', radius: 5 }, 'player_bullet')
      const enemy = createEntity(2, 8, 0, { type: 'circle', radius: 10 }, 'enemy')

      expect(system.checkCollision(bullet, enemy)).toBe(true)
    })

    it('should not detect collision between incompatible layers', () => {
      const bullet1 = createEntity(1, 0, 0, { type: 'circle', radius: 5 }, 'player_bullet')
      const bullet2 = createEntity(2, 5, 0, { type: 'circle', radius: 5 }, 'player_bullet')

      expect(system.checkCollision(bullet1, bullet2)).toBe(false)
    })

    it('should not detect collision if already hit', () => {
      const bullet = createEntity(1, 0, 0, { type: 'circle', radius: 5 }, 'player_bullet')
      bullet.hitEntities = new Set([2])
      const enemy = createEntity(2, 5, 0, { type: 'circle', radius: 10 }, 'enemy')

      expect(system.checkCollision(bullet, enemy)).toBe(false)
    })

    it('should detect player vs enemy bullet', () => {
      const player = createEntity(1, 0, 0, { type: 'box', halfWidth: 8, halfHeight: 6 }, 'player')
      const bullet = createEntity(2, 5, 0, { type: 'circle', radius: 6 }, 'enemy_bullet')

      expect(system.checkCollision(player, bullet)).toBe(true)
    })
  })

  describe('findCollisions', () => {
    it('should find all collisions in entity list', () => {
      const entities = [
        createEntity(1, 0, 0, { type: 'circle', radius: 10 }, 'player_bullet'),
        createEntity(2, 15, 0, { type: 'circle', radius: 10 }, 'enemy'),
        createEntity(3, 100, 0, { type: 'circle', radius: 10 }, 'enemy'),
      ]

      const collisions = system.findCollisions(entities)
      expect(collisions).toHaveLength(1)
      expect(collisions[0]![0].id).toBe(1)
      expect(collisions[0]![1].id).toBe(2)
    })

    it('should return empty array when no collisions', () => {
      const entities = [
        createEntity(1, 0, 0, { type: 'circle', radius: 5 }, 'player_bullet'),
        createEntity(2, 100, 0, { type: 'circle', radius: 5 }, 'enemy'),
      ]

      expect(system.findCollisions(entities)).toHaveLength(0)
    })
  })

  describe('findGroupCollisions', () => {
    it('should find collisions between two groups', () => {
      const bullets = [
        createEntity(1, 0, 0, { type: 'circle', radius: 5 }, 'player_bullet'),
        createEntity(2, 50, 0, { type: 'circle', radius: 5 }, 'player_bullet'),
      ]
      const enemies = [
        createEntity(10, 8, 0, { type: 'circle', radius: 10 }, 'enemy'),
        createEntity(11, 100, 0, { type: 'circle', radius: 10 }, 'enemy'),
      ]

      const collisions = system.findGroupCollisions(bullets, enemies)
      expect(collisions).toHaveLength(1)
      expect(collisions[0]![0].id).toBe(1)
      expect(collisions[0]![1].id).toBe(10)
    })

    it('should find multiple collisions from same entity', () => {
      const bullets = [
        createEntity(1, 0, 0, { type: 'circle', radius: 20 }, 'player_bullet'),
      ]
      const enemies = [
        createEntity(10, 10, 0, { type: 'circle', radius: 10 }, 'enemy'),
        createEntity(11, 10, 15, { type: 'circle', radius: 10 }, 'enemy'),
      ]

      const collisions = system.findGroupCollisions(bullets, enemies)
      expect(collisions).toHaveLength(2)
    })
  })

  describe('findFirstCollision', () => {
    it('should find first collision', () => {
      const bullet = createEntity(1, 0, 0, { type: 'circle', radius: 10 }, 'player_bullet')
      const enemies = [
        createEntity(10, 15, 0, { type: 'circle', radius: 10 }, 'enemy'),
        createEntity(11, 100, 0, { type: 'circle', radius: 10 }, 'enemy'),
      ]

      const hit = system.findFirstCollision(bullet, enemies)
      expect(hit).not.toBeNull()
      expect(hit!.id).toBe(10)
    })

    it('should return null when no collision', () => {
      const bullet = createEntity(1, 0, 0, { type: 'circle', radius: 5 }, 'player_bullet')
      const enemies = [
        createEntity(10, 100, 0, { type: 'circle', radius: 10 }, 'enemy'),
      ]

      expect(system.findFirstCollision(bullet, enemies)).toBeNull()
    })
  })

  describe('findAtPoint', () => {
    it('should find entities at point', () => {
      const entities = [
        createEntity(1, 0, 0, { type: 'circle', radius: 10 }, 'enemy'),
        createEntity(2, 50, 0, { type: 'circle', radius: 10 }, 'enemy'),
      ]

      const found = system.findAtPoint(5, 5, entities)
      expect(found).toHaveLength(1)
      expect(found[0]!.id).toBe(1)
    })

    it('should find multiple entities at same point', () => {
      const entities = [
        createEntity(1, 0, 0, { type: 'circle', radius: 20 }, 'enemy'),
        createEntity(2, 10, 0, { type: 'circle', radius: 20 }, 'enemy'),
      ]

      const found = system.findAtPoint(5, 0, entities)
      expect(found).toHaveLength(2)
    })

    it('should work with box shapes', () => {
      const entities = [
        createEntity(1, 0, 0, { type: 'box', halfWidth: 10, halfHeight: 10 }, 'player'),
      ]

      expect(system.findAtPoint(5, 5, entities)).toHaveLength(1)
      expect(system.findAtPoint(15, 15, entities)).toHaveLength(0)
    })
  })

  describe('pointInAny', () => {
    it('should return true if point in any entity', () => {
      const entities = [
        createEntity(1, 0, 0, { type: 'circle', radius: 10 }, 'enemy'),
      ]

      expect(system.pointInAny(5, 0, entities)).toBe(true)
    })

    it('should return false if point not in any entity', () => {
      const entities = [
        createEntity(1, 0, 0, { type: 'circle', radius: 10 }, 'enemy'),
      ]

      expect(system.pointInAny(50, 0, entities)).toBe(false)
    })
  })
})

describe('HITBOX_SIZES', () => {
  it('should have player hitbox', () => {
    expect(HITBOX_SIZES.player.halfWidth).toBe(8)
    expect(HITBOX_SIZES.player.halfHeight).toBe(6)
  })

  it('should have all enemy types', () => {
    expect(HITBOX_SIZES.enemy.scout).toBe(20)
    expect(HITBOX_SIZES.enemy.tank).toBe(30)
    expect(HITBOX_SIZES.enemy.carrier).toBe(35)
    expect(HITBOX_SIZES.enemy.mine).toBe(15)
  })

  it('should have all boss types', () => {
    expect(HITBOX_SIZES.boss[0]).toBe(40)
    expect(HITBOX_SIZES.boss[4]).toBe(55)
    expect(HITBOX_SIZES.boss[5]).toBe(50)
  })

  it('should have bullet types', () => {
    expect(HITBOX_SIZES.bullet.default).toBe(6)
    expect(HITBOX_SIZES.bullet.big).toBe(10)
    expect(HITBOX_SIZES.bullet.mega).toBe(12)
  })
})

describe('shape factory functions', () => {
  describe('createPlayerShape', () => {
    it('should create box shape with player dimensions', () => {
      const shape = createPlayerShape()
      expect(shape.type).toBe('box')
      if (shape.type === 'box') {
        expect(shape.halfWidth).toBe(8)
        expect(shape.halfHeight).toBe(6)
      }
    })
  })

  describe('createEnemyShape', () => {
    it('should create circle shape for each enemy type', () => {
      const scout = createEnemyShape('scout')
      expect(scout.type).toBe('circle')
      if (scout.type === 'circle') {
        expect(scout.radius).toBe(20)
      }

      const tank = createEnemyShape('tank')
      if (tank.type === 'circle') {
        expect(tank.radius).toBe(30)
      }
    })
  })

  describe('createBossShape', () => {
    it('should create circle shape for each boss type', () => {
      const boss0 = createBossShape(0)
      expect(boss0.type).toBe('circle')
      if (boss0.type === 'circle') {
        expect(boss0.radius).toBe(40)
      }

      const boss4 = createBossShape(4)
      if (boss4.type === 'circle') {
        expect(boss4.radius).toBe(55)
      }
    })
  })

  describe('createBulletShape', () => {
    it('should create default bullet shape', () => {
      const shape = createBulletShape()
      expect(shape.type).toBe('circle')
      if (shape.type === 'circle') {
        expect(shape.radius).toBe(6)
      }
    })

    it('should create specific bullet shape', () => {
      const big = createBulletShape('big')
      if (big.type === 'circle') {
        expect(big.radius).toBe(10)
      }

      const mega = createBulletShape('mega')
      if (mega.type === 'circle') {
        expect(mega.radius).toBe(12)
      }
    })

    it('should fall back to default for unknown type', () => {
      const shape = createBulletShape('unknown')
      if (shape.type === 'circle') {
        expect(shape.radius).toBe(6)
      }
    })
  })

  describe('createBeamShape', () => {
    it('should create beam shape', () => {
      const shape = createBeamShape()
      expect(shape.type).toBe('beam')
      if (shape.type === 'beam') {
        expect(shape.direction).toBe('right')
        expect(shape.height).toBe(25)
      }
    })
  })

  describe('createOrbShape', () => {
    it('should create orb shape', () => {
      const shape = createOrbShape()
      expect(shape.type).toBe('circle')
      if (shape.type === 'circle') {
        expect(shape.radius).toBe(8)
      }
    })
  })
})
