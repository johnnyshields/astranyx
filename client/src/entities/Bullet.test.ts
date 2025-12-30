import { describe, it, expect } from 'vitest'
import { Bullet } from './Bullet.ts'

describe('Bullet', () => {
  describe('constructor', () => {
    it('should create bullet with position and velocity', () => {
      const bullet = new Bullet(1, 100, 200, 10, 5, {
        type: 'shot',
        damage: 15,
        pierce: 0,
        isEnemy: false,
        ownerId: 'player_1',
        lifetime: 100,
      })

      expect(bullet.id).toBe(1)
      expect(bullet.x).toBe(100)
      expect(bullet.y).toBe(200)
      expect(bullet.vx).toBe(10)
      expect(bullet.vy).toBe(5)
      expect(bullet.type).toBe('shot')
      expect(bullet.damage).toBe(15)
      expect(bullet.isEnemy).toBe(false)
    })
  })

  describe('getCollisionRadius', () => {
    it('should return larger radius for big bullets', () => {
      const big = new Bullet(1, 0, 0, 0, 0, {
        type: 'big',
        damage: 50,
        pierce: 0,
        isEnemy: true,
        ownerId: 'enemy',
        lifetime: 100,
      })
      const normal = new Bullet(2, 0, 0, 0, 0, {
        type: 'shot',
        damage: 10,
        pierce: 0,
        isEnemy: false,
        ownerId: 'player',
        lifetime: 100,
      })

      expect(big.getCollisionRadius()).toBeGreaterThan(normal.getCollisionRadius())
    })
  })

  describe('pierce mechanics', () => {
    it('should track hit entities', () => {
      const bullet = new Bullet(1, 0, 0, 10, 0, {
        type: 'shot',
        damage: 10,
        pierce: 2,
        isEnemy: false,
        ownerId: 'player',
        lifetime: 100,
      })

      expect(bullet.hasHit(5)).toBe(false)
      bullet.recordHit(5)
      expect(bullet.hasHit(5)).toBe(true)
      expect(bullet.hasHit(6)).toBe(false)
    })

    it('should consume pierce and survive', () => {
      const bullet = new Bullet(1, 0, 0, 10, 0, {
        type: 'shot',
        damage: 10,
        pierce: 2,
        isEnemy: false,
        ownerId: 'player',
        lifetime: 100,
      })

      expect(bullet.consumePierce()).toBe(true)
      expect(bullet.pierce).toBe(1)
      expect(bullet.consumePierce()).toBe(true)
      expect(bullet.pierce).toBe(0)
      expect(bullet.consumePierce()).toBe(false) // No more pierce
    })
  })

  describe('update', () => {
    it('should move by velocity', () => {
      const bullet = new Bullet(1, 0, 0, 10, 5, {
        type: 'shot',
        damage: 10,
        pierce: 0,
        isEnemy: false,
        ownerId: 'player',
        lifetime: 100,
      })

      bullet.update(1)
      expect(bullet.x).toBe(10)
      expect(bullet.y).toBe(5)
    })

    it('should decrease lifetime', () => {
      const bullet = new Bullet(1, 0, 0, 10, 0, {
        type: 'shot',
        damage: 10,
        pierce: 0,
        isEnemy: false,
        ownerId: 'player',
        lifetime: 100,
      })

      bullet.update(1)
      expect(bullet.lifetime).toBe(99)
    })

    it('should increment frame', () => {
      const bullet = new Bullet(1, 0, 0, 10, 0, {
        type: 'shot',
        damage: 10,
        pierce: 0,
        isEnemy: false,
        ownerId: 'player',
        lifetime: 100,
      })

      expect(bullet.frame).toBe(0)
      bullet.update(1)
      expect(bullet.frame).toBe(1)
    })
  })

  describe('isDead', () => {
    it('should be dead when lifetime expires', () => {
      const bullet = new Bullet(1, 0, 0, 10, 0, {
        type: 'shot',
        damage: 10,
        pierce: 0,
        isEnemy: false,
        ownerId: 'player',
        lifetime: 2,
      })

      expect(bullet.isDead()).toBe(false)
      bullet.update(1)
      expect(bullet.isDead()).toBe(false)
      bullet.update(1)
      expect(bullet.isDead()).toBe(true)
    })

    it('should be dead when killed', () => {
      const bullet = new Bullet(1, 0, 0, 10, 0, {
        type: 'shot',
        damage: 10,
        pierce: 0,
        isEnemy: false,
        ownerId: 'player',
        lifetime: 100,
      })

      expect(bullet.isDead()).toBe(false)
      bullet.kill()
      expect(bullet.isDead()).toBe(true)
    })
  })

  describe('isOffScreen', () => {
    it('should detect off-screen bullets', () => {
      const bullet = new Bullet(1, 0, 0, 10, 0, {
        type: 'shot',
        damage: 10,
        pierce: 0,
        isEnemy: false,
        ownerId: 'player',
        lifetime: 100,
      })

      expect(bullet.isOffScreen(500, 300)).toBe(false)

      bullet.x = 600
      expect(bullet.isOffScreen(500, 300)).toBe(true)

      bullet.x = 0
      bullet.y = -400
      expect(bullet.isOffScreen(500, 300)).toBe(true)
    })
  })

  describe('factory methods', () => {
    it('should create player shot', () => {
      const bullet = Bullet.createPlayerShot(1, 100, 200, 15, 0, 'player_1')
      expect(bullet.isEnemy).toBe(false)
      expect(bullet.ownerId).toBe('player_1')
      expect(bullet.type).toBe('shot')
    })

    it('should create player shot with options', () => {
      const bullet = Bullet.createPlayerShot(1, 100, 200, 15, 0, 'player_1', {
        type: 'spread',
        damage: 20,
        pierce: 1,
      })
      expect(bullet.type).toBe('spread')
      expect(bullet.damage).toBe(20)
      expect(bullet.pierce).toBe(1)
    })

    it('should create enemy shot', () => {
      const bullet = Bullet.createEnemyShot(1, 100, 200, -10, 0)
      expect(bullet.isEnemy).toBe(true)
      expect(bullet.type).toBe('enemy')
    })

    it('should create enemy shot with custom type', () => {
      const bullet = Bullet.createEnemyShot(1, 100, 200, -10, 0, 'big', 50)
      expect(bullet.type).toBe('big')
      expect(bullet.damage).toBe(50)
    })
  })
})
