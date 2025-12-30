import { describe, it, expect, beforeEach } from 'vitest'
import { Enemy, ENEMY_STATS, type EnemyType } from './Enemy.ts'

describe('Enemy', () => {
  let enemy: Enemy

  beforeEach(() => {
    enemy = Enemy.create(1, 'grunt', 100, 50)
  })

  describe('constructor', () => {
    it('should create enemy with correct initial values', () => {
      expect(enemy.id).toBe(1)
      expect(enemy.type).toBe('grunt')
      expect(enemy.x).toBe(100)
      expect(enemy.y).toBe(50)
      expect(enemy.health).toBe(20)
      expect(enemy.maxHealth).toBe(20)
      expect(enemy.points).toBe(100)
    })

    it('should set velocity based on speed', () => {
      expect(enemy.vx).toBe(-2)  // Moves left
    })

    it('should accept custom stats', () => {
      const custom = new Enemy(2, {
        type: 'grunt',
        x: 0,
        y: 0,
        stats: { health: 50, points: 200 },
      })

      expect(custom.health).toBe(50)
      expect(custom.points).toBe(200)
    })
  })

  describe('ENEMY_STATS', () => {
    it('should have stats for all enemy types', () => {
      const types: EnemyType[] = [
        'grunt', 'shooter', 'swerver', 'tank', 'speeder', 'bomber',
        'sniper', 'carrier', 'mine', 'spiral', 'shield', 'splitter',
      ]

      for (const type of types) {
        expect(ENEMY_STATS[type]).toBeDefined()
        expect(ENEMY_STATS[type].health).toBeGreaterThan(0)
        expect(ENEMY_STATS[type].points).toBeGreaterThan(0)
      }
    })

    it('should have shield config for shield enemy', () => {
      expect(ENEMY_STATS.shield.hasShield).toBe(true)
      expect(ENEMY_STATS.shield.shieldHealth).toBe(50)
    })

    it('should have splitCount for splitter enemy', () => {
      expect(ENEMY_STATS.splitter.splitCount).toBe(2)
    })
  })

  describe('getCollisionRadius', () => {
    it('should return different radii for different types', () => {
      const grunt = Enemy.create(1, 'grunt', 0, 0)
      const tank = Enemy.create(2, 'tank', 0, 0)
      const mine = Enemy.create(3, 'mine', 0, 0)

      expect(grunt.getCollisionRadius()).toBe(20)
      expect(tank.getCollisionRadius()).toBe(30)
      expect(mine.getCollisionRadius()).toBe(15)
    })
  })

  describe('takeDamage', () => {
    it('should reduce health', () => {
      enemy.takeDamage(10)
      expect(enemy.health).toBe(10)
    })

    it('should return false if enemy survives', () => {
      expect(enemy.takeDamage(10)).toBe(false)
    })

    it('should return true if enemy dies', () => {
      expect(enemy.takeDamage(25)).toBe(true)
      expect(enemy.health).toBeLessThanOrEqual(0)
    })

    it('should absorb damage with shield first', () => {
      const shielded = Enemy.create(1, 'shield', 0, 0)
      shielded.takeDamage(30)

      expect(shielded.shieldHealth).toBe(20)
      expect(shielded.health).toBe(50)  // Health unchanged
    })

    it('should break shield when depleted', () => {
      const shielded = Enemy.create(1, 'shield', 0, 0)
      shielded.takeDamage(60)

      expect(shielded.hasShield).toBe(false)
      expect(shielded.shieldHealth).toBe(0)
    })

    it('should damage health after shield breaks', () => {
      const shielded = Enemy.create(1, 'shield', 0, 0)
      shielded.takeDamage(60)  // Break shield
      shielded.takeDamage(20)  // Damage health

      expect(shielded.health).toBe(30)
    })
  })

  describe('shooting', () => {
    it('should not shoot if no fire rate', () => {
      expect(enemy.canShoot()).toBe(false)
    })

    it('should shoot if has fire rate and timer ready', () => {
      const shooter = Enemy.create(1, 'shooter', 0, 0)
      expect(shooter.canShoot()).toBe(true)
    })

    it('should not shoot if timer active', () => {
      const shooter = Enemy.create(1, 'shooter', 0, 0)
      shooter.shootTimer = 30
      expect(shooter.canShoot()).toBe(false)
    })

    it('should reset shoot timer', () => {
      const shooter = Enemy.create(1, 'shooter', 0, 0)
      shooter.resetShootTimer()
      expect(shooter.shootTimer).toBe(90)  // shooter fire rate
    })
  })

  describe('canSplit', () => {
    it('should return true for splitter with split count', () => {
      const splitter = Enemy.create(1, 'splitter', 0, 0)
      expect(splitter.canSplit()).toBe(true)
    })

    it('should return false for non-splitter', () => {
      expect(enemy.canSplit()).toBe(false)
    })

    it('should return false if split count exhausted', () => {
      const splitter = Enemy.create(1, 'splitter', 0, 0)
      splitter.splitCount = 0
      expect(splitter.canSplit()).toBe(false)
    })
  })

  describe('getHealthPercent', () => {
    it('should return health percentage', () => {
      enemy.health = 10
      expect(enemy.getHealthPercent()).toBe(0.5)
    })

    it('should return 0 when health is 0', () => {
      enemy.health = 0
      expect(enemy.getHealthPercent()).toBe(0)
    })
  })

  describe('updateBehavior', () => {
    it('should update sine behavior', () => {
      const swerver = Enemy.create(1, 'swerver', 0, 0)
      swerver.frame = 10
      swerver.updateBehavior(1 / 60)

      expect(swerver.vy).not.toBe(0)
    })

    it('should update circle behavior', () => {
      const spiral = Enemy.create(1, 'spiral', 0, 0)
      spiral.frame = 10
      spiral.updateBehavior(1 / 60)

      expect(spiral.vx).not.toBe(-ENEMY_STATS.spiral.speed)
    })

    it('should stop stationary enemies', () => {
      const mine = Enemy.create(1, 'mine', 0, 0)
      mine.vx = 5
      mine.vy = 5
      mine.updateBehavior(1 / 60)

      expect(mine.vx).toBe(0)
      expect(mine.vy).toBe(0)
    })
  })

  describe('update', () => {
    it('should move enemy', () => {
      const startX = enemy.x
      enemy.update(1 / 60)
      expect(enemy.x).toBeLessThan(startX)
    })

    it('should decrement shoot timer', () => {
      const shooter = Enemy.create(1, 'shooter', 0, 0)
      shooter.shootTimer = 10
      shooter.update(1 / 60)
      expect(shooter.shootTimer).toBe(9)
    })

    it('should increment frame', () => {
      enemy.update(1 / 60)
      expect(enemy.frame).toBe(1)
    })
  })

  describe('isDead', () => {
    it('should return false when alive', () => {
      expect(enemy.isDead()).toBe(false)
    })

    it('should return true when health depleted', () => {
      enemy.health = 0
      expect(enemy.isDead()).toBe(true)
    })
  })

  describe('factory methods', () => {
    it('should create basic enemy', () => {
      const e = Enemy.create(5, 'tank', 200, 100)
      expect(e.id).toBe(5)
      expect(e.type).toBe('tank')
      expect(e.x).toBe(200)
      expect(e.y).toBe(100)
    })

    it('should create enemy with weapon', () => {
      const e = Enemy.createWithWeapon(5, 'shooter', 200, 100, 'spread_small')
      expect(e.equippedWeapon).toBe('spread_small')
    })
  })

  describe('equipped weapon', () => {
    it('should store equipped weapon', () => {
      const e = new Enemy(1, {
        type: 'shooter',
        x: 0,
        y: 0,
        equippedWeapon: 'laser_small',
      })

      expect(e.equippedWeapon).toBe('laser_small')
    })

    it('should be undefined by default', () => {
      expect(enemy.equippedWeapon).toBeUndefined()
    })
  })
})
