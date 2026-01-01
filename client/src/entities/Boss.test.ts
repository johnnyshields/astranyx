import { describe, it, expect, beforeEach } from 'vitest'
import { Boss, BOSS_STATS, BOSS_NAMES, type BossType } from './Boss.ts'

describe('Boss', () => {
  let boss: Boss

  beforeEach(() => {
    boss = Boss.create(1, 0, 500, 0)  // CLASSIC boss
  })

  describe('constructor', () => {
    it('should create boss with correct initial values', () => {
      expect(boss.id).toBe(1)
      expect(boss.type).toBe(0)
      expect(boss.x).toBe(500)
      expect(boss.y).toBe(0)
      expect(boss.health).toBe(500)
      expect(boss.maxHealth).toBe(500)
      expect(boss.points).toBe(5000)
      expect(boss.phase).toBe(0)
    })

    it('should initialize TWIN boss with twin data', () => {
      const twin = Boss.create(1, 1, 0, 0)
      expect(twin.twin).not.toBeNull()
      expect(twin.twin?.y).toBe(100)
      expect(twin.twin?.vy).toBe(0)
    })

    it('should initialize LASER boss with charge data', () => {
      const laser = Boss.create(1, 3, 0, 0)
      expect(laser.charging).toBe(false)
      expect(laser.chargeTime).toBe(0)
    })

    it('should initialize WALL boss with segments', () => {
      const wall = Boss.create(1, 4, 0, 0)
      expect(wall.segments).toHaveLength(7)
      expect(wall.segments[0]?.hp).toBe(100)
    })
  })

  describe('BOSS_STATS', () => {
    it('should have stats for all boss types', () => {
      const types: BossType[] = [0, 1, 2, 3, 4, 5]

      for (const type of types) {
        expect(BOSS_STATS[type]).toBeDefined()
        expect(BOSS_STATS[type].health).toBeGreaterThan(0)
        expect(BOSS_STATS[type].points).toBeGreaterThan(0)
        expect(BOSS_STATS[type].phases).toBeGreaterThan(0)
      }
    })

    it('should have increasing health for later bosses', () => {
      expect(BOSS_STATS[5].health).toBeGreaterThan(BOSS_STATS[0].health)
    })
  })

  describe('BOSS_NAMES', () => {
    it('should have names for all boss types', () => {
      expect(BOSS_NAMES[0]).toBe('CLASSIC')
      expect(BOSS_NAMES[1]).toBe('TWIN')
      expect(BOSS_NAMES[5]).toBe('FINAL')
    })
  })

  describe('getCollisionRadius', () => {
    it('should return different radii for different types', () => {
      const classic = Boss.create(1, 0, 0, 0)
      const wall = Boss.create(2, 4, 0, 0)
      const final = Boss.create(3, 5, 0, 0)

      expect(classic.getCollisionRadius()).toBe(40)
      expect(wall.getCollisionRadius()).toBe(55)
      expect(final.getCollisionRadius()).toBe(50)
    })
  })

  describe('takeDamage', () => {
    it('should reduce health', () => {
      boss.takeDamage(100)
      expect(boss.health).toBe(400)
    })

    it('should return false if boss survives', () => {
      expect(boss.takeDamage(100)).toBe(false)
    })

    it('should return true if boss dies', () => {
      expect(boss.takeDamage(600)).toBe(true)
    })

    it('should advance phase when health drops', () => {
      // CLASSIC has 2 phases, so phase 1 at 50% health
      boss.takeDamage(300)  // 40% health
      expect(boss.phase).toBe(1)
    })

    it('should not exceed max phases', () => {
      boss.takeDamage(400)  // 20% health
      expect(boss.phase).toBeLessThan(boss.maxPhases)
    })
  })

  describe('takeSegmentDamage', () => {
    it('should damage segment for WALL boss', () => {
      const wall = Boss.create(1, 4, 0, 0)
      wall.takeSegmentDamage(0, 50)
      expect(wall.segments[0]?.hp).toBe(50)
    })

    it('should damage main health when segment destroyed', () => {
      const wall = Boss.create(1, 4, 0, 0)
      const initialHealth = wall.health
      wall.takeSegmentDamage(0, 100)
      expect(wall.health).toBe(initialHealth - 100)
    })

    it('should return false for non-WALL boss', () => {
      expect(boss.takeSegmentDamage(0, 50)).toBe(false)
    })
  })

  describe('getHealthPercent', () => {
    it('should return health percentage', () => {
      boss.health = 250
      expect(boss.getHealthPercent()).toBe(0.5)
    })
  })

  describe('shooting', () => {
    it('should be able to shoot when timer ready', () => {
      boss.shootTimer = 0
      expect(boss.canShoot()).toBe(true)
    })

    it('should not shoot when timer active', () => {
      boss.shootTimer = 30
      expect(boss.canShoot()).toBe(false)
    })

    it('should reset shoot timer', () => {
      boss.resetShootTimer(90, 60, 0.5)
      expect(boss.shootTimer).toBe(120)
    })
  })

  describe('LASER boss charging', () => {
    let laser: Boss

    beforeEach(() => {
      laser = Boss.create(1, 3, 0, 0)
    })

    it('should not be charging initially', () => {
      expect(laser.isCharging()).toBe(false)
    })

    it('should start charging', () => {
      laser.startCharging()
      expect(laser.isCharging()).toBe(true)
      expect(laser.chargeTime).toBe(0)
    })

    it('should update charge time', () => {
      laser.startCharging()
      laser.updateCharge(0.5)
      expect(laser.chargeTime).toBe(0.5)
    })

    it('should fire when fully charged', () => {
      laser.startCharging()
      laser.updateCharge(1)
      expect(laser.updateCharge(1.5)).toBe(true)
      expect(laser.isCharging()).toBe(false)
    })

    it('should return charge percentage', () => {
      laser.startCharging()
      laser.chargeTime = 1
      expect(laser.getChargePercent()).toBe(0.5)
    })

    it('should not start charging for non-LASER boss', () => {
      boss.startCharging()
      expect(boss.isCharging()).toBe(false)
    })
  })

  describe('TWIN boss', () => {
    let twin: Boss

    beforeEach(() => {
      twin = Boss.create(1, 1, 0, 0)
    })

    it('should update twin movement', () => {
      const initialY = twin.twin!.y
      twin.updateTwin(1 / 60, 0.8)  // Random > 0.5 moves up
      expect(twin.twin!.y).not.toBe(initialY)
    })

    it('should clamp twin Y position', () => {
      twin.twin!.y = 300
      twin.updateTwin(1 / 60, 0.5)
      expect(twin.twin!.y).toBeLessThanOrEqual(200)
    })

    it('should return twin Y', () => {
      twin.twin!.y = 50
      expect(twin.getTwinY()).toBe(50)
    })

    it('should return 0 for non-TWIN boss', () => {
      expect(boss.getTwinY()).toBe(0)
    })
  })

  describe('WALL boss segments', () => {
    let wall: Boss

    beforeEach(() => {
      wall = Boss.create(1, 4, 0, 0)
    })

    it('should return living segments', () => {
      wall.segments[0]!.hp = 0
      wall.segments[1]!.hp = 0
      expect(wall.getLivingSegments()).toHaveLength(5)
    })

    it('should return segment count', () => {
      expect(wall.getSegmentCount()).toBe(7)
    })
  })

  describe('getPatternIndex', () => {
    it('should return pattern based on frame', () => {
      boss.frame = 0
      expect(boss.getPatternIndex()).toBe(0)

      boss.frame = 100
      expect(boss.getPatternIndex()).toBe(1)

      boss.frame = 400
      expect(boss.getPatternIndex()).toBe(0)  // Wraps
    })
  })

  describe('getName', () => {
    it('should return boss name', () => {
      expect(boss.getName()).toBe('CLASSIC')

      const final = Boss.create(1, 5, 0, 0)
      expect(final.getName()).toBe('FINAL')
    })
  })

  describe('update', () => {
    it('should decrement shoot timer', () => {
      boss.shootTimer = 10
      boss.update(1 / 60)
      expect(boss.shootTimer).toBe(9)
    })

    it('should increment frame', () => {
      boss.update(1 / 60)
      expect(boss.frame).toBe(1)
    })
  })

  describe('isDead', () => {
    it('should return false when alive', () => {
      expect(boss.isDead()).toBe(false)
    })

    it('should return true when health depleted', () => {
      boss.health = 0
      expect(boss.isDead()).toBe(true)
    })
  })

  describe('getTypeForWave', () => {
    it('should return boss type based on wave', () => {
      expect(Boss.getTypeForWave(5)).toBe(0)
      expect(Boss.getTypeForWave(10)).toBe(1)
      expect(Boss.getTypeForWave(15)).toBe(2)
      expect(Boss.getTypeForWave(30)).toBe(5)
    })

    it('should cap at type 5', () => {
      expect(Boss.getTypeForWave(100)).toBe(5)
    })
  })
})
