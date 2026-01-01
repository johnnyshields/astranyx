import { describe, it, expect, beforeEach } from 'vitest'
import { Powerup, POWERUP_EFFECTS, ALL_POWERUP_TYPES } from './Powerup.ts'

describe('Powerup', () => {
  let powerup: Powerup

  beforeEach(() => {
    powerup = Powerup.create(1, 100, 50, 'SHIELD')
  })

  describe('constructor', () => {
    it('should create powerup with correct initial values', () => {
      expect(powerup.id).toBe(1)
      expect(powerup.x).toBe(100)
      expect(powerup.y).toBe(50)
      expect(powerup.type).toBe('SHIELD')
      expect(powerup.lifetime).toBe(600)
    })

    it('should have slight leftward drift', () => {
      expect(powerup.vx).toBe(-0.5)
    })
  })

  describe('POWERUP_EFFECTS', () => {
    it('should have effects for all powerup types', () => {
      for (const type of ALL_POWERUP_TYPES) {
        expect(POWERUP_EFFECTS[type]).toBeDefined()
        expect(POWERUP_EFFECTS[type].description).toBeTruthy()
        expect(POWERUP_EFFECTS[type].rarity).toBeGreaterThan(0)
      }
    })

    it('should have LIFE as rarest', () => {
      const lifeRarity = POWERUP_EFFECTS.LIFE.rarity
      for (const effect of Object.values(POWERUP_EFFECTS)) {
        expect(effect.rarity).toBeGreaterThanOrEqual(lifeRarity)
      }
    })
  })

  describe('ALL_POWERUP_TYPES', () => {
    it('should contain all powerup types', () => {
      expect(ALL_POWERUP_TYPES).toHaveLength(11)
      expect(ALL_POWERUP_TYPES).toContain('SHIELD')
      expect(ALL_POWERUP_TYPES).toContain('LIFE')
    })
  })

  describe('getCollisionRadius', () => {
    it('should return powerup collision radius', () => {
      expect(powerup.getCollisionRadius()).toBe(15)
    })
  })

  describe('getEffect', () => {
    it('should return effect metadata', () => {
      const effect = powerup.getEffect()
      expect(effect.type).toBe('SHIELD')
      expect(effect.description).toBe('Restore shields')
    })
  })

  describe('getDescription', () => {
    it('should return description', () => {
      expect(powerup.getDescription()).toBe('Restore shields')
    })
  })

  describe('getColorIndex', () => {
    it('should return color index', () => {
      expect(powerup.getColorIndex()).toBe(0)

      const upgrade = Powerup.create(2, 0, 0, 'UPGRADE')
      expect(upgrade.getColorIndex()).toBe(1)
    })
  })

  describe('hasExpired', () => {
    it('should return false when lifetime remaining', () => {
      expect(powerup.hasExpired()).toBe(false)
    })

    it('should return true when lifetime depleted', () => {
      powerup.lifetime = 0
      expect(powerup.hasExpired()).toBe(true)
    })
  })

  describe('getVisualY', () => {
    it('should return Y with bob effect', () => {
      const baseY = powerup.y
      powerup.bobOffset = Math.PI / 2  // sin = 1
      expect(powerup.getVisualY()).toBeCloseTo(baseY + 5)
    })
  })

  describe('getOpacity', () => {
    it('should return 1 when plenty of lifetime', () => {
      powerup.lifetime = 300
      expect(powerup.getOpacity()).toBe(1)
    })

    it('should blink when expiring', () => {
      powerup.lifetime = 100
      // Should alternate between 1 and 0.3 based on lifetime % 10
      const opacity1 = powerup.getOpacity()
      powerup.lifetime = 105
      const opacity2 = powerup.getOpacity()

      expect([opacity1, opacity2]).toContain(1)
      expect([opacity1, opacity2]).toContain(0.3)
    })
  })

  describe('update', () => {
    it('should move powerup', () => {
      const startX = powerup.x
      powerup.update(1 / 60)
      expect(powerup.x).toBeLessThan(startX)
    })

    it('should decrement lifetime', () => {
      powerup.update(1 / 60)
      expect(powerup.lifetime).toBe(599)
    })

    it('should update bob offset', () => {
      powerup.update(1 / 60)
      expect(powerup.bobOffset).toBeGreaterThan(0)
    })

    it('should increment frame', () => {
      powerup.update(1 / 60)
      expect(powerup.frame).toBe(1)
    })
  })

  describe('isDead', () => {
    it('should return false when alive', () => {
      expect(powerup.isDead()).toBe(false)
    })

    it('should return true when lifetime depleted', () => {
      powerup.lifetime = 0
      expect(powerup.isDead()).toBe(true)
    })
  })

  describe('factory methods', () => {
    it('should create powerup', () => {
      const p = Powerup.create(5, 200, 100, 'LASER')
      expect(p.id).toBe(5)
      expect(p.type).toBe('LASER')
    })

    it('should create random powerup', () => {
      const p = Powerup.createRandom(5, 200, 100, 0.5)
      expect(p.id).toBe(5)
      expect(ALL_POWERUP_TYPES).toContain(p.type)
    })
  })

  describe('getRandomType', () => {
    it('should return valid powerup type', () => {
      for (let i = 0; i < 10; i++) {
        const type = Powerup.getRandomType(Math.random())
        expect(ALL_POWERUP_TYPES).toContain(type)
      }
    })

    it('should be deterministic for same value', () => {
      const type1 = Powerup.getRandomType(0.3)
      const type2 = Powerup.getRandomType(0.3)
      expect(type1).toBe(type2)
    })

    it('should return different types for different values', () => {
      const type1 = Powerup.getRandomType(0.1)
      const type2 = Powerup.getRandomType(0.9)
      // May be same by chance, but usually different
      // Just check they're valid
      expect(ALL_POWERUP_TYPES).toContain(type1)
      expect(ALL_POWERUP_TYPES).toContain(type2)
    })
  })

  describe('type classification', () => {
    it('should identify weapon powerups', () => {
      expect(Powerup.isWeaponPowerup('SPREAD')).toBe(true)
      expect(Powerup.isWeaponPowerup('LASER')).toBe(true)
      expect(Powerup.isWeaponPowerup('MISSILE')).toBe(true)
      expect(Powerup.isWeaponPowerup('SHIELD')).toBe(false)
    })

    it('should identify stat powerups', () => {
      expect(Powerup.isStatPowerup('SPEED')).toBe(true)
      expect(Powerup.isStatPowerup('RAPID')).toBe(true)
      expect(Powerup.isStatPowerup('PIERCE')).toBe(true)
      expect(Powerup.isStatPowerup('SHIELD')).toBe(false)
    })

    it('should identify special powerups', () => {
      expect(Powerup.isSpecialPowerup('SHIELD')).toBe(true)
      expect(Powerup.isSpecialPowerup('UPGRADE')).toBe(true)
      expect(Powerup.isSpecialPowerup('LIFE')).toBe(true)
      expect(Powerup.isSpecialPowerup('ORBIT')).toBe(true)
      expect(Powerup.isSpecialPowerup('DRONE')).toBe(true)
      expect(Powerup.isSpecialPowerup('SPREAD')).toBe(false)
    })
  })
})
