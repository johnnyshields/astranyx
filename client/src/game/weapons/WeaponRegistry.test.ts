import { describe, it, expect } from 'vitest'
import { WeaponRegistry } from './WeaponRegistry.ts'
import { ALL_WEAPON_TYPES } from './WeaponTypes.ts'

describe('WeaponRegistry', () => {
  describe('getStats', () => {
    it('should return stats for vulcan', () => {
      const stats = WeaponRegistry.getStats('vulcan')
      expect(stats.type).toBe('vulcan')
      expect(stats.name).toBe('Vulcan')
      expect(stats.ammoType).toBe('BULLET')
      expect(stats.damage).toBe(8)
    })

    it('should return stats for all weapon types', () => {
      for (const type of ALL_WEAPON_TYPES) {
        const stats = WeaponRegistry.getStats(type)
        expect(stats).toBeDefined()
        expect(stats.type).toBe(type)
        expect(stats.name).toBeDefined()
        expect(stats.ammoType).toBeDefined()
      }
    })
  })

  describe('getAllStats', () => {
    it('should return all 16 weapons', () => {
      const allStats = WeaponRegistry.getAllStats()
      expect(Object.keys(allStats).length).toBe(16)
    })
  })

  describe('getAmmoColor', () => {
    it('should return RGBA color for BULLET', () => {
      const color = WeaponRegistry.getAmmoColor('BULLET')
      expect(color).toHaveLength(4)
      expect(color[0]).toBeCloseTo(1.0, 2) // Gold-ish
    })

    it('should return different colors for different ammo types', () => {
      const bullet = WeaponRegistry.getAmmoColor('BULLET')
      const energy = WeaponRegistry.getAmmoColor('ENERGY')
      expect(bullet).not.toEqual(energy)
    })
  })

  describe('getWeaponColor', () => {
    it('should return RGBA color for weapon', () => {
      const color = WeaponRegistry.getWeaponColor('vulcan')
      expect(color).toHaveLength(4)
      expect(color[3]).toBe(1.0) // Full alpha
    })
  })

  describe('getBulletType', () => {
    it('should return bullet visual type', () => {
      expect(WeaponRegistry.getBulletType('vulcan')).toBe('shot')
      expect(WeaponRegistry.getBulletType('laser_small')).toBe('laser')
      expect(WeaponRegistry.getBulletType('flame')).toBe('flame')
    })
  })

  describe('getAvailableWeapons', () => {
    it('should return base weapons at wave 1', () => {
      const weapons = WeaponRegistry.getAvailableWeapons(1)
      expect(weapons).toContain('vulcan')
      expect(weapons).toContain('shotgun')
      expect(weapons).toContain('spread_small')
      expect(weapons.length).toBe(3)
    })

    it('should unlock more weapons at wave 3', () => {
      const weapons = WeaponRegistry.getAvailableWeapons(3)
      expect(weapons).toContain('missile')
      expect(weapons).toContain('flame')
      expect(weapons.length).toBe(5)
    })

    it('should unlock all weapons by wave 12', () => {
      const weapons = WeaponRegistry.getAvailableWeapons(12)
      expect(weapons).toContain('railgun')
      expect(weapons).toContain('mine')
      expect(weapons).toContain('sword')
      expect(weapons.length).toBe(16)
    })
  })

  describe('isContinuous', () => {
    it('should return true for flame', () => {
      expect(WeaponRegistry.isContinuous('flame')).toBe(true)
    })

    it('should return true for beam weapons', () => {
      expect(WeaponRegistry.isContinuous('laser_small')).toBe(true)
      expect(WeaponRegistry.isContinuous('laser_large')).toBe(true)
    })

    it('should return false for standard weapons', () => {
      expect(WeaponRegistry.isContinuous('vulcan')).toBe(false)
      expect(WeaponRegistry.isContinuous('missile')).toBe(false)
    })
  })

  describe('isBeam', () => {
    it('should return true for laser weapons', () => {
      expect(WeaponRegistry.isBeam('laser_small')).toBe(true)
      expect(WeaponRegistry.isBeam('laser_large')).toBe(true)
    })

    it('should return false for projectile weapons', () => {
      expect(WeaponRegistry.isBeam('vulcan')).toBe(false)
      expect(WeaponRegistry.isBeam('flame')).toBe(false)
    })
  })

  describe('isHoming', () => {
    it('should return true for missile', () => {
      expect(WeaponRegistry.isHoming('missile')).toBe(true)
    })

    it('should return false for non-homing weapons', () => {
      expect(WeaponRegistry.isHoming('vulcan')).toBe(false)
      expect(WeaponRegistry.isHoming('cannon')).toBe(false)
    })
  })

  describe('isExplosive', () => {
    it('should return true for cannon and grenade', () => {
      expect(WeaponRegistry.isExplosive('cannon')).toBe(true)
      expect(WeaponRegistry.isExplosive('grenade')).toBe(true)
    })

    it('should return false for non-explosive weapons', () => {
      expect(WeaponRegistry.isExplosive('vulcan')).toBe(false)
      expect(WeaponRegistry.isExplosive('missile')).toBe(false)
    })
  })

  describe('getWeaponsByAmmoType', () => {
    it('should return all BULLET weapons', () => {
      const bulletWeapons = WeaponRegistry.getWeaponsByAmmoType('BULLET')
      expect(bulletWeapons).toContain('vulcan')
      expect(bulletWeapons).toContain('shotgun')
      expect(bulletWeapons).toContain('spread_small')
      expect(bulletWeapons).toContain('spread_large')
      expect(bulletWeapons).toContain('railgun')
      expect(bulletWeapons.length).toBe(5)
    })

    it('should return all ENERGY weapons', () => {
      const energyWeapons = WeaponRegistry.getWeaponsByAmmoType('ENERGY')
      expect(energyWeapons).toContain('sonic')
      expect(energyWeapons).toContain('laser_small')
      expect(energyWeapons).toContain('laser_large')
      expect(energyWeapons).toContain('lightning')
      expect(energyWeapons).toContain('sword')
      expect(energyWeapons.length).toBe(5)
    })

    it('should return all OIL weapons', () => {
      const oilWeapons = WeaponRegistry.getWeaponsByAmmoType('OIL')
      expect(oilWeapons).toContain('flame')
      expect(oilWeapons).toContain('acid')
      expect(oilWeapons.length).toBe(2)
    })
  })

  describe('weapon balance', () => {
    it('all weapons should have positive damage', () => {
      for (const type of ALL_WEAPON_TYPES) {
        const stats = WeaponRegistry.getStats(type)
        expect(stats.damage).toBeGreaterThan(0)
      }
    })

    it('all weapons should have positive fire rate', () => {
      for (const type of ALL_WEAPON_TYPES) {
        const stats = WeaponRegistry.getStats(type)
        expect(stats.fireRate).toBeGreaterThan(0)
      }
    })

    it('all weapons should have positive max ammo', () => {
      for (const type of ALL_WEAPON_TYPES) {
        const stats = WeaponRegistry.getStats(type)
        expect(stats.maxAmmo).toBeGreaterThan(0)
      }
    })

    it('high damage weapons should have slower fire rates', () => {
      const railgun = WeaponRegistry.getStats('railgun')
      const vulcan = WeaponRegistry.getStats('vulcan')
      expect(railgun.damage).toBeGreaterThan(vulcan.damage)
      expect(railgun.fireRate).toBeGreaterThan(vulcan.fireRate)
    })
  })
})
