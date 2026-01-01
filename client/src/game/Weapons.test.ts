import { describe, it, expect } from 'vitest'
import {
  WEAPON_STATS,
  AMMO_TYPE_COLORS,
  WEAPON_COLORS,
  WEAPON_BULLET_TYPE,
  ALL_WEAPON_TYPES,
  getAvailableWeapons,
  type WeaponType,
  type AmmoType,
} from './Weapons'

describe('Weapons', () => {
  describe('WEAPON_STATS', () => {
    it('should have stats for all 16 weapons', () => {
      expect(Object.keys(WEAPON_STATS)).toHaveLength(16)
    })

    it('should have stats for all weapon types', () => {
      for (const weaponType of ALL_WEAPON_TYPES) {
        expect(WEAPON_STATS[weaponType]).toBeDefined()
        expect(WEAPON_STATS[weaponType].type).toBe(weaponType)
      }
    })

    it('should have valid stat values', () => {
      for (const stats of Object.values(WEAPON_STATS)) {
        expect(stats.damage).toBeGreaterThan(0)
        expect(stats.fireRate).toBeGreaterThan(0)
        expect(stats.ammoPerPickup).toBeGreaterThan(0)
        expect(stats.maxAmmo).toBeGreaterThan(0)
        expect(stats.projectileCount).toBeGreaterThan(0)
        expect(stats.pierce).toBeGreaterThanOrEqual(0)
        expect(stats.lifetime).toBeGreaterThan(0)
        expect(stats.spread).toBeGreaterThanOrEqual(0)
      }
    })

    describe('BULLET weapons', () => {
      const bulletWeapons: WeaponType[] = ['vulcan', 'shotgun', 'spread_small', 'spread_large', 'railgun']

      it('should have correct ammo type', () => {
        for (const weapon of bulletWeapons) {
          expect(WEAPON_STATS[weapon].ammoType).toBe('BULLET')
        }
      })

      it('vulcan should be rapid fire', () => {
        expect(WEAPON_STATS.vulcan.fireRate).toBeLessThan(10)
        expect(WEAPON_STATS.vulcan.damage).toBeLessThan(20)
      })

      it('shotgun should fire multiple projectiles', () => {
        expect(WEAPON_STATS.shotgun.projectileCount).toBeGreaterThan(5)
        expect(WEAPON_STATS.shotgun.spread).toBeGreaterThan(0.3)
      })

      it('spread_small should be 5-way', () => {
        expect(WEAPON_STATS.spread_small.projectileCount).toBe(5)
      })

      it('spread_large should be 9-way', () => {
        expect(WEAPON_STATS.spread_large.projectileCount).toBe(9)
      })

      it('railgun should be high damage with pierce', () => {
        expect(WEAPON_STATS.railgun.damage).toBeGreaterThan(50)
        expect(WEAPON_STATS.railgun.pierce).toBeGreaterThan(0)
        expect(WEAPON_STATS.railgun.special).toBe('instant_hit')
      })
    })

    describe('BOMB weapons', () => {
      const bombWeapons: WeaponType[] = ['missile', 'cannon', 'mine', 'grenade']

      it('should have correct ammo type', () => {
        for (const weapon of bombWeapons) {
          expect(WEAPON_STATS[weapon].ammoType).toBe('BOMB')
        }
      })

      it('missile should be homing', () => {
        expect(WEAPON_STATS.missile.special).toBe('homing')
      })

      it('cannon should be explosive', () => {
        expect(WEAPON_STATS.cannon.special).toBe('explosive')
        expect(WEAPON_STATS.cannon.damage).toBeGreaterThan(80)
      })

      it('mine should be deployable', () => {
        expect(WEAPON_STATS.mine.special).toBe('deployable')
        expect(WEAPON_STATS.mine.lifetime).toBeGreaterThan(300)
      })

      it('grenade should be explosive', () => {
        expect(WEAPON_STATS.grenade.special).toBe('explosive')
      })
    })

    describe('OIL weapons', () => {
      const oilWeapons: WeaponType[] = ['flame', 'acid']

      it('should have correct ammo type', () => {
        for (const weapon of oilWeapons) {
          expect(WEAPON_STATS[weapon].ammoType).toBe('OIL')
        }
      })

      it('flame should be continuous', () => {
        expect(WEAPON_STATS.flame.special).toBe('continuous')
        expect(WEAPON_STATS.flame.fireRate).toBe(1)
        expect(WEAPON_STATS.flame.pierce).toBe(999)
      })

      it('acid should leave puddle', () => {
        expect(WEAPON_STATS.acid.special).toBe('puddle')
      })
    })

    describe('ENERGY weapons', () => {
      const energyWeapons: WeaponType[] = ['sonic', 'laser_small', 'laser_large', 'lightning', 'sword']

      it('should have correct ammo type', () => {
        for (const weapon of energyWeapons) {
          expect(WEAPON_STATS[weapon].ammoType).toBe('ENERGY')
        }
      })

      it('sonic should be wave type', () => {
        expect(WEAPON_STATS.sonic.special).toBe('wave')
        expect(WEAPON_STATS.sonic.pierce).toBeGreaterThan(0)
      })

      it('laser_small should be thin beam', () => {
        expect(WEAPON_STATS.laser_small.special).toBe('beam')
        expect(WEAPON_STATS.laser_small.projectileSpeed).toBe(0)
        expect(WEAPON_STATS.laser_small.pierce).toBe(999)
      })

      it('laser_large should be wide beam', () => {
        expect(WEAPON_STATS.laser_large.special).toBe('beam_wide')
        expect(WEAPON_STATS.laser_large.projectileSpeed).toBe(0)
        expect(WEAPON_STATS.laser_large.pierce).toBe(999)
      })

      it('lightning should chain', () => {
        expect(WEAPON_STATS.lightning.special).toBe('chain')
      })

      it('sword should be melee', () => {
        expect(WEAPON_STATS.sword.special).toBe('melee')
        expect(WEAPON_STATS.sword.projectileSpeed).toBe(0)
        expect(WEAPON_STATS.sword.damage).toBeGreaterThan(100)
      })
    })
  })

  describe('AMMO_TYPE_COLORS', () => {
    it('should have colors for all ammo types', () => {
      const ammoTypes: AmmoType[] = ['BULLET', 'BOMB', 'OIL', 'ENERGY']
      for (const ammoType of ammoTypes) {
        expect(AMMO_TYPE_COLORS[ammoType]).toBeDefined()
        expect(AMMO_TYPE_COLORS[ammoType]).toHaveLength(4)
      }
    })

    it('should have valid RGBA values', () => {
      for (const color of Object.values(AMMO_TYPE_COLORS)) {
        for (const component of color) {
          expect(component).toBeGreaterThanOrEqual(0)
          expect(component).toBeLessThanOrEqual(1)
        }
      }
    })
  })

  describe('WEAPON_COLORS', () => {
    it('should have colors for all weapon types', () => {
      for (const weaponType of ALL_WEAPON_TYPES) {
        expect(WEAPON_COLORS[weaponType]).toBeDefined()
        expect(WEAPON_COLORS[weaponType]).toHaveLength(4)
      }
    })

    it('should have valid RGBA values', () => {
      for (const color of Object.values(WEAPON_COLORS)) {
        for (const component of color) {
          expect(component).toBeGreaterThanOrEqual(0)
          expect(component).toBeLessThanOrEqual(1)
        }
      }
    })
  })

  describe('WEAPON_BULLET_TYPE', () => {
    it('should have bullet type for all weapon types', () => {
      for (const weaponType of ALL_WEAPON_TYPES) {
        expect(WEAPON_BULLET_TYPE[weaponType]).toBeDefined()
        expect(typeof WEAPON_BULLET_TYPE[weaponType]).toBe('string')
      }
    })
  })

  describe('ALL_WEAPON_TYPES', () => {
    it('should contain all 16 weapon types', () => {
      expect(ALL_WEAPON_TYPES).toHaveLength(16)
    })

    it('should include all weapon types', () => {
      const expectedTypes: WeaponType[] = [
        'vulcan', 'shotgun', 'spread_small', 'spread_large', 'railgun',
        'missile', 'cannon', 'mine', 'grenade',
        'flame', 'acid',
        'sonic', 'laser_small', 'laser_large', 'lightning', 'sword',
      ]
      for (const type of expectedTypes) {
        expect(ALL_WEAPON_TYPES).toContain(type)
      }
    })
  })

  describe('getAvailableWeapons', () => {
    it('should return base weapons at wave 1', () => {
      const weapons = getAvailableWeapons(1)
      expect(weapons).toContain('vulcan')
      expect(weapons).toContain('shotgun')
      expect(weapons).toContain('spread_small')
      expect(weapons).toHaveLength(3)
    })

    it('should return base weapons at wave 2', () => {
      const weapons = getAvailableWeapons(2)
      expect(weapons).toHaveLength(3)
    })

    it('should unlock wave 3 weapons', () => {
      const weapons = getAvailableWeapons(3)
      expect(weapons).toContain('missile')
      expect(weapons).toContain('flame')
      expect(weapons).toHaveLength(5)
    })

    it('should unlock wave 5 weapons', () => {
      const weapons = getAvailableWeapons(5)
      expect(weapons).toContain('spread_large')
      expect(weapons).toContain('cannon')
      expect(weapons).toContain('sonic')
      expect(weapons).toHaveLength(8)
    })

    it('should unlock wave 7 weapons', () => {
      const weapons = getAvailableWeapons(7)
      expect(weapons).toContain('grenade')
      expect(weapons).toContain('acid')
      expect(weapons).toContain('laser_small')
      expect(weapons).toHaveLength(11)
    })

    it('should unlock wave 9 weapons', () => {
      const weapons = getAvailableWeapons(9)
      expect(weapons).toContain('lightning')
      expect(weapons).toContain('laser_large')
      expect(weapons).toHaveLength(13)
    })

    it('should unlock wave 12 weapons (all)', () => {
      const weapons = getAvailableWeapons(12)
      expect(weapons).toContain('railgun')
      expect(weapons).toContain('mine')
      expect(weapons).toContain('sword')
      expect(weapons).toHaveLength(16)
    })

    it('should return all weapons at high wave', () => {
      const weapons = getAvailableWeapons(100)
      expect(weapons).toHaveLength(16)
    })

    it('should return consistent results for same wave', () => {
      const weapons1 = getAvailableWeapons(7)
      const weapons2 = getAvailableWeapons(7)
      expect(weapons1).toEqual(weapons2)
    })
  })

  describe('weapon balance', () => {
    it('should have higher per-shot damage for slower weapons', () => {
      // Railgun has much higher per-shot damage than vulcan
      expect(WEAPON_STATS.railgun.damage).toBeGreaterThan(WEAPON_STATS.vulcan.damage * 5)
      // Sword is slow but high damage
      expect(WEAPON_STATS.sword.damage).toBeGreaterThan(100)
    })

    it('should have limited ammo for powerful weapons', () => {
      // Railgun and sword have limited max ammo
      expect(WEAPON_STATS.railgun.maxAmmo).toBeLessThan(100)
      expect(WEAPON_STATS.sword.maxAmmo).toBeLessThan(100)
    })

    it('should have more ammo for rapid-fire weapons', () => {
      expect(WEAPON_STATS.vulcan.maxAmmo).toBeGreaterThan(300)
      expect(WEAPON_STATS.flame.maxAmmo).toBeGreaterThan(500)
    })

    it('should have appropriate pierce for beam weapons', () => {
      expect(WEAPON_STATS.laser_small.pierce).toBe(999)
      expect(WEAPON_STATS.laser_large.pierce).toBe(999)
      expect(WEAPON_STATS.flame.pierce).toBe(999)
    })
  })
})
