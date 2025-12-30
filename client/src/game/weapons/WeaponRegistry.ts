/**
 * WeaponRegistry - Central repository for all weapon configurations
 */

import type { WeaponType, WeaponStats, AmmoType } from './WeaponTypes.ts'

/**
 * Complete weapon stats configuration
 */
const WEAPON_STATS_DATA: Record<WeaponType, WeaponStats> = {
  // === BULLET WEAPONS ===
  vulcan: {
    type: 'vulcan',
    name: 'Vulcan',
    ammoType: 'BULLET',
    damage: 8,
    fireRate: 3,
    ammoPerPickup: 120,
    maxAmmo: 400,
    projectileSpeed: 500,
    projectileCount: 1,
    spread: 0.05,
    pierce: 0,
    lifetime: 180,
    special: 'none',
  },
  shotgun: {
    type: 'shotgun',
    name: 'Bulldog',
    ammoType: 'BULLET',
    damage: 6,
    fireRate: 25,
    ammoPerPickup: 30,
    maxAmmo: 120,
    projectileSpeed: 350,
    projectileCount: 8,
    spread: 0.5,
    pierce: 0,
    lifetime: 45,
    special: 'none',
  },
  spread_small: {
    type: 'spread_small',
    name: 'Jericho',
    ammoType: 'BULLET',
    damage: 12,
    fireRate: 12,
    ammoPerPickup: 50,
    maxAmmo: 200,
    projectileSpeed: 400,
    projectileCount: 5,
    spread: 0.4,
    pierce: 0,
    lifetime: 150,
    special: 'none',
  },
  spread_large: {
    type: 'spread_large',
    name: 'Kitsune',
    ammoType: 'BULLET',
    damage: 10,
    fireRate: 15,
    ammoPerPickup: 40,
    maxAmmo: 150,
    projectileSpeed: 380,
    projectileCount: 9,
    spread: 0.7,
    pierce: 0,
    lifetime: 150,
    special: 'none',
  },
  railgun: {
    type: 'railgun',
    name: 'Odin',
    ammoType: 'BULLET',
    damage: 80,
    fireRate: 50,
    ammoPerPickup: 12,
    maxAmmo: 40,
    projectileSpeed: 1200,
    projectileCount: 1,
    spread: 0,
    pierce: 10,
    lifetime: 60,
    special: 'instant_hit',
  },

  // === BOMB WEAPONS ===
  missile: {
    type: 'missile',
    name: 'Hornet',
    ammoType: 'BOMB',
    damage: 40,
    fireRate: 18,
    ammoPerPickup: 20,
    maxAmmo: 80,
    projectileSpeed: 180,
    projectileCount: 1,
    spread: 0,
    pierce: 0,
    lifetime: 300,
    special: 'homing',
  },
  cannon: {
    type: 'cannon',
    name: 'Megiddo',
    ammoType: 'BOMB',
    damage: 100,
    fireRate: 45,
    ammoPerPickup: 10,
    maxAmmo: 35,
    projectileSpeed: 300,
    projectileCount: 1,
    spread: 0,
    pierce: 0,
    lifetime: 180,
    special: 'explosive',
  },
  mine: {
    type: 'mine',
    name: 'Limpet',
    ammoType: 'BOMB',
    damage: 60,
    fireRate: 40,
    ammoPerPickup: 8,
    maxAmmo: 20,
    projectileSpeed: 50,
    projectileCount: 1,
    spread: 0,
    pierce: 0,
    lifetime: 600,
    special: 'deployable',
  },
  grenade: {
    type: 'grenade',
    name: 'Magus',
    ammoType: 'BOMB',
    damage: 50,
    fireRate: 30,
    ammoPerPickup: 15,
    maxAmmo: 50,
    projectileSpeed: 280,
    projectileCount: 1,
    spread: 0,
    pierce: 0,
    lifetime: 120,
    special: 'explosive',
  },

  // === OIL WEAPONS ===
  flame: {
    type: 'flame',
    name: 'Diablo',
    ammoType: 'OIL',
    damage: 3,
    fireRate: 1,
    ammoPerPickup: 250,
    maxAmmo: 600,
    projectileSpeed: 300,
    projectileCount: 3,
    spread: 0.2,
    pierce: 999,
    lifetime: 25,
    special: 'continuous',
  },
  acid: {
    type: 'acid',
    name: 'Slag',
    ammoType: 'OIL',
    damage: 25,
    fireRate: 35,
    ammoPerPickup: 25,
    maxAmmo: 80,
    projectileSpeed: 250,
    projectileCount: 1,
    spread: 0,
    pierce: 0,
    lifetime: 300,
    special: 'puddle',
  },

  // === ENERGY WEAPONS ===
  sonic: {
    type: 'sonic',
    name: 'Banshee',
    ammoType: 'ENERGY',
    damage: 30,
    fireRate: 22,
    ammoPerPickup: 35,
    maxAmmo: 120,
    projectileSpeed: 280,
    projectileCount: 1,
    spread: 0,
    pierce: 5,
    lifetime: 90,
    special: 'wave',
  },
  laser_small: {
    type: 'laser_small',
    name: 'Lancet',
    ammoType: 'ENERGY',
    damage: 4,
    fireRate: 1,
    ammoPerPickup: 180,
    maxAmmo: 500,
    projectileSpeed: 0,
    projectileCount: 1,
    spread: 0,
    pierce: 999,
    lifetime: 1,
    special: 'beam',
  },
  laser_large: {
    type: 'laser_large',
    name: 'Paladin',
    ammoType: 'ENERGY',
    damage: 10,
    fireRate: 1,
    ammoPerPickup: 120,
    maxAmmo: 350,
    projectileSpeed: 0,
    projectileCount: 1,
    spread: 0,
    pierce: 999,
    lifetime: 1,
    special: 'beam_wide',
  },
  lightning: {
    type: 'lightning',
    name: 'Valkyrie',
    ammoType: 'ENERGY',
    damage: 35,
    fireRate: 18,
    ammoPerPickup: 25,
    maxAmmo: 90,
    projectileSpeed: 600,
    projectileCount: 1,
    spread: 0,
    pierce: 0,
    lifetime: 20,
    special: 'chain',
  },
  sword: {
    type: 'sword',
    name: 'Durandal',
    ammoType: 'ENERGY',
    damage: 120,
    fireRate: 28,
    ammoPerPickup: 12,
    maxAmmo: 35,
    projectileSpeed: 0,
    projectileCount: 1,
    spread: 0,
    pierce: 999,
    lifetime: 10,
    special: 'melee',
  },
}

/**
 * Ammo type colors for HUD
 */
const AMMO_TYPE_COLORS_DATA: Record<AmmoType, [number, number, number, number]> = {
  BULLET: [1.0, 0.85, 0.2, 1.0],
  BOMB: [1.0, 0.4, 0.1, 1.0],
  OIL: [0.4, 0.9, 0.2, 1.0],
  ENERGY: [0.3, 0.7, 1.0, 1.0],
}

/**
 * Weapon colors for rendering
 */
const WEAPON_COLORS_DATA: Record<WeaponType, [number, number, number, number]> = {
  vulcan: [0.7, 0.7, 0.75, 1.0],
  shotgun: [0.6, 0.5, 0.35, 1.0],
  spread_small: [0.8, 0.7, 0.5, 1.0],
  spread_large: [1.0, 0.6, 0.7, 1.0],
  railgun: [0.5, 0.5, 0.8, 1.0],
  missile: [0.8, 0.5, 0.2, 1.0],
  cannon: [0.6, 0.3, 0.2, 1.0],
  mine: [0.5, 0.5, 0.2, 1.0],
  grenade: [0.7, 0.3, 0.6, 1.0],
  flame: [1.0, 0.4, 0.1, 1.0],
  acid: [0.3, 0.9, 0.3, 1.0],
  sonic: [0.7, 0.4, 0.9, 1.0],
  laser_small: [0.2, 1.0, 1.0, 1.0],
  laser_large: [0.5, 0.8, 1.0, 1.0],
  lightning: [1.0, 1.0, 0.4, 1.0],
  sword: [1.0, 0.3, 0.5, 1.0],
}

/**
 * Map weapon types to bullet visual types
 */
const WEAPON_BULLET_TYPE_DATA: Record<WeaponType, string> = {
  vulcan: 'shot',
  shotgun: 'shot',
  spread_small: 'spread',
  spread_large: 'spread',
  railgun: 'laser',
  missile: 'missile',
  cannon: 'big',
  mine: 'shot',
  grenade: 'big',
  flame: 'flame',
  acid: 'acid',
  sonic: 'ring',
  laser_small: 'laser',
  laser_large: 'laser',
  lightning: 'laser',
  sword: 'shot',
}

/**
 * WeaponRegistry class - provides access to weapon data
 */
export class WeaponRegistry {
  /**
   * Get stats for a weapon type
   */
  static getStats(type: WeaponType): WeaponStats {
    return WEAPON_STATS_DATA[type]
  }

  /**
   * Get all weapon stats
   */
  static getAllStats(): Record<WeaponType, WeaponStats> {
    return WEAPON_STATS_DATA
  }

  /**
   * Get ammo type color
   */
  static getAmmoColor(ammoType: AmmoType): [number, number, number, number] {
    return AMMO_TYPE_COLORS_DATA[ammoType]
  }

  /**
   * Get weapon color for rendering
   */
  static getWeaponColor(type: WeaponType): [number, number, number, number] {
    return WEAPON_COLORS_DATA[type]
  }

  /**
   * Get bullet visual type for a weapon
   */
  static getBulletType(type: WeaponType): string {
    return WEAPON_BULLET_TYPE_DATA[type]
  }

  /**
   * Get weapons available at a given wave
   */
  static getAvailableWeapons(wave: number): WeaponType[] {
    const weapons: WeaponType[] = ['vulcan', 'shotgun', 'spread_small']

    if (wave >= 3) {
      weapons.push('missile', 'flame')
    }
    if (wave >= 5) {
      weapons.push('spread_large', 'cannon', 'sonic')
    }
    if (wave >= 7) {
      weapons.push('grenade', 'acid', 'laser_small')
    }
    if (wave >= 9) {
      weapons.push('lightning', 'laser_large')
    }
    if (wave >= 12) {
      weapons.push('railgun', 'mine', 'sword')
    }

    return weapons
  }

  /**
   * Check if a weapon is continuous fire (fires every frame while held)
   */
  static isContinuous(type: WeaponType): boolean {
    const stats = this.getStats(type)
    return stats.special === 'continuous' || stats.special === 'beam' || stats.special === 'beam_wide'
  }

  /**
   * Check if a weapon is a beam weapon
   */
  static isBeam(type: WeaponType): boolean {
    const stats = this.getStats(type)
    return stats.special === 'beam' || stats.special === 'beam_wide'
  }

  /**
   * Check if a weapon has homing projectiles
   */
  static isHoming(type: WeaponType): boolean {
    return this.getStats(type).special === 'homing'
  }

  /**
   * Check if a weapon is explosive
   */
  static isExplosive(type: WeaponType): boolean {
    return this.getStats(type).special === 'explosive'
  }

  /**
   * Get weapons by ammo type
   */
  static getWeaponsByAmmoType(ammoType: AmmoType): WeaponType[] {
    return (Object.keys(WEAPON_STATS_DATA) as WeaponType[]).filter(
      (type) => WEAPON_STATS_DATA[type].ammoType === ammoType
    )
  }
}

// Export constants for backwards compatibility
export const WEAPON_STATS = WEAPON_STATS_DATA
export const AMMO_TYPE_COLORS = AMMO_TYPE_COLORS_DATA
export const WEAPON_COLORS = WEAPON_COLORS_DATA
export const WEAPON_BULLET_TYPE = WEAPON_BULLET_TYPE_DATA
export const getAvailableWeapons = WeaponRegistry.getAvailableWeapons.bind(WeaponRegistry)
