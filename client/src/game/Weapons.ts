/**
 * Weapon System Types and Configuration
 *
 * 16 weapons across 4 ammo types, Einhänder-style pickup system
 */

// Ammo categories
export type AmmoType = 'BULLET' | 'BOMB' | 'OIL' | 'ENERGY'

// All 16 weapon types
export type WeaponType =
  // BULLET (5 weapons)
  | 'vulcan'        // Minigun, rapid fire
  | 'shotgun'       // Bulldog - wide spread, short range
  | 'spread_small'  // Jericho - 5-way spread
  | 'spread_large'  // Kitsune - 9-way spread
  | 'railgun'       // Odin - piercing beam
  // BOMB (4 weapons)
  | 'missile'       // Hornet - homing torpedo
  | 'cannon'        // Megiddo - explosive shell
  | 'mine'          // Limpet - deployable homing mine
  | 'grenade'       // Magus - area effect
  // OIL (2 weapons)
  | 'flame'         // Diablo - flamethrower
  | 'acid'          // Slag - caustic spray
  // ENERGY (5 weapons)
  | 'sonic'         // Banshee - sonic wave
  | 'laser_small'   // Lancet - thin piercing laser
  | 'laser_large'   // Paladin - charge laser
  | 'lightning'     // Valkyrie - chain lightning
  | 'sword'         // Durandal - energy sword

export interface WeaponStats {
  type: WeaponType
  name: string              // UI display name
  ammoType: AmmoType
  damage: number            // Base damage per hit
  fireRate: number          // Frames between shots
  ammoPerPickup: number     // Ammo gained from pickup
  maxAmmo: number           // Maximum ammo capacity
  projectileSpeed: number   // World units per second
  projectileCount: number   // Bullets per shot
  spread: number            // Angle spread in radians
  pierce: number            // How many enemies it can hit
  lifetime: number          // Frames before despawn
  special: WeaponSpecial    // Special behavior flag
}

export type WeaponSpecial =
  | 'none'          // Standard projectile
  | 'homing'        // Tracks nearest enemy
  | 'explosive'     // Area damage on impact
  | 'deployable'    // Stationary mine
  | 'bouncing'      // Bounces off walls
  | 'continuous'    // Fires every frame while held
  | 'puddle'        // Leaves damaging area
  | 'wave'          // Expands as it travels
  | 'beam'          // Instant hit, thin
  | 'beam_wide'     // Instant hit, wide
  | 'chain'         // Jumps to nearby enemies
  | 'melee'         // Close range arc
  | 'instant_hit'   // Railgun-style instant

export interface WeaponDrop {
  id: number
  x: number         // Fixed-point position
  y: number
  weaponType: WeaponType
  ammo: number      // Ammo this drop provides
  frame: number     // For animation
}

export interface PlayerWeapon {
  type: WeaponType
  ammo: number
  maxAmmo: number
  cooldown: number  // Frames remaining
}

// Complete weapon stats configuration
export const WEAPON_STATS: Record<WeaponType, WeaponStats> = {
  // === BULLET WEAPONS ===
  vulcan: {
    type: 'vulcan',
    name: 'Vulcan',
    ammoType: 'BULLET',
    damage: 8,
    fireRate: 3,            // Very fast
    ammoPerPickup: 120,
    maxAmmo: 400,
    projectileSpeed: 500,
    projectileCount: 1,
    spread: 0.05,           // Slight inaccuracy
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
    spread: 0.5,            // ~30 degrees
    pierce: 0,
    lifetime: 45,           // Short range
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
    projectileSpeed: 180,   // Slow start, accelerates
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
    projectileSpeed: 50,    // Drifts slowly
    projectileCount: 1,
    spread: 0,
    pierce: 0,
    lifetime: 600,          // 10 seconds
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
    special: 'explosive',   // Explodes on timer or impact
  },

  // === OIL WEAPONS ===
  flame: {
    type: 'flame',
    name: 'Diablo',
    ammoType: 'OIL',
    damage: 3,              // Per frame while in contact
    fireRate: 1,            // Continuous
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
    damage: 4,              // Per frame
    fireRate: 1,
    ammoPerPickup: 180,
    maxAmmo: 500,
    projectileSpeed: 0,     // Instant beam
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
    damage: 10,             // Per frame
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
    projectileSpeed: 0,     // Melee
    projectileCount: 1,
    spread: 0,
    pierce: 999,
    lifetime: 10,
    special: 'melee',
  },
}

// Ammo type colors for HUD
export const AMMO_TYPE_COLORS: Record<AmmoType, [number, number, number, number]> = {
  BULLET: [1.0, 0.85, 0.2, 1.0],   // Gold
  BOMB: [1.0, 0.4, 0.1, 1.0],      // Orange
  OIL: [0.4, 0.9, 0.2, 1.0],       // Green
  ENERGY: [0.3, 0.7, 1.0, 1.0],    // Blue
}

// Weapon colors for rendering meshes
export const WEAPON_COLORS: Record<WeaponType, [number, number, number, number]> = {
  // BULLET - warm metallics
  vulcan: [0.7, 0.7, 0.75, 1.0],
  shotgun: [0.6, 0.5, 0.35, 1.0],
  spread_small: [0.8, 0.7, 0.5, 1.0],
  spread_large: [1.0, 0.6, 0.7, 1.0],
  railgun: [0.5, 0.5, 0.8, 1.0],
  // BOMB - oranges/reds
  missile: [0.8, 0.5, 0.2, 1.0],
  cannon: [0.6, 0.3, 0.2, 1.0],
  mine: [0.5, 0.5, 0.2, 1.0],
  grenade: [0.7, 0.3, 0.6, 1.0],
  // OIL - greens
  flame: [1.0, 0.4, 0.1, 1.0],
  acid: [0.3, 0.9, 0.3, 1.0],
  // ENERGY - blues/purples
  sonic: [0.7, 0.4, 0.9, 1.0],
  laser_small: [0.2, 1.0, 1.0, 1.0],
  laser_large: [0.5, 0.8, 1.0, 1.0],
  lightning: [1.0, 1.0, 0.4, 1.0],
  sword: [1.0, 0.3, 0.5, 1.0],
}

// Weapon availability by wave
export function getAvailableWeapons(wave: number): WeaponType[] {
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

// All weapon types array for iteration
export const ALL_WEAPON_TYPES: WeaponType[] = [
  'vulcan', 'shotgun', 'spread_small', 'spread_large', 'railgun',
  'missile', 'cannon', 'mine', 'grenade',
  'flame', 'acid',
  'sonic', 'laser_small', 'laser_large', 'lightning', 'sword',
]

// Map weapon types to bullet visual types for rendering
export const WEAPON_BULLET_TYPE: Record<WeaponType, string> = {
  // BULLET weapons - cyan/blue shots
  vulcan: 'shot',
  shotgun: 'shot',
  spread_small: 'spread',   // Orange/yellow spread
  spread_large: 'spread',   // Orange/yellow spread
  railgun: 'laser',         // Cyan laser
  // BOMB weapons
  missile: 'missile',
  cannon: 'big',            // Large red projectile
  mine: 'shot',
  grenade: 'big',
  // OIL weapons - red/orange
  flame: 'flame',           // Fire projectile
  acid: 'acid',             // Green acid
  // ENERGY weapons
  sonic: 'ring',            // Expanding ring
  laser_small: 'laser',
  laser_large: 'laser',
  lightning: 'laser',
  sword: 'shot',
}
