/**
 * Weapon System Types
 * 16 weapons across 4 ammo types, Einhänder-style pickup system
 */

export type AmmoType = 'BULLET' | 'BOMB' | 'OIL' | 'ENERGY'

export type WeaponType =
  // BULLET (5 weapons)
  | 'vulcan' // Minigun, rapid fire
  | 'shotgun' // Bulldog - wide spread, short range
  | 'spread_small' // Jericho - 5-way spread
  | 'spread_large' // Kitsune - 9-way spread
  | 'railgun' // Odin - piercing beam
  // BOMB (4 weapons)
  | 'missile' // Hornet - homing torpedo
  | 'cannon' // Megiddo - explosive shell
  | 'mine' // Limpet - deployable homing mine
  | 'grenade' // Magus - area effect
  // OIL (2 weapons)
  | 'flame' // Diablo - flamethrower
  | 'acid' // Slag - caustic spray
  // ENERGY (5 weapons)
  | 'sonic' // Banshee - sonic wave
  | 'laser_small' // Lancet - thin piercing laser
  | 'laser_large' // Paladin - charge laser
  | 'lightning' // Valkyrie - chain lightning
  | 'sword' // Durandal - energy sword

export type WeaponSpecial =
  | 'none' // Standard projectile
  | 'homing' // Tracks nearest enemy
  | 'explosive' // Area damage on impact
  | 'deployable' // Stationary mine
  | 'bouncing' // Bounces off walls
  | 'continuous' // Fires every frame while held
  | 'puddle' // Leaves damaging area
  | 'wave' // Expands as it travels
  | 'beam' // Instant hit, thin
  | 'beam_wide' // Instant hit, wide
  | 'chain' // Jumps to nearby enemies
  | 'melee' // Close range arc
  | 'instant_hit' // Railgun-style instant

export interface WeaponStats {
  type: WeaponType
  name: string
  ammoType: AmmoType
  damage: number
  fireRate: number
  ammoPerPickup: number
  maxAmmo: number
  projectileSpeed: number
  projectileCount: number
  spread: number
  pierce: number
  lifetime: number
  special: WeaponSpecial
}

export interface WeaponDrop {
  id: number
  x: number
  y: number
  weaponType: WeaponType
  ammo: number
  frame: number
}

export interface PlayerWeapon {
  type: WeaponType
  ammo: number
  maxAmmo: number
  cooldown: number
}

export const ALL_WEAPON_TYPES: readonly WeaponType[] = [
  'vulcan',
  'shotgun',
  'spread_small',
  'spread_large',
  'railgun',
  'missile',
  'cannon',
  'mine',
  'grenade',
  'flame',
  'acid',
  'sonic',
  'laser_small',
  'laser_large',
  'lightning',
  'sword',
] as const

export const BULLET_WEAPONS: readonly WeaponType[] = [
  'vulcan',
  'shotgun',
  'spread_small',
  'spread_large',
  'railgun',
] as const

export const BOMB_WEAPONS: readonly WeaponType[] = [
  'missile',
  'cannon',
  'mine',
  'grenade',
] as const

export const OIL_WEAPONS: readonly WeaponType[] = ['flame', 'acid'] as const

export const ENERGY_WEAPONS: readonly WeaponType[] = [
  'sonic',
  'laser_small',
  'laser_large',
  'lightning',
  'sword',
] as const
