import { Entity, type Collidable } from './Entity.ts'

/**
 * Powerup types
 */
export type PowerupType =
  | 'SHIELD'
  | 'UPGRADE'
  | 'SPREAD'
  | 'LASER'
  | 'MISSILE'
  | 'ORBIT'
  | 'DRONE'
  | 'SPEED'
  | 'RAPID'
  | 'PIERCE'
  | 'LIFE'

/**
 * Powerup effect configuration
 */
export interface PowerupEffect {
  type: PowerupType
  description: string
  color: number  // Color index for rendering
  rarity: number  // 0-1, higher = rarer
}

/**
 * Powerup effects and metadata
 */
export const POWERUP_EFFECTS: Record<PowerupType, PowerupEffect> = {
  SHIELD: { type: 'SHIELD', description: 'Restore shields', color: 0, rarity: 0.2 },
  UPGRADE: { type: 'UPGRADE', description: 'Upgrade ship', color: 1, rarity: 0.1 },
  SPREAD: { type: 'SPREAD', description: 'Spread shot', color: 2, rarity: 0.15 },
  LASER: { type: 'LASER', description: 'Laser power', color: 3, rarity: 0.15 },
  MISSILE: { type: 'MISSILE', description: 'Homing missiles', color: 4, rarity: 0.1 },
  ORBIT: { type: 'ORBIT', description: 'Orbital shield', color: 5, rarity: 0.1 },
  DRONE: { type: 'DRONE', description: 'Attack drone', color: 6, rarity: 0.1 },
  SPEED: { type: 'SPEED', description: 'Speed boost', color: 7, rarity: 0.2 },
  RAPID: { type: 'RAPID', description: 'Rapid fire', color: 8, rarity: 0.15 },
  PIERCE: { type: 'PIERCE', description: 'Piercing shots', color: 9, rarity: 0.1 },
  LIFE: { type: 'LIFE', description: 'Extra life', color: 10, rarity: 0.05 },
}

/**
 * All powerup types as array
 */
export const ALL_POWERUP_TYPES: PowerupType[] = [
  'SHIELD', 'UPGRADE', 'SPREAD', 'LASER', 'MISSILE',
  'ORBIT', 'DRONE', 'SPEED', 'RAPID', 'PIERCE', 'LIFE',
]

/**
 * Powerup entity - collectible items that enhance the player
 */
export class Powerup extends Entity implements Collidable {
  public readonly type: PowerupType
  public lifetime: number = 600  // 10 seconds at 60fps
  public bobOffset: number = 0

  constructor(id: number, x: number, y: number, type: PowerupType) {
    super(id, x, y)
    this.type = type
    // Slight leftward drift
    this.vx = -0.5
    this.vy = 0
  }

  /**
   * Get collision radius
   */
  getCollisionRadius(): number {
    return 15
  }

  /**
   * Check collision with another entity
   */
  collidesWith(other: Collidable & Entity): boolean {
    const dx = this.x - other.x
    const dy = this.y - other.y
    const distSq = dx * dx + dy * dy
    const radiusSum = this.getCollisionRadius() + other.getCollisionRadius()
    return distSq < radiusSum * radiusSum
  }

  /**
   * Get effect metadata
   */
  getEffect(): PowerupEffect {
    return POWERUP_EFFECTS[this.type]
  }

  /**
   * Get description
   */
  getDescription(): string {
    return POWERUP_EFFECTS[this.type].description
  }

  /**
   * Get color index for rendering
   */
  getColorIndex(): number {
    return POWERUP_EFFECTS[this.type].color
  }

  /**
   * Check if powerup has expired
   */
  hasExpired(): boolean {
    return this.lifetime <= 0
  }

  /**
   * Get visual Y position with bob effect
   */
  getVisualY(): number {
    return this.y + Math.sin(this.bobOffset) * 5
  }

  /**
   * Get opacity based on remaining lifetime (blinks when expiring)
   */
  getOpacity(): number {
    if (this.lifetime > 120) return 1
    // Blink faster as expiration approaches
    return this.lifetime % 10 < 5 ? 1 : 0.3
  }

  update(dt: number): void {
    this.move(dt)
    this.lifetime -= dt * 60
    this.bobOffset += 0.1 * dt * 60
    this.frame++
  }

  isDead(): boolean {
    return this.lifetime <= 0
  }

  /**
   * Create powerup
   */
  static create(id: number, x: number, y: number, type: PowerupType): Powerup {
    return new Powerup(id, x, y, type)
  }

  /**
   * Create random powerup based on rarity weights
   */
  static createRandom(id: number, x: number, y: number, randomValue: number): Powerup {
    const type = Powerup.getRandomType(randomValue)
    return new Powerup(id, x, y, type)
  }

  /**
   * Get random powerup type based on rarity
   */
  static getRandomType(randomValue: number): PowerupType {
    // Calculate total rarity weight
    let totalWeight = 0
    for (const effect of Object.values(POWERUP_EFFECTS)) {
      totalWeight += effect.rarity
    }

    // Pick based on weighted random
    let current = randomValue * totalWeight
    for (const effect of Object.values(POWERUP_EFFECTS)) {
      current -= effect.rarity
      if (current <= 0) {
        return effect.type
      }
    }

    return 'SHIELD'  // Fallback
  }

  /**
   * Check if type is a weapon powerup
   */
  static isWeaponPowerup(type: PowerupType): boolean {
    return ['SPREAD', 'LASER', 'MISSILE'].includes(type)
  }

  /**
   * Check if type is a stat powerup
   */
  static isStatPowerup(type: PowerupType): boolean {
    return ['SPEED', 'RAPID', 'PIERCE'].includes(type)
  }

  /**
   * Check if type is a special powerup
   */
  static isSpecialPowerup(type: PowerupType): boolean {
    return ['SHIELD', 'UPGRADE', 'LIFE', 'ORBIT', 'DRONE'].includes(type)
  }
}
