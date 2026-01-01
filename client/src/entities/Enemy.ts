import { Entity, type Collidable } from './Entity.ts'
import type { WeaponType } from '../game/weapons/WeaponTypes.ts'

/**
 * Enemy types
 */
export type EnemyType =
  | 'grunt'
  | 'shooter'
  | 'swerver'
  | 'tank'
  | 'speeder'
  | 'bomber'
  | 'sniper'
  | 'carrier'
  | 'mine'
  | 'spiral'
  | 'shield'
  | 'splitter'

/**
 * Enemy behavior types
 */
export type EnemyBehavior = 'straight' | 'sine' | 'circle' | 'dive' | 'chase' | 'stationary'

/**
 * Enemy stats configuration
 */
export interface EnemyStats {
  health: number
  speed: number
  points: number
  behavior: EnemyBehavior
  hasShield?: boolean
  shieldHealth?: number
  fireRate?: number
  splitCount?: number
}

/**
 * Default stats for each enemy type
 */
export const ENEMY_STATS: Record<EnemyType, EnemyStats> = {
  grunt: { health: 20, speed: 2, points: 100, behavior: 'straight' },
  shooter: { health: 30, speed: 1.5, points: 200, behavior: 'straight', fireRate: 90 },
  swerver: { health: 20, speed: 2.5, points: 150, behavior: 'sine' },
  tank: { health: 100, speed: 1, points: 500, behavior: 'straight', fireRate: 150 },
  speeder: { health: 15, speed: 5, points: 120, behavior: 'straight' },
  bomber: { health: 40, speed: 1.5, points: 250, behavior: 'straight', fireRate: 120 },
  sniper: { health: 25, speed: 1, points: 350, behavior: 'stationary', fireRate: 180 },
  carrier: { health: 80, speed: 1, points: 600, behavior: 'straight' },
  mine: { health: 10, speed: 0, points: 50, behavior: 'stationary' },
  spiral: { health: 35, speed: 2, points: 300, behavior: 'circle', fireRate: 60 },
  shield: { health: 50, speed: 1.5, points: 400, behavior: 'straight', hasShield: true, shieldHealth: 50 },
  splitter: { health: 60, speed: 2, points: 450, behavior: 'straight', splitCount: 2 },
}

/**
 * Enemy configuration for creation
 */
export interface EnemyConfig {
  type: EnemyType
  x: number
  y: number
  stats?: Partial<EnemyStats>
  equippedWeapon?: WeaponType
}

/**
 * Enemy entity - hostile ships
 */
export class Enemy extends Entity implements Collidable {
  public readonly type: EnemyType
  public health: number
  public maxHealth: number
  public points: number
  public behavior: EnemyBehavior
  public shootTimer: number = 0
  public fireRate: number = 0

  // Shield
  public hasShield: boolean = false
  public shieldHealth: number = 0

  // Splitter
  public splitCount: number = 0

  // Equipped weapon (drops on death)
  public equippedWeapon?: WeaponType

  // Behavior state
  public behaviorTimer: number = 0

  constructor(id: number, config: EnemyConfig) {
    super(id, config.x, config.y)

    this.type = config.type
    const baseStats = ENEMY_STATS[config.type]
    const stats = { ...baseStats, ...config.stats }

    this.health = stats.health
    this.maxHealth = stats.health
    this.points = stats.points
    this.behavior = stats.behavior
    this.fireRate = stats.fireRate ?? 0

    // Set initial velocity based on behavior
    this.vx = -stats.speed

    if (stats.hasShield) {
      this.hasShield = true
      this.shieldHealth = stats.shieldHealth ?? 50
    }

    if (stats.splitCount) {
      this.splitCount = stats.splitCount
    }

    this.equippedWeapon = config.equippedWeapon
  }

  /**
   * Get collision radius based on enemy type
   */
  getCollisionRadius(): number {
    switch (this.type) {
      case 'tank':
        return 30
      case 'carrier':
        return 35
      case 'mine':
        return 15
      case 'speeder':
        return 18
      case 'bomber':
        return 25
      default:
        return 20
    }
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
   * Take damage, returns true if enemy dies
   */
  takeDamage(amount: number): boolean {
    // Shield absorbs damage first
    if (this.hasShield && this.shieldHealth > 0) {
      this.shieldHealth -= amount
      if (this.shieldHealth <= 0) {
        this.hasShield = false
        this.shieldHealth = 0
      }
      return false
    }

    this.health -= amount
    return this.health <= 0
  }

  /**
   * Check if enemy should shoot
   */
  canShoot(): boolean {
    if (this.fireRate <= 0) return false
    return this.shootTimer <= 0
  }

  /**
   * Reset shoot timer
   */
  resetShootTimer(): void {
    this.shootTimer = this.fireRate
  }

  /**
   * Check if enemy can split (for splitter type)
   */
  canSplit(): boolean {
    return this.type === 'splitter' && this.splitCount > 0
  }

  /**
   * Get health percentage (0-1)
   */
  getHealthPercent(): number {
    return this.maxHealth > 0 ? this.health / this.maxHealth : 0
  }

  /**
   * Update enemy behavior based on type
   */
  updateBehavior(dt: number, playerX?: number, playerY?: number): void {
    const frameTime = dt * 60

    switch (this.behavior) {
      case 'sine':
        // Sinusoidal movement
        this.vy = Math.sin(this.frame * 0.05) * 3
        break

      case 'circle':
        // Circular/spiral movement
        this.vx = Math.cos(this.frame * 0.03) * 2 - 1
        this.vy = Math.sin(this.frame * 0.03) * 3
        break

      case 'chase':
        // Chase player
        if (playerX !== undefined && playerY !== undefined) {
          const dx = playerX - this.x
          const dy = playerY - this.y
          const dist = Math.sqrt(dx * dx + dy * dy)
          if (dist > 0) {
            this.vx = (dx / dist) * 3
            this.vy = (dy / dist) * 3
          }
        }
        break

      case 'dive':
        // Dive toward player then pull up
        this.behaviorTimer += frameTime
        if (this.behaviorTimer < 60) {
          this.vy = 2
        } else if (this.behaviorTimer < 120) {
          this.vy = -2
        } else {
          this.behaviorTimer = 0
        }
        break

      case 'stationary':
        this.vx = 0
        this.vy = 0
        break

      // 'straight' - default, just moves left
    }
  }

  update(dt: number): void {
    this.move(dt)

    // Update shoot timer
    if (this.shootTimer > 0) {
      this.shootTimer -= dt * 60
    }

    this.frame++
  }

  isDead(): boolean {
    return this.health <= 0
  }

  /**
   * Create enemy with default stats
   */
  static create(id: number, type: EnemyType, x: number, y: number): Enemy {
    return new Enemy(id, { type, x, y })
  }

  /**
   * Create enemy with weapon
   */
  static createWithWeapon(
    id: number,
    type: EnemyType,
    x: number,
    y: number,
    weapon: WeaponType
  ): Enemy {
    return new Enemy(id, { type, x, y, equippedWeapon: weapon })
  }
}
