import { Entity, type Collidable } from './Entity.ts'

export type BulletType =
  | 'shot'
  | 'spread'
  | 'laser'
  | 'mega'
  | 'missile'
  | 'drone'
  | 'enemy'
  | 'aimed'
  | 'big'
  | 'ring'
  | 'flame'
  | 'acid'

export interface BulletConfig {
  type: BulletType
  damage: number
  pierce: number
  isEnemy: boolean
  ownerId: string
  lifetime: number
}

/**
 * Bullet entity - projectiles fired by players and enemies
 */
export class Bullet extends Entity implements Collidable {
  public readonly type: BulletType
  public damage: number
  public pierce: number
  public readonly isEnemy: boolean
  public readonly ownerId: string
  public lifetime: number
  public readonly hitEntities: Set<number> = new Set()

  private dead: boolean = false

  constructor(id: number, x: number, y: number, vx: number, vy: number, config: BulletConfig) {
    super(id, x, y)
    this.vx = vx
    this.vy = vy
    this.type = config.type
    this.damage = config.damage
    this.pierce = config.pierce
    this.isEnemy = config.isEnemy
    this.ownerId = config.ownerId
    this.lifetime = config.lifetime
  }

  /**
   * Get collision radius based on bullet type
   */
  getCollisionRadius(): number {
    switch (this.type) {
      case 'big':
        return 10
      case 'mega':
        return 12
      case 'ring':
        return 4
      case 'flame':
        return 5
      default:
        return 6
    }
  }

  /**
   * Check collision with another collidable entity
   */
  collidesWith(other: Collidable & Entity): boolean {
    const dx = this.x - other.x
    const dy = this.y - other.y
    const distSq = dx * dx + dy * dy
    const radiusSum = this.getCollisionRadius() + other.getCollisionRadius()
    return distSq < radiusSum * radiusSum
  }

  /**
   * Record that this bullet has hit an entity (for pierce mechanics)
   */
  recordHit(entityId: number): void {
    this.hitEntities.add(entityId)
  }

  /**
   * Check if this bullet has already hit an entity
   */
  hasHit(entityId: number): boolean {
    return this.hitEntities.has(entityId)
  }

  /**
   * Consume a pierce (return true if bullet should survive)
   */
  consumePierce(): boolean {
    if (this.pierce > 0) {
      this.pierce--
      return true
    }
    return false
  }

  /**
   * Mark bullet as dead
   */
  kill(): void {
    this.dead = true
  }

  update(dt: number): void {
    this.move(dt)
    this.lifetime--
    this.frame++

    // Special behavior for ring bullets (expand)
    if (this.type === 'ring') {
      // Ring bullets slow down but expand
      this.vx *= 0.98
      this.vy *= 0.98
    }
  }

  isDead(): boolean {
    return this.dead || this.lifetime <= 0
  }

  /**
   * Check if bullet is off-screen (for cleanup)
   */
  isOffScreen(halfWidth: number, halfHeight: number): boolean {
    return (
      this.x < -halfWidth - 50 ||
      this.x > halfWidth + 50 ||
      this.y < -halfHeight - 50 ||
      this.y > halfHeight + 50
    )
  }

  /**
   * Create a player shot bullet
   */
  static createPlayerShot(
    id: number,
    x: number,
    y: number,
    vx: number,
    vy: number,
    ownerId: string,
    options: Partial<BulletConfig> = {}
  ): Bullet {
    return new Bullet(id, x, y, vx, vy, {
      type: options.type ?? 'shot',
      damage: options.damage ?? 10,
      pierce: options.pierce ?? 0,
      isEnemy: false,
      ownerId,
      lifetime: options.lifetime ?? 180,
    })
  }

  /**
   * Create an enemy bullet
   */
  static createEnemyShot(
    id: number,
    x: number,
    y: number,
    vx: number,
    vy: number,
    type: BulletType = 'enemy',
    damage: number = 20
  ): Bullet {
    return new Bullet(id, x, y, vx, vy, {
      type,
      damage,
      pierce: 0,
      isEnemy: true,
      ownerId: 'enemy',
      lifetime: 300,
    })
  }
}
