import { Vector2 } from '../math/Vector2.ts'

/**
 * Base class for all game entities.
 * Uses fixed-point internally but exposes float API for convenience.
 */
export abstract class Entity {
  public readonly id: number
  protected position: Vector2
  protected velocity: Vector2
  public frame: number = 0

  constructor(id: number, x: number = 0, y: number = 0) {
    this.id = id
    this.position = new Vector2(x, y)
    this.velocity = new Vector2(0, 0)
  }

  get x(): number {
    return this.position.x
  }

  set x(value: number) {
    this.position.x = value
  }

  get y(): number {
    return this.position.y
  }

  set y(value: number) {
    this.position.y = value
  }

  get vx(): number {
    return this.velocity.x
  }

  set vx(value: number) {
    this.velocity.x = value
  }

  get vy(): number {
    return this.velocity.y
  }

  set vy(value: number) {
    this.velocity.y = value
  }

  /**
   * Get position as Vector2
   */
  getPosition(): Vector2 {
    return this.position.clone()
  }

  /**
   * Set position from Vector2
   */
  setPosition(pos: Vector2): void {
    this.position.copy(pos)
  }

  /**
   * Get velocity as Vector2
   */
  getVelocity(): Vector2 {
    return this.velocity.clone()
  }

  /**
   * Set velocity from Vector2
   */
  setVelocity(vel: Vector2): void {
    this.velocity.copy(vel)
  }

  /**
   * Get speed (velocity magnitude)
   */
  getSpeed(): number {
    return this.velocity.length()
  }

  /**
   * Move by velocity
   */
  move(dt: number = 1): void {
    this.position.x += this.velocity.x * dt
    this.position.y += this.velocity.y * dt
  }

  /**
   * Distance to another entity
   */
  distanceTo(other: Entity): number {
    return this.position.distanceTo(other.position)
  }

  /**
   * Squared distance to another entity (faster, for comparisons)
   */
  distanceSquaredTo(other: Entity): number {
    return this.position.distanceSquaredTo(other.position)
  }

  /**
   * Direction to another entity (normalized)
   */
  directionTo(other: Entity): Vector2 {
    return other.position.minus(this.position).normalize()
  }

  /**
   * Angle to another entity in radians
   */
  angleTo(other: Entity): number {
    const dx = other.x - this.x
    const dy = other.y - this.y
    return Math.atan2(dy, dx)
  }

  /**
   * Check if within bounds
   */
  isInBounds(minX: number, maxX: number, minY: number, maxY: number): boolean {
    return this.x >= minX && this.x <= maxX && this.y >= minY && this.y <= maxY
  }

  /**
   * Clamp position to bounds
   */
  clampToBounds(minX: number, maxX: number, minY: number, maxY: number): void {
    if (this.x < minX) this.x = minX
    if (this.x > maxX) this.x = maxX
    if (this.y < minY) this.y = minY
    if (this.y > maxY) this.y = maxY
  }

  /**
   * Update entity (override in subclasses)
   */
  abstract update(dt: number): void

  /**
   * Check if entity should be removed
   */
  abstract isDead(): boolean
}

/**
 * Interface for entities that can take damage
 */
export interface Damageable {
  health: number
  maxHealth: number
  takeDamage(amount: number): void
  heal(amount: number): void
  getHealthPercent(): number
}

/**
 * Interface for entities that can collide
 */
export interface Collidable {
  getCollisionRadius(): number
  collidesWith(other: Collidable & Entity): boolean
}

/**
 * Helper class that provides damageable functionality
 */
export class DamageableEntity {
  health: number
  maxHealth: number

  constructor(maxHealth: number = 100) {
    this.maxHealth = maxHealth
    this.health = maxHealth
  }

  takeDamage(amount: number): void {
    this.health = Math.max(0, this.health - amount)
  }

  heal(amount: number): void {
    this.health = Math.min(this.maxHealth, this.health + amount)
  }

  getHealthPercent(): number {
    return this.maxHealth > 0 ? this.health / this.maxHealth : 0
  }

  isDead(): boolean {
    return this.health <= 0
  }
}

/**
 * Helper function to check circle collision between two entities
 */
export function checkCircleCollision(
  x1: number, y1: number, r1: number,
  x2: number, y2: number, r2: number
): boolean {
  const dx = x1 - x2
  const dy = y1 - y2
  const distSq = dx * dx + dy * dy
  const radiusSum = r1 + r2
  return distSq < radiusSum * radiusSum
}
