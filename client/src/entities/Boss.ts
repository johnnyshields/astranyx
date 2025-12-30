import { Entity, type Collidable } from './Entity.ts'

/**
 * Boss types
 * 0: CLASSIC - Basic attack patterns
 * 1: TWIN - Two-part boss
 * 2: CARRIER - Spawns enemies
 * 3: LASER - Charges and fires beam
 * 4: WALL - Segmented boss
 * 5: FINAL - Ultimate boss
 */
export type BossType = 0 | 1 | 2 | 3 | 4 | 5

/**
 * Boss type names for display
 */
export const BOSS_NAMES: Record<BossType, string> = {
  0: 'CLASSIC',
  1: 'TWIN',
  2: 'CARRIER',
  3: 'LASER',
  4: 'WALL',
  5: 'FINAL',
}

/**
 * Boss stats configuration
 */
export interface BossStats {
  health: number
  points: number
  phases: number
}

/**
 * Default stats for each boss type
 */
export const BOSS_STATS: Record<BossType, BossStats> = {
  0: { health: 500, points: 5000, phases: 2 },
  1: { health: 750, points: 7500, phases: 2 },
  2: { health: 1000, points: 10000, phases: 3 },
  3: { health: 1500, points: 15000, phases: 3 },
  4: { health: 2000, points: 20000, phases: 4 },
  5: { health: 3000, points: 30000, phases: 5 },
}

/**
 * Wall segment for WALL boss
 */
export interface BossSegment {
  y: number
  hp: number
}

/**
 * Twin data for TWIN boss
 */
export interface BossTwin {
  y: number
  vy: number
}

/**
 * Boss configuration for creation
 */
export interface BossConfig {
  type: BossType
  x: number
  y: number
  stats?: Partial<BossStats>
}

/**
 * Boss entity - powerful enemies at end of waves
 */
export class Boss extends Entity implements Collidable {
  public readonly type: BossType
  public health: number
  public maxHealth: number
  public points: number
  public phase: number = 0
  public maxPhases: number
  public shootTimer: number = 120

  // LASER boss specific
  public charging: boolean = false
  public chargeTime: number = 0

  // WALL boss specific
  public segments: BossSegment[] = []

  // TWIN boss specific
  public twin: BossTwin | null = null

  constructor(id: number, config: BossConfig) {
    super(id, config.x, config.y)

    this.type = config.type
    const baseStats = BOSS_STATS[config.type]
    const stats = { ...baseStats, ...config.stats }

    this.health = stats.health
    this.maxHealth = stats.health
    this.points = stats.points
    this.maxPhases = stats.phases

    // Type-specific initialization
    this.initializeTypeSpecific()
  }

  /**
   * Initialize type-specific properties
   */
  private initializeTypeSpecific(): void {
    switch (this.type) {
      case 1: // TWIN
        this.twin = { y: 100, vy: 0 }
        break

      case 3: // LASER
        this.charging = false
        this.chargeTime = 0
        break

      case 4: // WALL
        this.segments = []
        for (let i = -3; i <= 3; i++) {
          this.segments.push({ y: i * 35, hp: 100 })
        }
        break
    }
  }

  /**
   * Get collision radius based on boss type
   */
  getCollisionRadius(): number {
    switch (this.type) {
      case 4: // WALL
        return 55
      case 5: // FINAL
        return 50
      default:
        return 40
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
   * Take damage, returns true if boss dies
   */
  takeDamage(amount: number): boolean {
    this.health -= amount

    // Check for phase transition
    const healthPercent = this.getHealthPercent()
    const phaseThreshold = 1 - (this.phase + 1) / this.maxPhases

    if (healthPercent < phaseThreshold && this.phase < this.maxPhases - 1) {
      this.phase++
    }

    return this.health <= 0
  }

  /**
   * Take damage to a specific segment (WALL boss)
   */
  takeSegmentDamage(segmentIndex: number, amount: number): boolean {
    if (this.type !== 4 || !this.segments[segmentIndex]) return false

    const segment = this.segments[segmentIndex]!
    segment.hp -= amount

    if (segment.hp <= 0) {
      // Segment destroyed, damage main health
      this.health -= 100
      segment.hp = 0
    }

    return this.health <= 0
  }

  /**
   * Get health percentage (0-1)
   */
  getHealthPercent(): number {
    return this.maxHealth > 0 ? this.health / this.maxHealth : 0
  }

  /**
   * Check if boss can shoot
   */
  canShoot(): boolean {
    return this.shootTimer <= 0
  }

  /**
   * Reset shoot timer with optional variation
   */
  resetShootTimer(base: number = 90, variation: number = 60, randomValue: number = 0): void {
    this.shootTimer = base + Math.floor(randomValue * variation)
  }

  /**
   * Check if laser boss is charging
   */
  isCharging(): boolean {
    return this.type === 3 && this.charging
  }

  /**
   * Start charging (LASER boss)
   */
  startCharging(): void {
    if (this.type === 3) {
      this.charging = true
      this.chargeTime = 0
    }
  }

  /**
   * Update charge time, returns true when ready to fire
   */
  updateCharge(dt: number): boolean {
    if (!this.charging) return false

    this.chargeTime += dt
    if (this.chargeTime >= 2) {
      this.charging = false
      this.chargeTime = 0
      return true  // Ready to fire
    }

    return false
  }

  /**
   * Get charge percentage (0-1)
   */
  getChargePercent(): number {
    if (!this.charging) return 0
    return Math.min(1, this.chargeTime / 2)
  }

  /**
   * Update twin movement (TWIN boss)
   */
  updateTwin(dt: number, randomValue: number): void {
    if (!this.twin) return

    this.twin.vy += (randomValue - 0.5) * 200 * dt
    this.twin.y += this.twin.vy * dt
    this.twin.y = Math.max(-200, Math.min(200, this.twin.y))
    this.twin.vy *= 0.95
  }

  /**
   * Get twin Y position
   */
  getTwinY(): number {
    return this.twin?.y ?? 0
  }

  /**
   * Get living segments (WALL boss)
   */
  getLivingSegments(): BossSegment[] {
    return this.segments.filter(s => s.hp > 0)
  }

  /**
   * Get segment count (WALL boss)
   */
  getSegmentCount(): number {
    return this.segments.length
  }

  /**
   * Get current attack pattern index based on frame
   */
  getPatternIndex(): number {
    return Math.floor(this.frame / 100) % 4
  }

  /**
   * Get boss name
   */
  getName(): string {
    return BOSS_NAMES[this.type]
  }

  update(dt: number): void {
    // Shoot timer
    if (this.shootTimer > 0) {
      this.shootTimer -= dt * 60
    }

    this.frame++
  }

  isDead(): boolean {
    return this.health <= 0
  }

  /**
   * Create boss with default stats
   */
  static create(id: number, type: BossType, x: number, y: number): Boss {
    return new Boss(id, { type, x, y })
  }

  /**
   * Get boss type for a given wave number
   */
  static getTypeForWave(wave: number, bossEveryWaves: number = 5): BossType {
    const bossNumber = Math.floor(wave / bossEveryWaves) - 1
    return Math.min(5, bossNumber) as BossType
  }
}
