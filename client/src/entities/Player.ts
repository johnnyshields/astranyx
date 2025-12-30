import { Entity } from './Entity.ts'
import type { WeaponType } from '../game/weapons/WeaponTypes.ts'

/**
 * Orbital orb configuration
 */
export interface Orb {
  angle: number
  radius: number
}

/**
 * Drone configuration
 */
export interface Drone {
  offsetX: number
  offsetY: number
  x: number
  y: number
  shootTimer: number
}

/**
 * Player weapon slot
 */
export interface PlayerWeapon {
  type: WeaponType
  ammo: number
  maxAmmo: number
}

/**
 * Player powerup state
 */
export interface PlayerPowerups {
  spread: number
  laser: number
  missile: number
  orbit: number
  drone: number
  speed: number
  rapid: number
  pierce: number
}

/**
 * Player configuration for creation
 */
export interface PlayerConfig {
  playerId: string
  x?: number
  y?: number
  lives?: number
  maxShields?: number
  maxWeaponSlots?: number
}

/**
 * Player entity - the player's ship
 */
export class Player extends Entity {
  public readonly playerId: string

  // Health and lives
  public shields: number
  public maxShields: number
  public lives: number
  public dead: boolean = false
  public invincible: number = 0
  public respawnTimer: number = 0

  // Ship progression
  public shipLevel: number = 1  // 1-5

  // Shooting
  public shootCooldown: number = 0
  public chargeTime: number = 0
  public charging: boolean = false
  public baseGunCooldown: number = 0

  // Powerups
  public powerups: PlayerPowerups = {
    spread: 0,
    laser: 0,
    missile: 0,
    orbit: 0,
    drone: 0,
    speed: 0,
    rapid: 0,
    pierce: 0,
  }

  // Orbitals and drones
  public orbs: Orb[] = []
  public drones: Drone[] = []

  // Weapon system
  public weaponSlots: PlayerWeapon[] = []
  public activeWeaponIndex: number = 0
  public maxWeaponSlots: number

  constructor(id: number, config: PlayerConfig) {
    super(id, config.x ?? 0, config.y ?? 0)
    this.playerId = config.playerId
    this.lives = config.lives ?? 3
    this.maxShields = config.maxShields ?? 100
    this.shields = this.maxShields
    this.maxWeaponSlots = config.maxWeaponSlots ?? 2
  }

  /**
   * Get collision radius
   */
  getCollisionRadius(): number {
    return 8
  }

  /**
   * Check if player can take damage
   */
  canTakeDamage(): boolean {
    return !this.dead && this.invincible <= 0
  }

  /**
   * Take damage, returns true if player died
   */
  takeDamage(amount: number): boolean {
    if (!this.canTakeDamage()) return false

    this.shields -= amount

    if (this.shields <= 0) {
      this.shields = 0
      this.die()
      return true
    }

    return false
  }

  /**
   * Die and handle respawn
   */
  die(): void {
    this.dead = true
    this.lives--

    if (this.lives > 0) {
      this.respawnTimer = 120  // 2 seconds at 60fps
    }
  }

  /**
   * Respawn the player
   */
  respawn(x: number, y: number): void {
    this.x = x
    this.y = y
    this.vx = 0
    this.vy = 0
    this.dead = false
    this.shields = this.maxShields
    this.invincible = 180  // 3 seconds invincibility
    this.respawnTimer = 0
    this.chargeTime = 0
    this.charging = false
  }

  /**
   * Heal shields
   */
  heal(amount: number): void {
    this.shields = Math.min(this.maxShields, this.shields + amount)
  }

  /**
   * Get shield percentage (0-1)
   */
  getShieldPercent(): number {
    return this.maxShields > 0 ? this.shields / this.maxShields : 0
  }

  /**
   * Upgrade ship level
   */
  upgradeShip(): void {
    if (this.shipLevel < 5) {
      this.shipLevel++
      this.maxShields += 20
      this.shields = this.maxShields
    }
  }

  /**
   * Add powerup
   */
  addPowerup(type: keyof PlayerPowerups, amount: number = 1): void {
    this.powerups[type] = Math.min(10, this.powerups[type] + amount)

    // Special handling for orbit - add orbs
    if (type === 'orbit') {
      this.updateOrbs()
    }

    // Special handling for drone - add drones
    if (type === 'drone') {
      this.updateDrones()
    }
  }

  /**
   * Update orb count based on orbit powerup
   */
  private updateOrbs(): void {
    const count = this.powerups.orbit
    while (this.orbs.length < count) {
      const angle = (this.orbs.length / count) * Math.PI * 2
      this.orbs.push({ angle, radius: 40 })
    }
  }

  /**
   * Update drone count based on drone powerup
   */
  private updateDrones(): void {
    const count = Math.min(this.powerups.drone, 4)
    const offsets = [
      { x: -30, y: -20 },
      { x: -30, y: 20 },
      { x: -50, y: -30 },
      { x: -50, y: 30 },
    ]

    while (this.drones.length < count) {
      const offset = offsets[this.drones.length]!
      this.drones.push({
        offsetX: offset.x,
        offsetY: offset.y,
        x: this.x + offset.x,
        y: this.y + offset.y,
        shootTimer: 0,
      })
    }
  }

  /**
   * Get active weapon or null
   */
  getActiveWeapon(): PlayerWeapon | null {
    return this.weaponSlots[this.activeWeaponIndex] ?? null
  }

  /**
   * Equip a weapon (add to slot or swap)
   */
  equipWeapon(type: WeaponType, ammo: number, maxAmmo: number): void {
    const weapon: PlayerWeapon = { type, ammo, maxAmmo }

    if (this.weaponSlots.length < this.maxWeaponSlots) {
      this.weaponSlots.push(weapon)
      this.activeWeaponIndex = this.weaponSlots.length - 1
    } else {
      // Replace active weapon
      this.weaponSlots[this.activeWeaponIndex] = weapon
    }
  }

  /**
   * Cycle to next weapon
   */
  cycleWeapon(): void {
    if (this.weaponSlots.length > 1) {
      this.activeWeaponIndex = (this.activeWeaponIndex + 1) % this.weaponSlots.length
    }
  }

  /**
   * Use ammo from active weapon, returns true if successful
   */
  useAmmo(amount: number = 1): boolean {
    const weapon = this.getActiveWeapon()
    if (!weapon) return false

    if (weapon.ammo >= amount) {
      weapon.ammo -= amount
      return true
    }

    return false
  }

  /**
   * Remove empty weapons
   */
  removeEmptyWeapons(): void {
    this.weaponSlots = this.weaponSlots.filter(w => w.ammo > 0)
    if (this.activeWeaponIndex >= this.weaponSlots.length) {
      this.activeWeaponIndex = Math.max(0, this.weaponSlots.length - 1)
    }
  }

  /**
   * Get effective speed multiplier
   */
  getSpeedMultiplier(): number {
    return 1 + this.powerups.speed * 0.1
  }

  /**
   * Get effective fire rate multiplier
   */
  getFireRateMultiplier(): number {
    return 1 + this.powerups.rapid * 0.15
  }

  /**
   * Get pierce count from powerups
   */
  getPierceCount(): number {
    return this.powerups.pierce
  }

  update(dt: number): void {
    if (this.dead) {
      if (this.respawnTimer > 0) {
        this.respawnTimer -= dt * 60
      }
      return
    }

    // Movement
    this.move(dt)

    // Cooldowns
    if (this.shootCooldown > 0) {
      this.shootCooldown -= dt * 60
    }

    if (this.invincible > 0) {
      this.invincible -= dt * 60
    }

    if (this.baseGunCooldown > 0) {
      this.baseGunCooldown -= dt * 60
    }

    // Update orb positions
    for (const orb of this.orbs) {
      orb.angle += 0.05 * dt * 60
    }

    // Update drone positions (lerp to offset)
    for (const drone of this.drones) {
      const targetX = this.x + drone.offsetX
      const targetY = this.y + drone.offsetY
      drone.x += (targetX - drone.x) * 0.1
      drone.y += (targetY - drone.y) * 0.1

      if (drone.shootTimer > 0) {
        drone.shootTimer -= dt * 60
      }
    }

    this.frame++
  }

  isDead(): boolean {
    return this.dead && this.lives <= 0
  }

  /**
   * Create default player
   */
  static create(id: number, playerId: string, x: number = 0, y: number = 0): Player {
    return new Player(id, { playerId, x, y })
  }
}
