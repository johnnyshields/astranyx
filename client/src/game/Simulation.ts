/**
 * Deterministic Game Simulation - Astranyx
 *
 * Ported from delta-v.html with full game mechanics:
 * - Player ship with 5 upgrade levels
 * - 11 powerup types (spread, laser, missile, orbit, drone, speed, rapid, pierce, shield, upgrade, life)
 * - 12+ enemy types with unique behaviors
 * - 6 boss types with attack patterns
 * - Wave spawning system
 * - Score multiplier
 *
 * CRITICAL: Must be 100% deterministic for P2P lockstep.
 * - No Math.random() - use seeded PRNG
 * - No Date.now() - use frame counter
 * - Fixed-point math for positions
 * - Arrays only (no object iteration order issues)
 */

import type { PlayerInput } from '../network/LockstepNetcode.ts'
import {
  type WeaponType,
  type WeaponDrop,
  type PlayerWeapon,
  type WeaponStats,
  WEAPON_STATS,
  getAvailableWeapons,
} from './Weapons.ts'

// ============================================================================
// Fixed-Point Math (16.16 format)
// ============================================================================

const FP_SHIFT = 16
const FP_ONE = 1 << FP_SHIFT

export function toFixed(n: number): number {
  return Math.round(n * FP_ONE)
}

export function fromFixed(n: number): number {
  return n / FP_ONE
}

// ============================================================================
// Seeded PRNG (xorshift32) - Deterministic random
// ============================================================================

export class SeededRandom {
  private state: number

  constructor(seed: number) {
    this.state = seed || 1
  }

  next(): number {
    let x = this.state
    x ^= x << 13
    x ^= x >>> 17
    x ^= x << 5
    this.state = x >>> 0
    return (x >>> 0) / 0xffffffff
  }

  nextInt(max: number): number {
    return Math.floor(this.next() * max)
  }

  nextRange(min: number, max: number): number {
    return min + this.next() * (max - min)
  }

  getSeed(): number {
    return this.state
  }
}

// ============================================================================
// Type Definitions
// ============================================================================

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

export type BossType = 0 | 1 | 2 | 3 | 4 | 5 // CLASSIC, TWIN, CARRIER, LASER, WALL, FINAL

export interface Orb {
  angle: number
  radius: number
}

export interface Drone {
  offsetX: number
  offsetY: number
  x: number
  y: number
  shootTimer: number
}

export interface Player {
  id: number
  playerId: string
  x: number // Fixed-point
  y: number
  vx: number
  vy: number
  shields: number
  maxShields: number
  shipLevel: number // 1-5
  lives: number
  dead: boolean
  invincible: number // frames
  respawnTimer: number
  shootCooldown: number
  chargeTime: number
  charging: boolean
  frame: number
  powerups: {
    spread: number
    laser: number
    missile: number
    orbit: number
    drone: number
    speed: number
    rapid: number
    pierce: number
  }
  orbs: Orb[]
  drones: Drone[]
  // Weapon system
  weaponSlots: PlayerWeapon[]
  activeWeaponIndex: number
  maxWeaponSlots: number
  baseGunCooldown: number
}

export interface Bullet {
  id: number
  x: number // Fixed-point
  y: number
  vx: number
  vy: number
  type: BulletType
  pierce: number
  damage: number
  isEnemy: boolean
  ownerId: string
  lifetime: number
  hitEntities: Set<number> // IDs of entities already hit (for pierce)
}

export interface Beam {
  id: number
  x: number
  y: number
  width: number
  power: number
  ownerId: string
  lifetime: number
  hitEntities: Set<number>
}

export interface Missile {
  id: number
  x: number
  y: number
  vx: number
  vy: number
  targetId: number | null
  ownerId: string
  lifetime: number
  damage: number
}

export interface Enemy {
  id: number
  type: EnemyType
  x: number // Fixed-point
  y: number
  vx: number
  vy: number
  health: number
  maxHealth: number
  points: number
  frame: number
  behavior: number
  shootTimer: number
  hasShield?: boolean
  shieldHealth?: number
  splitCount?: number
  equippedWeapon?: WeaponType // Weapon this enemy carries (drops on death)
}

export interface Boss {
  id: number
  type: BossType
  x: number
  y: number
  health: number
  maxHealth: number
  points: number
  frame: number
  phase: number
  shootTimer: number
  charging?: boolean
  chargeTime?: number
  segments?: Array<{ y: number; hp: number }>
  twin?: { y: number; vy: number }
}

export interface Powerup {
  id: number
  x: number
  y: number
  type: PowerupType
  frame: number
}

export interface Particle {
  id: number
  x: number
  y: number
  vx: number
  vy: number
  life: number
  colorIndex: number
  size: number
}

export interface SimulationState {
  frame: number
  players: Player[]
  bullets: Bullet[]
  beams: Beam[]
  missiles: Missile[]
  enemies: Enemy[]
  boss: Boss | null
  powerups: Powerup[]
  weaponDrops: WeaponDrop[]
  particles: Particle[]
  nextId: number
  rng: SeededRandom
  score: number
  multiplier: number // 1.0 - 8.0
  wave: number
  waveTimer: number
  bossActive: boolean
  screenShake: number
  gameOver: boolean
}

// ============================================================================
// Play Bounds Type (for camera-compensated bounds)
// ============================================================================

export interface PlayBounds {
  leftX: number
  rightX: number
  getTopY: (x: number) => number
  getBottomY: (x: number) => number
}

// ============================================================================
// Game Constants
// ============================================================================

// Default play area (used when no camera-compensated bounds provided)
const DEFAULT_LEFT_X = -750
const DEFAULT_RIGHT_X = 750
const DEFAULT_HALF_HEIGHT_LEFT = 300
const DEFAULT_HALF_HEIGHT_RIGHT = 400

// Helper to get interpolated half-height based on X position (for default bounds)
function getDefaultHalfHeightAtX(x: number): number {
  const t = (x - DEFAULT_LEFT_X) / (DEFAULT_RIGHT_X - DEFAULT_LEFT_X)  // 0 at left edge, 1 at right edge
  return DEFAULT_HALF_HEIGHT_LEFT + t * (DEFAULT_HALF_HEIGHT_RIGHT - DEFAULT_HALF_HEIGHT_LEFT)
}

// Default bounds object
const DEFAULT_BOUNDS: PlayBounds = {
  leftX: DEFAULT_LEFT_X,
  rightX: DEFAULT_RIGHT_X,
  getTopY: (x: number) => getDefaultHalfHeightAtX(x),
  getBottomY: (x: number) => -getDefaultHalfHeightAtX(x),
}

// World space bounds for off-screen entities (spawning, bullets, etc.)
// These are larger than the visible area to allow smooth entry/exit
const WORLD_HALF_WIDTH = 1000  // Spawn enemies this far right
const WORLD_HALF_HEIGHT = 500  // Max vertical extent

// Player constants
const PLAYER_BASE_ACCEL = toFixed(1500)
const PLAYER_BASE_MAX_SPEED = toFixed(800)

// Enemy stats by type
// shootThreshold: how far inside the screen edge before enemy can shoot (larger = waits longer)
const ENEMY_STATS: Record<
  EnemyType,
  { health: number; speed: number; points: number; shootThreshold: number }
> = {
  grunt: { health: 20, speed: 80, points: 50, shootThreshold: 20 },
  shooter: { health: 40, speed: 50, points: 100, shootThreshold: 25 },
  swerver: { health: 25, speed: 100, points: 75, shootThreshold: 18 },
  tank: { health: 150, speed: 30, points: 300, shootThreshold: 50 },
  speeder: { health: 15, speed: 200, points: 60, shootThreshold: 25 },
  bomber: { health: 60, speed: 40, points: 150, shootThreshold: 35 },
  sniper: { health: 50, speed: 20, points: 200, shootThreshold: 30 },
  carrier: { health: 120, speed: 25, points: 400, shootThreshold: 60 },
  mine: { health: 30, speed: 0, points: 40, shootThreshold: 20 },
  spiral: { health: 70, speed: 35, points: 180, shootThreshold: 35 },
  shield: { health: 100, speed: 45, points: 250, shootThreshold: 40 },
  splitter: { health: 80, speed: 60, points: 200, shootThreshold: 30 },
}

// Boss stats by type
const BOSS_STATS: Array<{ health: number; points: number }> = [
  { health: 800, points: 5000 }, // CLASSIC
  { health: 1000, points: 7500 }, // TWIN
  { health: 1200, points: 10000 }, // CARRIER
  { health: 1500, points: 12500 }, // LASER
  { health: 2000, points: 15000 }, // WALL
  { health: 3000, points: 25000 }, // FINAL
]

const POWERUP_TYPES: PowerupType[] = [
  'SHIELD',
  'SHIELD',
  'UPGRADE',
  'SPREAD',
  'LASER',
  'MISSILE',
  'ORBIT',
  'DRONE',
  'SPEED',
  'RAPID',
  'PIERCE',
]

// ============================================================================
// Main Simulation Class
// ============================================================================

export class Simulation {
  private state: SimulationState
  private playerIdMap: Map<string, number> = new Map()
  private playBounds: PlayBounds = DEFAULT_BOUNDS

  constructor(playerIds: string[], seed: number = 12345) {
    this.state = {
      frame: 0,
      players: [],
      bullets: [],
      beams: [],
      missiles: [],
      enemies: [],
      boss: null,
      powerups: [],
      weaponDrops: [],
      particles: [],
      nextId: 1,
      rng: new SeededRandom(seed),
      score: 0,
      multiplier: 1,
      wave: 1,
      waveTimer: 0,
      bossActive: false,
      screenShake: 0,
      gameOver: false,
    }

    // Spawn players
    const spawnY = [-100, 100, -200, 200]
    playerIds.forEach((playerId, index) => {
      const player: Player = {
        id: this.state.nextId++,
        playerId,
        x: toFixed(-350),
        y: toFixed(spawnY[index % 4]!),
        vx: 0,
        vy: 0,
        shields: 100,
        maxShields: 100,
        shipLevel: 1,
        lives: 3,
        dead: false,
        invincible: 180, // 3 seconds at 60fps
        respawnTimer: 0,
        shootCooldown: 0,
        chargeTime: 0,
        charging: false,
        frame: 0,
        powerups: {
          spread: 0,
          laser: 0,
          missile: 0,
          orbit: 0,
          drone: 0,
          speed: 0,
          rapid: 0,
          pierce: 0,
        },
        orbs: [],
        drones: [],
        // Weapon system
        weaponSlots: [],
        activeWeaponIndex: 0,
        maxWeaponSlots: 2,
        baseGunCooldown: 0,
      }
      this.state.players.push(player)
      this.playerIdMap.set(playerId, player.id)
    })
  }

  // ==========================================================================
  // Play Bounds (camera-compensated)
  // ==========================================================================

  /**
   * Update play bounds based on camera projection.
   * This allows the game to adjust to different camera angles.
   * Also nudges players inside if they're currently outside bounds.
   */
  setPlayBounds(bounds: PlayBounds): void {
    this.playBounds = bounds

    // Nudge players inside if they're outside the new bounds
    const nudgeSpeed = 5 // Units per frame to move toward valid position
    for (const player of this.state.players) {
      if (player.dead) continue

      let x = fromFixed(player.x)
      let y = fromFixed(player.y)
      let nudged = false

      // Check X bounds
      const margin = 20
      if (x < bounds.leftX + margin) {
        x = Math.min(x + nudgeSpeed, bounds.leftX + margin)
        nudged = true
      } else if (x > bounds.rightX - margin) {
        x = Math.max(x - nudgeSpeed, bounds.rightX - margin)
        nudged = true
      }

      // Check Y bounds (using X-dependent height)
      const topY = bounds.getTopY(x) - 15
      const bottomY = bounds.getBottomY(x) + 15
      if (y > topY) {
        y = Math.max(y - nudgeSpeed, topY)
        nudged = true
      } else if (y < bottomY) {
        y = Math.min(y + nudgeSpeed, bottomY)
        nudged = true
      }

      if (nudged) {
        player.x = toFixed(x)
        player.y = toFixed(y)
      }
    }
  }

  getPlayBounds(): PlayBounds {
    return this.playBounds
  }

  // ==========================================================================
  // Main Tick
  // ==========================================================================

  tick(inputs: Map<string, PlayerInput>): void {
    if (this.state.gameOver) return

    this.state.frame++
    const dt = 1 / 60 // Fixed timestep

    // Update screen shake
    if (this.state.screenShake > 0) {
      this.state.screenShake -= dt
    }

    // Update multiplier decay
    this.state.multiplier = Math.max(1, this.state.multiplier - 0.07 * dt)

    // Update players
    for (const player of this.state.players) {
      const input = inputs.get(player.playerId) ?? {
        up: false,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
      }
      this.updatePlayer(player, input, dt)
    }

    // Update bullets
    this.updateBullets(dt)

    // Update beams
    this.updateBeams(dt)

    // Update missiles
    this.updateMissiles(dt)

    // Update enemies
    this.updateEnemies(dt)

    // Update boss
    if (this.state.boss) {
      this.updateBoss(dt)
    }

    // Update powerups
    this.updatePowerups(dt)

    // Update weapon drops
    this.updateWeaponDrops(dt)

    // Update particles
    this.updateParticles(dt)

    // Check collisions
    this.checkCollisions()

    // Wave spawning
    this.updateWaveSpawning(dt)

    // Check game over
    this.checkGameOver()
  }

  // ==========================================================================
  // Player Update
  // ==========================================================================

  private updatePlayer(player: Player, input: PlayerInput, dt: number): void {
    // Handle respawn
    if (player.dead && player.lives > 0) {
      player.respawnTimer -= dt * 60 // Convert to frames
      if (player.respawnTimer <= 0) {
        this.respawnPlayer(player)
      }
      return
    }

    if (player.dead) return

    player.frame++

    // Invincibility decay
    if (player.invincible > 0) {
      player.invincible--
    }

    // Shoot cooldown
    if (player.shootCooldown > 0) {
      player.shootCooldown -= dt * 60
    }

    // Movement
    const speedBonus = player.powerups.speed * 50
    const accel = fromFixed(PLAYER_BASE_ACCEL) + player.powerups.speed * 120
    const maxSpeed = fromFixed(PLAYER_BASE_MAX_SPEED) + speedBonus
    const friction = 0.91

    let dvx = 0
    let dvy = 0

    if (input.up) dvy -= accel * dt
    if (input.down) dvy += accel * dt
    if (input.left) dvx -= accel * dt
    if (input.right) dvx += accel * dt

    // Slight gravity (set to 0 for now)
    const gravity = 0
    dvy += gravity * dt

    // Fugoid oscillation when idle (subtle up/down drift, max +/-20 units)
    const isMoving = input.up || input.down || input.left || input.right
    if (!isMoving) {
      // Oscillation period ~3 seconds (180 frames at 60fps)
      const oscillationPhase = (player.frame % 180) / 180 * Math.PI * 2
      // Apply gentle sinusoidal force - tuned so amplitude stays within +/-20 units
      dvy += Math.sin(oscillationPhase) * 25 * dt
    }

    // Apply velocity changes
    let vx = fromFixed(player.vx) + dvx
    let vy = fromFixed(player.vy) + dvy

    // Apply friction
    vx *= friction
    vy *= friction

    // Clamp speed
    const speed = Math.hypot(vx, vy)
    if (speed > maxSpeed) {
      vx = (vx / speed) * maxSpeed
      vy = (vy / speed) * maxSpeed
    }

    // Update position
    let x = fromFixed(player.x) + vx * dt
    let y = fromFixed(player.y) + vy * dt

    // Clamp to play area (camera-compensated bounds)
    const bounds = this.playBounds
    const margin = 20
    x = Math.max(bounds.leftX + margin, Math.min(bounds.rightX - margin, x))
    const topY = bounds.getTopY(x) - 15
    const bottomY = bounds.getBottomY(x) + 15
    // Absolute Y limits to prevent camping in corners
    const absoluteMaxY = 400
    const absoluteMinY = -400
    y = Math.max(Math.max(bottomY, absoluteMinY), Math.min(Math.min(topY, absoluteMaxY), y))

    player.x = toFixed(x)
    player.y = toFixed(y)
    player.vx = toFixed(vx)
    player.vy = toFixed(vy)

    // Shooting
    if (input.fire) {
      player.chargeTime += dt
      if (player.chargeTime < 0.3 && player.shootCooldown <= 0) {
        this.playerShoot(player, false)
      }
      if (player.chargeTime >= 0.5) {
        player.charging = true
      }
    } else {
      if (player.charging && player.chargeTime >= 0.5) {
        this.playerShoot(player, true)
      }
      player.chargeTime = 0
      player.charging = false
    }

    // Update orbs
    for (const orb of player.orbs) {
      orb.angle += (2.5 + player.powerups.orbit * 0.3) * dt
    }

    // Update drones
    for (const drone of player.drones) {
      const tx = x + drone.offsetX
      const ty = y + drone.offsetY
      drone.x += (tx - drone.x) * 6 * dt
      drone.y += (ty - drone.y) * 6 * dt

      drone.shootTimer -= dt
      if (drone.shootTimer <= 0) {
        drone.shootTimer = 0.25 - player.powerups.rapid * 0.03
        this.spawnBullet(
          toFixed(drone.x + 8),
          toFixed(drone.y),
          toFixed(380),
          0,
          'drone',
          player.powerups.pierce,
          10,
          false,
          player.playerId
        )
      }
    }

    // Weapon system: update cooldowns
    for (const weapon of player.weaponSlots) {
      if (weapon.cooldown > 0) {
        weapon.cooldown -= dt * 60
      }
    }

    // Weapon swap (Q key - edge triggered)
    if (input.swap) {
      this.cycleWeapon(player)
    }

    // Manual weapon pickup (E key - edge triggered)
    if (input.pickup) {
      const pickedUp = this.tryManualPickup(player)
      if (pickedUp) {
        // Remove the picked up drop from state
        this.state.weaponDrops = this.state.weaponDrops.filter(d => d.id !== pickedUp.id)
      }
    }

    // Secondary fire (equipped weapon)
    if (input.secondary && player.weaponSlots.length > 0) {
      const weapon = player.weaponSlots[player.activeWeaponIndex]
      if (weapon && weapon.cooldown <= 0 && weapon.ammo > 0) {
        this.fireWeapon(player, weapon)
      }
    }
  }

  private respawnPlayer(player: Player): void {
    player.x = toFixed(-350)
    player.y = toFixed(0)
    player.vx = 0
    player.vy = 0
    player.shields = player.maxShields
    player.dead = false
    player.invincible = 180 // 3 seconds
    player.respawnTimer = 0
    player.chargeTime = 0
    player.charging = false
    // Keep ship level and weapon powerups, but reset orbs and drones
    player.orbs = []
    player.drones = []
    player.powerups.orbit = 0
    player.powerups.drone = 0
  }

  private playerShoot(player: Player, charged: boolean): void {
    const x = player.x
    const y = player.y
    const recoil = charged ? 50 : 8
    player.vx -= toFixed(recoil)
    this.state.screenShake = charged ? 0.1 : 0.015

    if (charged) {
      // Charged shot: mega bullet + laser beam + missiles
      if (player.powerups.laser > 0) {
        this.spawnBeam(
          x + toFixed(15),
          y,
          player.powerups.laser + player.shipLevel,
          player.playerId
        )
      }

      this.spawnBullet(
        x + toFixed(15),
        y,
        toFixed(420),
        0,
        'mega',
        player.powerups.pierce + 2,
        40,
        false,
        player.playerId
      )

      if (player.powerups.missile > 0) {
        const count = player.powerups.missile + player.shipLevel
        for (let i = 0; i < count; i++) {
          // Stagger missile spawns using frame offset
          this.spawnMissile(
            x,
            y + toFixed((i - count / 2) * 10),
            player.playerId
          )
        }
      }

      player.shootCooldown = 15 // 0.25 seconds
    } else {
      // Normal shot
      const baseShots = player.shipLevel
      const rapidMod = 1 - player.powerups.rapid * 0.15

      for (let i = 0; i < baseShots; i++) {
        const spread = (i - (baseShots - 1) / 2) * 6
        this.spawnBullet(
          x + toFixed(12),
          y + toFixed(spread),
          toFixed(360),
          0,
          'shot',
          player.powerups.pierce,
          15,
          false,
          player.playerId
        )
      }

      // Spread shots
      if (player.powerups.spread >= 1) {
        this.spawnBullet(
          x + toFixed(10),
          y,
          toFixed(330),
          toFixed(-45),
          'spread',
          player.powerups.pierce,
          12,
          false,
          player.playerId
        )
        this.spawnBullet(
          x + toFixed(10),
          y,
          toFixed(330),
          toFixed(45),
          'spread',
          player.powerups.pierce,
          12,
          false,
          player.playerId
        )
      }
      if (player.powerups.spread >= 2) {
        this.spawnBullet(
          x + toFixed(8),
          y,
          toFixed(300),
          toFixed(-90),
          'spread',
          player.powerups.pierce,
          10,
          false,
          player.playerId
        )
        this.spawnBullet(
          x + toFixed(8),
          y,
          toFixed(300),
          toFixed(90),
          'spread',
          player.powerups.pierce,
          10,
          false,
          player.playerId
        )
      }
      if (player.powerups.spread >= 3) {
        this.spawnBullet(
          x + toFixed(5),
          y,
          toFixed(280),
          toFixed(-130),
          'spread',
          player.powerups.pierce,
          8,
          false,
          player.playerId
        )
        this.spawnBullet(
          x + toFixed(5),
          y,
          toFixed(280),
          toFixed(130),
          'spread',
          player.powerups.pierce,
          8,
          false,
          player.playerId
        )
      }

      // Laser shots
      if (player.powerups.laser > 0) {
        this.spawnBullet(
          x + toFixed(15),
          y,
          toFixed(500),
          0,
          'laser',
          player.powerups.pierce + 1,
          20,
          false,
          player.playerId
        )
      }

      player.shootCooldown =
        (7 - player.shipLevel * 0.5) * rapidMod // frames
    }
  }

  private playerTakeDamage(player: Player, amount: number): boolean {
    if (player.invincible > 0) return false

    // Orbs absorb damage
    if (player.orbs.length > 0) {
      player.orbs.pop()
      player.powerups.orbit--
      this.state.screenShake = 0.1
      return false
    }

    player.shields -= amount
    player.invincible = 30 // 0.5 seconds
    this.state.screenShake = 0.15

    if (player.shields <= 0) {
      this.playerDie(player)
      return true
    }

    return false
  }

  private playerDie(player: Player): void {
    player.dead = true
    this.state.screenShake = 0.5
    this.spawnExplosion(player.x, player.y, 50)
    player.lives--

    if (player.lives > 0) {
      player.respawnTimer = 120 // 2 seconds
    }
  }

  private upgradePlayerShip(player: Player): void {
    if (player.shipLevel < 5) {
      player.shipLevel++
      player.maxShields += 25
      player.shields = Math.min(player.shields + 50, player.maxShields)
      this.state.screenShake = 0.3
    }
  }

  private addPlayerPowerup(player: Player, type: PowerupType): void {
    switch (type) {
      case 'SHIELD':
        player.shields = Math.min(player.shields + 35, player.maxShields)
        break
      case 'UPGRADE':
        this.upgradePlayerShip(player)
        break
      case 'SPREAD':
        player.powerups.spread = Math.min(player.powerups.spread + 1, 3)
        break
      case 'LASER':
        player.powerups.laser = Math.min(player.powerups.laser + 1, 3)
        break
      case 'MISSILE':
        player.powerups.missile = Math.min(player.powerups.missile + 1, 3)
        break
      case 'RAPID':
        player.powerups.rapid = Math.min(player.powerups.rapid + 1, 3)
        break
      case 'PIERCE':
        player.powerups.pierce = Math.min(player.powerups.pierce + 1, 2)
        break
      case 'ORBIT':
        if (player.powerups.orbit < 6) {
          player.powerups.orbit++
          player.orbs.push({
            angle: (player.powerups.orbit - 1) * (Math.PI / 3),
            radius: 28 + player.shipLevel * 4,
          })
        }
        break
      case 'DRONE':
        if (player.powerups.drone < 4) {
          player.powerups.drone++
          const positions = [
            [-1, -1],
            [1, -1],
            [-1, 1],
            [1, 1],
          ]
          const pos = positions[player.powerups.drone - 1]!
          player.drones.push({
            offsetX: -15 + pos[0]! * 5,
            offsetY: pos[1]! * (15 + player.powerups.drone * 5),
            x: fromFixed(player.x) - 15 + pos[0]! * 5,
            y: fromFixed(player.y) + pos[1]! * (15 + player.powerups.drone * 5),
            shootTimer: this.state.rng.next(),
          })
        }
        break
      case 'SPEED':
        player.powerups.speed = Math.min(player.powerups.speed + 1, 3)
        break
      case 'LIFE':
        player.lives++
        this.state.screenShake = 0.2
        break
    }
  }

  // ==========================================================================
  // Bullet System
  // ==========================================================================

  private spawnBullet(
    x: number,
    y: number,
    vx: number,
    vy: number,
    type: BulletType,
    pierce: number,
    damage: number,
    isEnemy: boolean,
    ownerId: string
  ): void {
    this.state.bullets.push({
      id: this.state.nextId++,
      x,
      y,
      vx,
      vy,
      type,
      pierce,
      damage,
      isEnemy,
      ownerId,
      lifetime: 300, // 5 seconds
      hitEntities: new Set(),
    })
  }

  private spawnBeam(
    x: number,
    y: number,
    power: number,
    ownerId: string
  ): void {
    this.state.beams.push({
      id: this.state.nextId++,
      x,
      y,
      width: toFixed(800),
      power,
      ownerId,
      lifetime: 20, // ~0.33 seconds
      hitEntities: new Set(),
    })
  }

  private spawnMissile(x: number, y: number, ownerId: string): void {
    // Find nearest enemy to target
    let targetId: number | null = null
    let minDist = Infinity

    for (const enemy of this.state.enemies) {
      const dist = Math.hypot(
        fromFixed(enemy.x) - fromFixed(x),
        fromFixed(enemy.y) - fromFixed(y)
      )
      if (dist < minDist) {
        minDist = dist
        targetId = enemy.id
      }
    }

    // Also check boss
    if (this.state.boss) {
      const dist = Math.hypot(
        fromFixed(this.state.boss.x) - fromFixed(x),
        fromFixed(this.state.boss.y) - fromFixed(y)
      )
      if (dist < minDist) {
        targetId = this.state.boss.id
      }
    }

    this.state.missiles.push({
      id: this.state.nextId++,
      x,
      y,
      vx: toFixed(100 + this.state.rng.next() * 50),
      vy: toFixed((this.state.rng.next() - 0.5) * 100),
      targetId,
      ownerId,
      lifetime: 300,
      damage: 25,
    })
  }

  private updateBullets(dt: number): void {
    const toRemove: number[] = []

    for (const bullet of this.state.bullets) {
      // Update position
      bullet.x += Math.round(bullet.vx * dt)
      bullet.y += Math.round(bullet.vy * dt)
      bullet.lifetime--

      // Check bounds - player bullets go further right to hit off-screen enemies
      const x = fromFixed(bullet.x)
      const y = fromFixed(bullet.y)
      const rightBound = bullet.isEnemy ? WORLD_HALF_WIDTH + 50 : WORLD_HALF_WIDTH + 500  // Player shots go further

      if (
        x < -WORLD_HALF_WIDTH - 50 ||
        x > rightBound ||
        y < -WORLD_HALF_HEIGHT - 50 ||
        y > WORLD_HALF_HEIGHT + 50 ||
        bullet.lifetime <= 0
      ) {
        toRemove.push(bullet.id)
      }
    }

    this.state.bullets = this.state.bullets.filter(
      (b) => !toRemove.includes(b.id)
    )
  }

  private updateBeams(_dt: number): void {
    for (const beam of this.state.beams) {
      beam.lifetime--
    }
    this.state.beams = this.state.beams.filter((b) => b.lifetime > 0)
  }

  private updateMissiles(dt: number): void {
    const toRemove: number[] = []

    for (const missile of this.state.missiles) {
      // Find target position
      let targetX = fromFixed(missile.x) + 200
      let targetY = fromFixed(missile.y)

      if (missile.targetId !== null) {
        const enemy = this.state.enemies.find((e) => e.id === missile.targetId)
        if (enemy) {
          targetX = fromFixed(enemy.x)
          targetY = fromFixed(enemy.y)
        } else if (
          this.state.boss &&
          this.state.boss.id === missile.targetId
        ) {
          targetX = fromFixed(this.state.boss.x)
          targetY = fromFixed(this.state.boss.y)
        }
      }

      // Home towards target
      const mx = fromFixed(missile.x)
      const my = fromFixed(missile.y)
      const angle = Math.atan2(targetY - my, targetX - mx)
      const speed = 250

      const vx = fromFixed(missile.vx)
      const vy = fromFixed(missile.vy)
      const newVx = vx + Math.cos(angle) * 500 * dt
      const newVy = vy + Math.sin(angle) * 500 * dt

      const currentSpeed = Math.hypot(newVx, newVy)
      missile.vx = toFixed((newVx / currentSpeed) * speed)
      missile.vy = toFixed((newVy / currentSpeed) * speed)

      missile.x += Math.round(missile.vx * dt)
      missile.y += Math.round(missile.vy * dt)
      missile.lifetime--

      // Check bounds - missiles can go further right to hit off-screen enemies
      if (
        mx < -WORLD_HALF_WIDTH - 50 ||
        mx > WORLD_HALF_WIDTH + 500 ||
        my < -WORLD_HALF_HEIGHT - 50 ||
        my > WORLD_HALF_HEIGHT + 50 ||
        missile.lifetime <= 0
      ) {
        toRemove.push(missile.id)
      }
    }

    this.state.missiles = this.state.missiles.filter(
      (m) => !toRemove.includes(m.id)
    )
  }

  // ==========================================================================
  // Enemy System
  // ==========================================================================

  private spawnEnemy(type: EnemyType, x: number, y: number): void {
    const stats = ENEMY_STATS[type]

    // Determine if this enemy has a weapon (based on enemy type and wave)
    // Stronger enemies more likely to have weapons
    let equippedWeapon: WeaponType | undefined
    const weaponChance = this.getEnemyWeaponChance(type)
    if (this.state.rng.next() < weaponChance) {
      const availableWeapons = getAvailableWeapons(this.state.wave)
      equippedWeapon = availableWeapons[this.state.rng.nextInt(availableWeapons.length)]
    }

    this.state.enemies.push({
      id: this.state.nextId++,
      type,
      x,
      y,
      vx: toFixed(-stats.speed),
      vy: 0,
      health: stats.health,
      maxHealth: stats.health,
      points: stats.points,
      frame: 0,
      behavior: this.state.rng.nextInt(4),
      shootTimer: 60 + this.state.rng.nextInt(120),
      hasShield: type === 'shield',
      shieldHealth: type === 'shield' ? 50 : 0,
      splitCount: type === 'splitter' ? 2 : 0,
      equippedWeapon,
    })
  }

  // Chance for enemy type to have a weapon equipped
  private getEnemyWeaponChance(type: EnemyType): number {
    switch (type) {
      case 'tank': return 0.8       // Heavy enemies almost always have weapons
      case 'carrier': return 0.9
      case 'shield': return 0.7
      case 'bomber': return 0.6
      case 'sniper': return 0.5
      case 'shooter': return 0.4
      case 'spiral': return 0.4
      case 'splitter': return 0.3
      case 'swerver': return 0.25
      case 'grunt': return 0.15     // Basic enemies rarely have weapons
      case 'speeder': return 0.2
      case 'mine': return 0         // Mines never have weapons
      default: return 0.2
    }
  }

  private updateEnemies(dt: number): void {
    const toRemove: number[] = []
    const visibleRightX = this.playBounds.rightX  // Use camera-compensated bounds for visibility

    for (const enemy of this.state.enemies) {
      enemy.frame++

      // Update position
      enemy.x += Math.round(enemy.vx * dt)
      enemy.y += Math.round(enemy.vy * dt)

      const x = fromFixed(enemy.x)

      // Type-specific behavior
      this.updateEnemyBehavior(enemy, dt)

      // Shooting - only when on-screen (threshold varies by enemy size)
      const shootThreshold = ENEMY_STATS[enemy.type].shootThreshold
      if (x < visibleRightX - shootThreshold) {
        enemy.shootTimer -= dt * 60
        if (enemy.shootTimer <= 0) {
          this.enemyShoot(enemy)
          enemy.shootTimer = 60 + this.state.rng.nextInt(180)
        }
      }

      // Check bounds (remove if off-screen left)
      if (x < -WORLD_HALF_WIDTH - 100) {
        toRemove.push(enemy.id)
      }
    }

    this.state.enemies = this.state.enemies.filter(
      (e) => !toRemove.includes(e.id)
    )
  }

  private updateEnemyBehavior(enemy: Enemy, dt: number): void {
    const x = fromFixed(enemy.x)
    const topY = this.playBounds.getTopY(x)
    const bottomY = this.playBounds.getBottomY(x)

    switch (enemy.type) {
      case 'grunt':
        // Simple sine wave
        enemy.vy = toFixed(Math.sin(enemy.frame * 0.05) * 80)
        break

      case 'swerver':
        // Fast sine wave
        enemy.vy = toFixed(Math.sin(enemy.frame * 0.1) * 120)
        break

      case 'speeder':
        // Straight line, occasional dodge
        if (enemy.frame % 60 === 0 && this.state.rng.next() < 0.3) {
          enemy.vy = toFixed((this.state.rng.next() - 0.5) * 200)
        }
        enemy.vy = toFixed(fromFixed(enemy.vy) * 0.95)
        break

      case 'bomber':
        // Slow descent
        enemy.vy = toFixed(30)
        break

      case 'sniper':
        // Stays still and aims
        enemy.vx = toFixed(-10)
        break

      case 'mine':
        // Stationary
        enemy.vx = 0
        enemy.vy = 0
        break

      case 'spiral':
        // Spiral pattern
        enemy.vy = toFixed(Math.sin(enemy.frame * 0.08) * 100)
        enemy.vx = toFixed(-35 + Math.cos(enemy.frame * 0.08) * 30)
        break

      case 'tank':
      case 'carrier':
      case 'shooter':
        // Slow steady movement
        enemy.vy = toFixed(Math.sin(enemy.frame * 0.03) * 40)
        break

      case 'shield':
        // Protective movement
        enemy.vy = toFixed(Math.sin(enemy.frame * 0.04) * 60)
        break

      case 'splitter':
        // Erratic movement
        enemy.vy = toFixed(Math.sin(enemy.frame * 0.07 + enemy.id) * 90)
        break
    }

    // Clamp Y position using camera-compensated bounds
    const y = fromFixed(enemy.y)
    if (y < bottomY + 30) {
      enemy.y = toFixed(bottomY + 30)
      enemy.vy = Math.abs(enemy.vy)
    }
    if (y > topY - 30) {
      enemy.y = toFixed(topY - 30)
      enemy.vy = -Math.abs(enemy.vy)
    }
  }

  private enemyShoot(enemy: Enemy): void {
    const closestPlayer = this.getClosestPlayer(enemy.x, enemy.y)
    if (!closestPlayer) return

    switch (enemy.type) {
      case 'shooter':
        // Aimed shot
        {
          const angle = Math.atan2(
            fromFixed(closestPlayer.y - enemy.y),
            fromFixed(closestPlayer.x - enemy.x)
          )
          this.spawnBullet(
            enemy.x - toFixed(20),
            enemy.y,
            toFixed(Math.cos(angle) * 160),
            toFixed(Math.sin(angle) * 160),
            'aimed',
            0,
            18,
            true,
            ''
          )
        }
        break

      case 'sniper':
        // Fast aimed shot
        {
          const angle = Math.atan2(
            fromFixed(closestPlayer.y - enemy.y),
            fromFixed(closestPlayer.x - enemy.x)
          )
          this.spawnBullet(
            enemy.x - toFixed(20),
            enemy.y,
            toFixed(Math.cos(angle) * 300),
            toFixed(Math.sin(angle) * 300),
            'aimed',
            0,
            25,
            true,
            ''
          )
        }
        break

      case 'bomber':
        // Drop bombs
        this.spawnBullet(
          enemy.x,
          enemy.y + toFixed(15),
          toFixed(-20),
          toFixed(100),
          'big',
          0,
          30,
          true,
          ''
        )
        break

      case 'spiral':
        // Spiral bullets
        for (let i = 0; i < 8; i++) {
          const angle = enemy.frame * 0.08 + (i / 8) * Math.PI * 2
          this.spawnBullet(
            enemy.x,
            enemy.y,
            toFixed(Math.cos(angle) * 70),
            toFixed(Math.sin(angle) * 70),
            'ring',
            0,
            15,
            true,
            ''
          )
        }
        break

      case 'carrier':
        // Spawn mini-enemies
        if (this.state.enemies.length < 20) {
          const types: EnemyType[] = ['grunt', 'shooter', 'swerver']
          const type = types[this.state.rng.nextInt(types.length)]!
          this.spawnEnemy(type, enemy.x - toFixed(20), enemy.y)
        }
        break

      default:
        // Basic enemy shot
        this.spawnBullet(
          enemy.x - toFixed(20),
          enemy.y,
          toFixed(-100),
          0,
          'enemy',
          0,
          18,
          true,
          ''
        )
        break
    }
  }

  private enemyDie(enemy: Enemy): void {
    this.spawnExplosion(enemy.x, enemy.y, 12)
    this.state.score += Math.floor(enemy.points * this.state.multiplier)
    this.state.multiplier = Math.min(8, this.state.multiplier + 0.2)
    this.state.screenShake = 0.08

    // Drop weapon if enemy had one equipped
    if (enemy.equippedWeapon) {
      this.spawnWeaponDrop(enemy.x, enemy.y, enemy.equippedWeapon)
    } else if (this.state.rng.next() < 0.3) {
      // Otherwise chance to drop powerup
      this.spawnPowerup(enemy.x, enemy.y)
    }

    // Splitter spawns smaller enemies
    if (enemy.type === 'splitter' && enemy.splitCount && enemy.splitCount > 0) {
      this.spawnEnemy('grunt', enemy.x + toFixed(20), enemy.y - toFixed(20))
      this.spawnEnemy('grunt', enemy.x + toFixed(20), enemy.y + toFixed(20))
    }
  }

  private spawnWeaponDrop(x: number, y: number, weaponType: WeaponType): void {
    const stats = WEAPON_STATS[weaponType]
    this.state.weaponDrops.push({
      id: this.state.nextId++,
      x,
      y,
      weaponType,
      ammo: stats.ammoPerPickup,
      frame: 0,
    })
  }

  // ==========================================================================
  // Weapon Firing System
  // ==========================================================================

  private fireWeapon(player: Player, weapon: PlayerWeapon): void {
    const stats = WEAPON_STATS[weapon.type]

    // Weapon mount position: forward and below player center (matching render position)
    // Player scale is ~50-62 based on level, weapon is at +25% forward, -20% below
    const weaponOffsetX = toFixed(35)  // Forward from player center to weapon muzzle
    const weaponOffsetY = toFixed(-12) // Below center where weapon is mounted
    const x = player.x + weaponOffsetX
    const y = player.y + weaponOffsetY

    // Apply recoil based on weapon
    const recoil = this.getWeaponRecoil(weapon.type)
    player.vx -= toFixed(recoil)

    // Screen shake based on weapon power
    this.state.screenShake = Math.max(this.state.screenShake, stats.damage / 500)

    // Fire based on weapon special behavior
    switch (stats.special) {
      case 'none':
        this.fireStandardWeapon(player, x, y, stats)
        break
      case 'homing':
        this.fireHomingMissile(player, x, y, stats)
        break
      case 'explosive':
        this.fireExplosiveShell(player, x, y, stats)
        break
      case 'deployable':
        this.deployMine(player, stats)
        break
      case 'continuous':
        this.fireContinuous(player, x, y, stats)
        break
      case 'puddle':
        this.fireAcidBlob(player, x, y, stats)
        break
      case 'wave':
        this.fireSonicWave(player, x, y, stats)
        break
      case 'beam':
      case 'beam_wide':
        this.fireLaserBeam(player, stats)
        break
      case 'chain':
        this.fireLightning(player, x, y, stats)
        break
      case 'melee':
        this.swingSword(player, stats)
        break
      case 'instant_hit':
        this.fireRailgun(player, x, y, stats)
        break
      case 'bouncing':
        this.fireGrenade(player, x, y, stats)
        break
    }

    // Consume ammo AFTER firing (so last shot fires)
    weapon.ammo -= 1
    weapon.cooldown = stats.fireRate
    if (weapon.ammo < 0) {
      weapon.ammo = 0
    }
  }

  private findNearestEnemy(x: number, y: number): Enemy | null {
    let nearest: Enemy | null = null
    let minDist = Infinity

    for (const enemy of this.state.enemies) {
      const dist = Math.hypot(
        fromFixed(enemy.x) - fromFixed(x),
        fromFixed(enemy.y) - fromFixed(y)
      )
      if (dist < minDist) {
        minDist = dist
        nearest = enemy
      }
    }

    return nearest
  }

  private getWeaponRecoil(type: WeaponType): number {
    switch (type) {
      case 'vulcan': return 2
      case 'shotgun': return 15
      case 'spread_small': return 5
      case 'spread_large': return 8
      case 'railgun': return 30
      case 'missile': return 10
      case 'cannon': return 25
      case 'mine': return 5
      case 'grenade': return 12
      case 'flame': return 1
      case 'acid': return 8
      case 'sonic': return 10
      case 'laser_small': return 0
      case 'laser_large': return 2
      case 'lightning': return 8
      case 'sword': return 15
      default: return 5
    }
  }

  private fireStandardWeapon(player: Player, x: number, y: number, stats: WeaponStats): void {
    const baseAngle = 0
    const spreadStep = stats.projectileCount > 1
      ? stats.spread / (stats.projectileCount - 1)
      : 0
    const startAngle = baseAngle - stats.spread / 2

    for (let i = 0; i < stats.projectileCount; i++) {
      const angle = startAngle + spreadStep * i + (this.state.rng.next() - 0.5) * 0.05
      const cos = Math.cos(angle)
      const sin = Math.sin(angle)

      this.spawnBullet(
        x,
        y,
        toFixed(stats.projectileSpeed * cos),
        toFixed(stats.projectileSpeed * sin),
        'shot', // Using existing bullet type for now
        stats.pierce,
        stats.damage,
        false,
        player.playerId
      )
    }
  }

  private fireHomingMissile(player: Player, x: number, y: number, stats: WeaponStats): void {
    // Find nearest enemy for targeting
    const target = this.findNearestEnemy(x, y)

    this.state.missiles.push({
      id: this.state.nextId++,
      x: fromFixed(x),
      y: fromFixed(y),
      vx: stats.projectileSpeed * 0.3, // Start slow
      vy: 0,
      targetId: target ? target.id : null,
      ownerId: player.playerId,
      lifetime: stats.lifetime,
      damage: stats.damage,
    })
  }

  private fireExplosiveShell(player: Player, x: number, y: number, stats: WeaponStats): void {
    // Fire as a regular bullet that will explode on impact
    this.spawnBullet(
      x,
      y,
      toFixed(stats.projectileSpeed),
      0,
      'mega', // Use mega type for explosive visual
      0, // No pierce - explodes on first hit
      stats.damage,
      false,
      player.playerId
    )
  }

  private deployMine(player: Player, stats: WeaponStats): void {
    // Deploy mine behind player
    const x = player.x - toFixed(30)
    const y = player.y

    this.spawnBullet(
      x,
      y,
      toFixed(-stats.projectileSpeed), // Drift backward
      0,
      'shot',
      0,
      stats.damage,
      false,
      player.playerId
    )
  }

  private fireContinuous(player: Player, x: number, y: number, stats: WeaponStats): void {
    // Flamethrower - multiple small projectiles
    for (let i = 0; i < stats.projectileCount; i++) {
      const angle = (this.state.rng.next() - 0.5) * stats.spread
      const speedVar = 0.8 + this.state.rng.next() * 0.4

      this.spawnBullet(
        x,
        y,
        toFixed(stats.projectileSpeed * speedVar * Math.cos(angle)),
        toFixed(stats.projectileSpeed * speedVar * Math.sin(angle)),
        'shot',
        stats.pierce,
        stats.damage,
        false,
        player.playerId
      )
    }
  }

  private fireAcidBlob(player: Player, x: number, y: number, stats: WeaponStats): void {
    // Acid blob - arcing projectile
    this.spawnBullet(
      x,
      y,
      toFixed(stats.projectileSpeed),
      toFixed(-50), // Arc upward slightly
      'shot',
      0,
      stats.damage,
      false,
      player.playerId
    )
  }

  private fireSonicWave(player: Player, x: number, y: number, stats: WeaponStats): void {
    // Sonic wave - wide projectile
    this.spawnBullet(
      x,
      y,
      toFixed(stats.projectileSpeed),
      0,
      'spread',
      stats.pierce,
      stats.damage,
      false,
      player.playerId
    )
  }

  private fireLaserBeam(player: Player, stats: WeaponStats): void {
    // Instant beam - hits everything in a line
    const width = stats.special === 'beam_wide' ? 20 : 8

    this.state.beams.push({
      id: this.state.nextId++,
      x: fromFixed(player.x) + 25,
      y: fromFixed(player.y),
      width,
      power: stats.damage,
      ownerId: player.playerId,
      lifetime: 3, // Very brief
      hitEntities: new Set(),
    })
  }

  private fireLightning(player: Player, x: number, y: number, stats: WeaponStats): void {
    // Lightning bolt - fast projectile
    this.spawnBullet(
      x,
      y,
      toFixed(stats.projectileSpeed),
      0,
      'laser',
      0, // Chain effect handled separately
      stats.damage,
      false,
      player.playerId
    )
  }

  private swingSword(player: Player, stats: WeaponStats): void {
    // Melee attack - damage enemies in front of player
    const attackX = fromFixed(player.x) + 40
    const attackY = fromFixed(player.y)
    const range = 50

    for (const enemy of this.state.enemies) {
      const ex = fromFixed(enemy.x)
      const ey = fromFixed(enemy.y)
      const dx = ex - attackX
      const dy = ey - attackY

      if (Math.abs(dx) < range && Math.abs(dy) < range * 0.8) {
        this.damageEnemy(enemy, stats.damage)
      }
    }

    // Also damage boss if in range
    if (this.state.boss) {
      const bx = fromFixed(this.state.boss.x)
      const by = fromFixed(this.state.boss.y)
      const dx = bx - attackX
      const dy = by - attackY

      if (Math.abs(dx) < range + 50 && Math.abs(dy) < range + 50) {
        this.damageBoss(stats.damage)
      }
    }

    this.state.screenShake = 0.15
  }

  private fireRailgun(player: Player, x: number, y: number, stats: WeaponStats): void {
    // Railgun - instant hit line
    this.state.beams.push({
      id: this.state.nextId++,
      x: fromFixed(x),
      y: fromFixed(y),
      width: 6,
      power: stats.damage,
      ownerId: player.playerId,
      lifetime: 8,
      hitEntities: new Set(),
    })

    this.state.screenShake = 0.2
  }

  private fireGrenade(player: Player, x: number, y: number, stats: WeaponStats): void {
    // Grenade - arcing projectile
    this.spawnBullet(
      x,
      y,
      toFixed(stats.projectileSpeed * 0.8),
      toFixed(-100), // Arc upward
      'mega',
      0,
      stats.damage,
      false,
      player.playerId
    )
  }

  private damageEnemy(enemy: Enemy, damage: number): void {
    if (enemy.hasShield && enemy.shieldHealth && enemy.shieldHealth > 0) {
      enemy.shieldHealth -= damage
      if (enemy.shieldHealth <= 0) {
        enemy.hasShield = false
        enemy.shieldHealth = 0
      }
    } else {
      enemy.health -= damage
    }

    if (enemy.health <= 0) {
      this.enemyDie(enemy)
      enemy.health = 0
    }
  }

  private damageBoss(damage: number): void {
    if (!this.state.boss) return
    this.state.boss.health -= damage
    if (this.state.boss.health <= 0) {
      this.bossDie(this.state.boss)
    }
  }

  // ==========================================================================
  // Boss System
  // ==========================================================================

  private spawnBoss(type: BossType): void {
    const stats = BOSS_STATS[type]!

    const boss: Boss = {
      id: this.state.nextId++,
      type,
      x: toFixed(WORLD_HALF_WIDTH + 450),  // Spawn off-screen
      y: toFixed(0),
      health: stats.health,
      maxHealth: stats.health,
      points: stats.points,
      frame: 0,
      phase: 0,
      shootTimer: 120,
    }

    // Type-specific initialization
    if (type === 3) {
      // LASER boss
      boss.charging = false
      boss.chargeTime = 0
    }

    if (type === 4) {
      // WALL boss
      boss.segments = []
      for (let i = -3; i <= 3; i++) {
        boss.segments.push({ y: i * 35, hp: 100 })
      }
    }

    if (type === 1) {
      // TWIN boss
      boss.twin = { y: 100, vy: 0 }
    }

    this.state.boss = boss
    this.state.bossActive = true
  }

  private updateBoss(dt: number): void {
    const boss = this.state.boss
    if (!boss) return

    boss.frame++

    // Move to target position (use visible bounds, offset further left for boss visibility)
    const targetX = this.playBounds.rightX - 500
    const currentX = fromFixed(boss.x)
    if (currentX > targetX) {
      boss.x -= toFixed(100 * dt)
    }

    // Vertical movement
    boss.y = toFixed(Math.sin(boss.frame * 0.02) * 80)

    // Type-specific behavior
    this.updateBossBehavior(boss, dt)

    // Shooting
    boss.shootTimer -= dt * 60
    if (boss.shootTimer <= 0) {
      this.bossShoot(boss)
      boss.shootTimer = 90 + this.state.rng.nextInt(60)
    }
  }

  private updateBossBehavior(boss: Boss, dt: number): void {
    switch (boss.type) {
      case 1: // TWIN
        if (boss.twin) {
          boss.twin.vy += (this.state.rng.next() - 0.5) * 200 * dt
          boss.twin.y += boss.twin.vy * dt
          boss.twin.y = Math.max(-200, Math.min(200, boss.twin.y))
          boss.twin.vy *= 0.95
        }
        break

      case 3: // LASER
        if (!boss.charging && boss.shootTimer < 60) {
          boss.charging = true
          boss.chargeTime = 0
        }
        if (boss.charging) {
          boss.chargeTime = (boss.chargeTime || 0) + dt
          if (boss.chargeTime >= 2) {
            this.bossFireLaser(boss)
            boss.charging = false
            boss.chargeTime = 0
          }
        }
        break
    }
  }

  private bossShoot(boss: Boss): void {
    const closestPlayer = this.getClosestPlayer(boss.x, boss.y)
    if (!closestPlayer) return

    const patternIndex = Math.floor(boss.frame / 100) % 4

    switch (boss.type) {
      case 0: // CLASSIC
        if (patternIndex === 0) {
          // Aimed shots
          const angle = Math.atan2(
            fromFixed(closestPlayer.y - boss.y),
            fromFixed(closestPlayer.x - boss.x)
          )
          this.spawnBullet(
            boss.x - toFixed(20),
            boss.y,
            toFixed(Math.cos(angle) * 160),
            toFixed(Math.sin(angle) * 160),
            'aimed',
            0,
            20,
            true,
            ''
          )
        } else if (patternIndex === 1) {
          // Spread
          for (let i = -4; i <= 4; i++) {
            this.spawnBullet(
              boss.x - toFixed(20),
              boss.y,
              toFixed(-100),
              toFixed(i * 30),
              'enemy',
              0,
              18,
              true,
              ''
            )
          }
        } else if (patternIndex === 2) {
          // Circle
          for (let i = 0; i < 12; i++) {
            const angle = (i / 12) * Math.PI * 2
            this.spawnBullet(
              boss.x,
              boss.y,
              toFixed(Math.cos(angle) * 90),
              toFixed(Math.sin(angle) * 90),
              'enemy',
              0,
              18,
              true,
              ''
            )
          }
        } else {
          // Single aimed
          const angle = Math.atan2(
            fromFixed(closestPlayer.y - boss.y),
            fromFixed(closestPlayer.x - boss.x)
          )
          this.spawnBullet(
            boss.x - toFixed(20),
            boss.y,
            toFixed(Math.cos(angle) * 160),
            toFixed(Math.sin(angle) * 160),
            'aimed',
            0,
            20,
            true,
            ''
          )
        }
        break

      case 1: // TWIN
        // Both cores shoot
        {
          const angle1 = Math.atan2(
            fromFixed(closestPlayer.y - boss.y),
            fromFixed(closestPlayer.x - boss.x)
          )
          this.spawnBullet(
            boss.x - toFixed(20),
            boss.y,
            toFixed(Math.cos(angle1) * 150),
            toFixed(Math.sin(angle1) * 150),
            'aimed',
            0,
            20,
            true,
            ''
          )

          if (boss.twin) {
            const angle2 = Math.atan2(
              fromFixed(closestPlayer.y) - boss.twin.y,
              fromFixed(closestPlayer.x - boss.x)
            )
            this.spawnBullet(
              boss.x - toFixed(20),
              toFixed(boss.twin.y),
              toFixed(Math.cos(angle2) * 150),
              toFixed(Math.sin(angle2) * 150),
              'aimed',
              0,
              20,
              true,
              ''
            )
          }
        }
        break

      case 2: // CARRIER
        // Spawn enemies
        if (this.state.enemies.length < 15) {
          const types: EnemyType[] = ['grunt', 'shooter', 'swerver']
          for (let i = 0; i < 4; i++) {
            const type = types[this.state.rng.nextInt(types.length)]!
            this.spawnEnemy(
              type,
              boss.x - toFixed(20),
              boss.y + toFixed((this.state.rng.next() - 0.5) * 60)
            )
          }
        }
        break

      case 4: // WALL
        // Each segment shoots
        if (boss.segments) {
          for (const seg of boss.segments) {
            if (seg.hp > 0) {
              this.spawnBullet(
                boss.x - toFixed(40),
                boss.y + toFixed(seg.y),
                toFixed(-120),
                0,
                'enemy',
                0,
                18,
                true,
                ''
              )
            }
          }
        }
        break

      case 5: // FINAL
        // Multiple attack patterns
        {
          const angle = Math.atan2(
            fromFixed(closestPlayer.y - boss.y),
            fromFixed(closestPlayer.x - boss.x)
          )

          // Aimed shots
          for (let i = -2; i <= 2; i++) {
            this.spawnBullet(
              boss.x - toFixed(60),
              boss.y + toFixed(i * 15),
              toFixed(Math.cos(angle) * 180),
              toFixed(Math.sin(angle) * 180 + i * 20),
              'aimed',
              0,
              25,
              true,
              ''
            )
          }

          // Spiral
          for (let i = 0; i < 12; i++) {
            const spiralAngle = boss.frame * 0.08 + (i / 12) * Math.PI * 2
            this.spawnBullet(
              boss.x,
              boss.y,
              toFixed(Math.cos(spiralAngle) * 70),
              toFixed(Math.sin(spiralAngle) * 70),
              'ring',
              0,
              20,
              true,
              ''
            )
          }
        }
        break
    }
  }

  private bossFireLaser(boss: Boss): void {
    this.state.screenShake = 0.4

    // Create damaging beam effect
    for (let i = 0; i < 50; i++) {
      this.spawnParticle(
        boss.x - toFixed(30 + i * 15),
        boss.y + toFixed((this.state.rng.next() - 0.5) * 20),
        toFixed(-200),
        toFixed((this.state.rng.next() - 0.5) * 50),
        30,
        0, // Red color
        8
      )
    }

    // Damage players in laser path
    for (const player of this.state.players) {
      if (!player.dead && Math.abs(fromFixed(player.y - boss.y)) < 30) {
        this.playerTakeDamage(player, 40)
      }
    }
  }

  private bossDie(boss: Boss): void {
    this.spawnExplosion(boss.x, boss.y, 60)
    this.state.score += Math.floor(boss.points * this.state.multiplier)
    this.state.screenShake = 0.5

    // Drop multiple powerups
    for (let i = 0; i < 6; i++) {
      this.spawnPowerup(
        boss.x + toFixed((this.state.rng.next() - 0.5) * 60),
        boss.y + toFixed((this.state.rng.next() - 0.5) * 60)
      )
    }

    this.state.boss = null
    this.state.bossActive = false
  }

  // ==========================================================================
  // Powerup System
  // ==========================================================================

  private spawnPowerup(x: number, y: number): void {
    // 5% chance for extra life
    let type: PowerupType
    if (this.state.rng.next() < 0.05) {
      type = 'LIFE'
    } else {
      type = POWERUP_TYPES[this.state.rng.nextInt(POWERUP_TYPES.length)]!
    }

    this.state.powerups.push({
      id: this.state.nextId++,
      x,
      y,
      type,
      frame: 0,
    })
  }

  private updatePowerups(dt: number): void {
    const toRemove: number[] = []

    for (const powerup of this.state.powerups) {
      powerup.x -= toFixed(22 * dt)
      powerup.frame++

      // Check if collected
      for (const player of this.state.players) {
        if (player.dead) continue

        const dx = Math.abs(fromFixed(player.x - powerup.x))
        const dy = Math.abs(fromFixed(player.y - powerup.y))

        if (dx < 18 && dy < 18) {
          this.addPlayerPowerup(player, powerup.type)
          this.spawnExplosion(powerup.x, powerup.y, 6)
          toRemove.push(powerup.id)
          break
        }
      }

      // Check bounds
      if (fromFixed(powerup.x) < -WORLD_HALF_WIDTH - 20) {
        toRemove.push(powerup.id)
      }
    }

    this.state.powerups = this.state.powerups.filter(
      (p) => !toRemove.includes(p.id)
    )
  }

  private updateWeaponDrops(dt: number): void {
    const toRemove: number[] = []

    for (const drop of this.state.weaponDrops) {
      // Drift left with scrolling
      drop.x -= toFixed(22 * dt)
      drop.frame++

      // Check if collected by player (auto-pickup if has empty slot)
      for (const player of this.state.players) {
        if (player.dead) continue

        const dx = Math.abs(fromFixed(player.x - drop.x))
        const dy = Math.abs(fromFixed(player.y - drop.y))

        // Pickup radius
        if (dx < 25 && dy < 25) {
          // Auto-pickup if player has empty slots
          if (player.weaponSlots.length < player.maxWeaponSlots) {
            this.pickupWeapon(player, drop)
            this.spawnExplosion(drop.x, drop.y, 6)
            toRemove.push(drop.id)
            break
          }
          // Otherwise, manual pickup via E key (handled in updatePlayer)
        }
      }

      // Despawn if off-screen left
      if (fromFixed(drop.x) < -WORLD_HALF_WIDTH - 30) {
        toRemove.push(drop.id)
      }
    }

    this.state.weaponDrops = this.state.weaponDrops.filter(
      (d) => !toRemove.includes(d.id)
    )
  }

  private pickupWeapon(player: Player, drop: WeaponDrop): void {
    const stats = WEAPON_STATS[drop.weaponType]

    // Check if player already has this weapon type
    const existingIndex = player.weaponSlots.findIndex(w => w.type === drop.weaponType)

    if (existingIndex >= 0) {
      // Add ammo to existing weapon
      player.weaponSlots[existingIndex]!.ammo = Math.min(
        player.weaponSlots[existingIndex]!.ammo + drop.ammo,
        player.weaponSlots[existingIndex]!.maxAmmo
      )
    } else if (player.weaponSlots.length < player.maxWeaponSlots) {
      // Add new weapon to empty slot
      player.weaponSlots.push({
        type: drop.weaponType,
        ammo: drop.ammo,
        maxAmmo: stats.maxAmmo,
        cooldown: 0,
      })
    }
  }

  private tryManualPickup(player: Player): WeaponDrop | null {
    // Find nearest weapon drop within pickup range
    let nearestDrop: WeaponDrop | null = null
    let nearestDist = Infinity

    for (const drop of this.state.weaponDrops) {
      const dx = Math.abs(fromFixed(player.x - drop.x))
      const dy = Math.abs(fromFixed(player.y - drop.y))

      if (dx < 35 && dy < 35) {
        const dist = dx + dy
        if (dist < nearestDist) {
          nearestDist = dist
          nearestDrop = drop
        }
      }
    }

    if (!nearestDrop) return null

    const stats = WEAPON_STATS[nearestDrop.weaponType]

    // Check if player already has this weapon type
    const existingIndex = player.weaponSlots.findIndex(w => w.type === nearestDrop!.weaponType)

    if (existingIndex >= 0) {
      // Add ammo to existing weapon
      player.weaponSlots[existingIndex]!.ammo = Math.min(
        player.weaponSlots[existingIndex]!.ammo + nearestDrop.ammo,
        player.weaponSlots[existingIndex]!.maxAmmo
      )
    } else if (player.weaponSlots.length < player.maxWeaponSlots) {
      // Add new weapon to empty slot
      player.weaponSlots.push({
        type: nearestDrop.weaponType,
        ammo: nearestDrop.ammo,
        maxAmmo: stats.maxAmmo,
        cooldown: 0,
      })
    } else {
      // Replace current weapon - drop the old one first
      const currentWeapon = player.weaponSlots[player.activeWeaponIndex]
      if (currentWeapon && currentWeapon.ammo > 0) {
        // Spawn old weapon as a drop
        this.spawnWeaponDrop(player.x, player.y, currentWeapon.type)
        // Update the dropped weapon's ammo to match what player had
        const droppedWeapon = this.state.weaponDrops[this.state.weaponDrops.length - 1]
        if (droppedWeapon) {
          droppedWeapon.ammo = currentWeapon.ammo
        }
      }

      // Replace with new weapon
      player.weaponSlots[player.activeWeaponIndex] = {
        type: nearestDrop.weaponType,
        ammo: nearestDrop.ammo,
        maxAmmo: stats.maxAmmo,
        cooldown: 0,
      }
    }

    this.spawnExplosion(nearestDrop.x, nearestDrop.y, 6)
    return nearestDrop
  }

  private cycleWeapon(player: Player): void {
    if (player.weaponSlots.length > 1) {
      player.activeWeaponIndex = (player.activeWeaponIndex + 1) % player.weaponSlots.length
    }
  }

  // ==========================================================================
  // Particle System
  // ==========================================================================

  private spawnParticle(
    x: number,
    y: number,
    vx: number,
    vy: number,
    life: number,
    colorIndex: number,
    size: number
  ): void {
    this.state.particles.push({
      id: this.state.nextId++,
      x,
      y,
      vx,
      vy,
      life,
      colorIndex,
      size,
    })
  }

  private spawnExplosion(x: number, y: number, count: number): void {
    for (let i = 0; i < count; i++) {
      const angle = (i / count) * Math.PI * 2
      const speed = 40 + this.state.rng.next() * 140
      this.spawnParticle(
        x,
        y,
        toFixed(Math.cos(angle) * speed),
        toFixed(Math.sin(angle) * speed),
        21 + this.state.rng.nextInt(21), // 0.35-0.7 seconds
        this.state.rng.nextInt(5), // Random explosion color
        2 + this.state.rng.next() * 4
      )
    }
  }

  private updateParticles(dt: number): void {
    for (const particle of this.state.particles) {
      particle.x += Math.round(particle.vx * dt)
      particle.y += Math.round(particle.vy * dt)
      particle.life--
      particle.size *= 0.94
    }

    this.state.particles = this.state.particles.filter((p) => p.life > 0)
  }

  // ==========================================================================
  // Wave Spawning
  // ==========================================================================

  private updateWaveSpawning(dt: number): void {
    this.state.waveTimer += dt

    // Don't spawn during boss fight
    if (this.state.bossActive) return

    // Spawn wave when timer reaches threshold and few enemies remain
    if (this.state.waveTimer > 6 && this.state.enemies.length < 3) {
      this.state.waveTimer = 0
      this.state.wave++
      this.spawnWave()
    }

    // Initial wave spawn
    if (
      this.state.wave === 1 &&
      this.state.enemies.length === 0 &&
      this.state.waveTimer > 1.2
    ) {
      this.spawnWave()
    }
  }

  private getAvailableEnemies(): EnemyType[] {
    const all: EnemyType[] = ['grunt']
    if (this.state.wave >= 2) all.push('swerver')
    if (this.state.wave >= 3) all.push('shooter', 'speeder')
    if (this.state.wave >= 4) all.push('mine')
    if (this.state.wave >= 5) all.push('bomber', 'spiral')
    if (this.state.wave >= 7) all.push('tank', 'sniper')
    if (this.state.wave >= 9) all.push('carrier', 'shield')
    if (this.state.wave >= 11) all.push('splitter')
    return all
  }

  private spawnWave(): void {
    const available = this.getAvailableEnemies()
    const patterns = ['line', 'v', 'swarm', 'mixed', 'rush', 'surround']
    const pattern = patterns[this.state.rng.nextInt(patterns.length)]
    const count = 4 + Math.floor(this.state.wave * 0.8)

    // Use world space for spawning (larger than visible area)
    const halfW = WORLD_HALF_WIDTH
    const halfH = WORLD_HALF_HEIGHT

    // Spawn offset - far enough off-screen to smoothly enter (accounting for 2.5D camera tilt)
    const spawnOffset = 400

    switch (pattern) {
      case 'line':
        for (let i = 0; i < count; i++) {
          const type =
            available[
              this.state.rng.nextInt(Math.min(available.length, 3))
            ]!
          this.spawnEnemy(
            type,
            toFixed(halfW + spawnOffset + i * 30),
            toFixed(-halfH * 0.5 + this.state.rng.next() * halfH)
          )
        }
        break

      case 'v':
        for (let i = 0; i < 7; i++) {
          const yOff = Math.abs(i - 3) * 18
          this.spawnEnemy(
            'grunt',
            toFixed(halfW + spawnOffset + i * 20),
            toFixed(yOff * (i < 3 ? -1 : 1))
          )
        }
        break

      case 'swarm':
        for (let i = 0; i < count; i++) {
          const type = available[this.state.rng.nextInt(available.length)]!
          this.spawnEnemy(
            type,
            toFixed(halfW + spawnOffset + i * 25),
            toFixed((this.state.rng.next() - 0.5) * halfH * 1.6)
          )
        }
        break

      case 'mixed':
        this.spawnEnemy('shooter', toFixed(halfW + spawnOffset), toFixed(-halfH * 0.5))
        this.spawnEnemy('shooter', toFixed(halfW + spawnOffset), toFixed(halfH * 0.5))
        for (let i = 0; i < 4; i++) {
          this.spawnEnemy(
            'grunt',
            toFixed(halfW + spawnOffset + 30 + i * 35),
            toFixed((this.state.rng.next() - 0.5) * 40)
          )
        }
        break

      case 'rush':
        for (let i = 0; i < count + 3; i++) {
          this.spawnEnemy(
            'speeder',
            toFixed(halfW + spawnOffset + i * 40),
            toFixed((this.state.rng.next() - 0.5) * halfH * 1.6)
          )
        }
        break

      case 'surround':
        for (let i = 0; i < 6; i++) {
          const type = available[this.state.rng.nextInt(available.length)]!
          this.spawnEnemy(type, toFixed(halfW + spawnOffset), toFixed((i - 2.5) * 80))
        }
        break
    }

    // Special spawns every 3 waves after wave 6
    if (this.state.wave % 3 === 0 && this.state.wave >= 6) {
      const heavies: EnemyType[] = available.filter((t) =>
        ['tank', 'carrier', 'shield'].includes(t)
      )
      if (heavies.length > 0) {
        const type = heavies[this.state.rng.nextInt(heavies.length)]!
        this.spawnEnemy(type, toFixed(halfW + spawnOffset + 50), toFixed(0))
      }
    }

    // Boss every 5 waves
    if (this.state.wave % 5 === 0 && !this.state.bossActive) {
      const bossType = Math.min(5, Math.floor(this.state.wave / 5) - 1) as BossType
      this.spawnBoss(bossType)
    }
  }

  // ==========================================================================
  // Collision Detection
  // ==========================================================================

  private checkCollisions(): void {
    const visibleRightX = this.playBounds.rightX  // Enemies are invincible until on-screen

    // Player bullets vs enemies
    for (const bullet of this.state.bullets) {
      if (bullet.isEnemy) continue

      // Check enemies
      for (const enemy of this.state.enemies) {
        if (bullet.hitEntities.has(enemy.id)) continue

        // Enemies are invincible when off-screen to the right
        const enemyX = fromFixed(enemy.x)
        if (enemyX > visibleRightX) continue

        if (this.bulletHitsEnemy(bullet, enemy)) {
          bullet.hitEntities.add(enemy.id)

          // Handle shield
          if (enemy.hasShield && enemy.shieldHealth && enemy.shieldHealth > 0) {
            enemy.shieldHealth -= bullet.damage
            if (enemy.shieldHealth <= 0) {
              enemy.hasShield = false
            }
          } else {
            enemy.health -= bullet.damage
          }

          if (bullet.pierce <= 0) {
            bullet.lifetime = 0
          } else {
            bullet.pierce--
          }

          if (enemy.health <= 0) {
            this.enemyDie(enemy)
            enemy.health = 0 // Mark for removal
          } else {
            this.spawnExplosion(bullet.x, bullet.y, 2)
          }

          break
        }
      }

      // Check boss
      if (this.state.boss && !bullet.hitEntities.has(this.state.boss.id)) {
        if (this.bulletHitsBoss(bullet, this.state.boss)) {
          bullet.hitEntities.add(this.state.boss.id)
          this.state.boss.health -= bullet.damage

          if (bullet.pierce <= 0) {
            bullet.lifetime = 0
          } else {
            bullet.pierce--
          }

          if (this.state.boss.health <= 0) {
            this.bossDie(this.state.boss)
          } else {
            this.spawnExplosion(bullet.x, bullet.y, 2)
          }
        }
      }
    }

    // Beams vs enemies/boss
    for (const beam of this.state.beams) {
      for (const enemy of this.state.enemies) {
        if (beam.hitEntities.has(enemy.id)) continue

        const ex = fromFixed(enemy.x)
        const ey = fromFixed(enemy.y)
        const bx = fromFixed(beam.x)
        const by = fromFixed(beam.y)

        // Enemies are invincible when off-screen to the right
        if (ex > visibleRightX) continue

        // Beam hits if enemy is to the right of beam origin and within height
        if (ex > bx && Math.abs(ey - by) < 25) {
          beam.hitEntities.add(enemy.id)
          enemy.health -= beam.power * 5

          if (enemy.health <= 0) {
            this.enemyDie(enemy)
            enemy.health = 0
          }
        }
      }

      if (this.state.boss && !beam.hitEntities.has(this.state.boss.id)) {
        const bossX = fromFixed(this.state.boss.x)
        const bossY = fromFixed(this.state.boss.y)
        const bx = fromFixed(beam.x)
        const by = fromFixed(beam.y)

        if (bossX > bx && Math.abs(bossY - by) < 40) {
          beam.hitEntities.add(this.state.boss.id)
          this.state.boss.health -= beam.power * 10

          if (this.state.boss.health <= 0) {
            this.bossDie(this.state.boss)
          }
        }
      }
    }

    // Missiles vs enemies/boss
    for (const missile of this.state.missiles) {
      const mx = fromFixed(missile.x)
      const my = fromFixed(missile.y)

      for (const enemy of this.state.enemies) {
        const ex = fromFixed(enemy.x)
        const ey = fromFixed(enemy.y)

        // Enemies are invincible when off-screen to the right
        if (ex > visibleRightX) continue

        if (Math.hypot(ex - mx, ey - my) < 25) {
          enemy.health -= missile.damage
          this.spawnExplosion(missile.x, missile.y, 8)
          missile.lifetime = 0

          if (enemy.health <= 0) {
            this.enemyDie(enemy)
            enemy.health = 0
          }
          break
        }
      }

      if (this.state.boss && missile.lifetime > 0) {
        const bossX = fromFixed(this.state.boss.x)
        const bossY = fromFixed(this.state.boss.y)

        if (Math.hypot(bossX - mx, bossY - my) < 50) {
          this.state.boss.health -= missile.damage
          this.spawnExplosion(missile.x, missile.y, 8)
          missile.lifetime = 0

          if (this.state.boss.health <= 0) {
            this.bossDie(this.state.boss)
          }
        }
      }
    }

    // Player orbs vs enemies/bullets
    for (const player of this.state.players) {
      if (player.dead) continue

      for (const orb of player.orbs) {
        const ox = fromFixed(player.x) + Math.cos(orb.angle) * orb.radius
        const oy = fromFixed(player.y) + Math.sin(orb.angle) * orb.radius

        // Orbs vs enemies
        for (const enemy of this.state.enemies) {
          const ex = fromFixed(enemy.x)
          const ey = fromFixed(enemy.y)

          // Enemies are invincible when off-screen to the right
          if (ex > visibleRightX) continue

          if (Math.hypot(ex - ox, ey - oy) < 25) {
            enemy.health -= 2
            this.spawnExplosion(toFixed(ox), toFixed(oy), 4)

            if (enemy.health <= 0) {
              this.enemyDie(enemy)
              enemy.health = 0
            }
          }
        }

        // Orbs vs enemy bullets
        for (const bullet of this.state.bullets) {
          if (!bullet.isEnemy) continue

          const bx = fromFixed(bullet.x)
          const by = fromFixed(bullet.y)

          if (Math.hypot(bx - ox, by - oy) < 8) {
            this.spawnExplosion(bullet.x, bullet.y, 2)
            bullet.lifetime = 0
          }
        }
      }
    }

    // Enemy bullets vs players
    for (const bullet of this.state.bullets) {
      if (!bullet.isEnemy) continue

      for (const player of this.state.players) {
        if (player.dead || player.invincible > 0) continue

        const px = fromFixed(player.x)
        const py = fromFixed(player.y)
        const bx = fromFixed(bullet.x)
        const by = fromFixed(bullet.y)

        if (Math.abs(bx - px) < 10 && Math.abs(by - py) < 8) {
          this.playerTakeDamage(player, bullet.damage)
          bullet.lifetime = 0
          break
        }
      }
    }

    // Enemies vs players (collision)
    for (const enemy of this.state.enemies) {
      const ex = fromFixed(enemy.x)
      const ey = fromFixed(enemy.y)

      for (const player of this.state.players) {
        if (player.dead || player.invincible > 0) continue

        const px = fromFixed(player.x)
        const py = fromFixed(player.y)

        if (Math.abs(ex - px) < 25 && Math.abs(ey - py) < 20) {
          this.playerTakeDamage(player, 25)
          break
        }
      }
    }

    // Remove dead enemies
    this.state.enemies = this.state.enemies.filter((e) => e.health > 0)

    // Remove dead bullets
    this.state.bullets = this.state.bullets.filter((b) => b.lifetime > 0)

    // Remove dead missiles
    this.state.missiles = this.state.missiles.filter((m) => m.lifetime > 0)
  }

  private bulletHitsEnemy(bullet: Bullet, enemy: Enemy): boolean {
    const bx = fromFixed(bullet.x)
    const by = fromFixed(bullet.y)
    const ex = fromFixed(enemy.x)
    const ey = fromFixed(enemy.y)

    // Different hitbox sizes per enemy type
    const size =
      enemy.type === 'tank'
        ? 30
        : enemy.type === 'carrier'
          ? 35
          : enemy.type === 'mine'
            ? 15
            : 20

    return Math.abs(bx - ex) < size && Math.abs(by - ey) < size
  }

  private bulletHitsBoss(bullet: Bullet, boss: Boss): boolean {
    const bx = fromFixed(bullet.x)
    const by = fromFixed(bullet.y)
    const bossX = fromFixed(boss.x)
    const bossY = fromFixed(boss.y)

    // Boss hitbox size varies by type
    const size = boss.type === 4 ? 55 : boss.type === 5 ? 50 : 40

    return Math.abs(bx - bossX) < size && Math.abs(by - bossY) < size
  }

  // ==========================================================================
  // Utility Functions
  // ==========================================================================

  private getClosestPlayer(x: number, y: number): Player | null {
    let closest: Player | null = null
    let minDist = Infinity

    for (const player of this.state.players) {
      if (player.dead) continue

      const dist = Math.hypot(
        fromFixed(player.x - x),
        fromFixed(player.y - y)
      )

      if (dist < minDist) {
        minDist = dist
        closest = player
      }
    }

    return closest
  }

  private checkGameOver(): void {
    const allDead = this.state.players.every(
      (p) => p.dead && p.lives <= 0
    )

    if (allDead) {
      this.state.gameOver = true
    }
  }

  // ==========================================================================
  // State Access
  // ==========================================================================

  getState(): {
    frame: number
    players: Array<{
      id: number
      playerId: string
      x: number
      y: number
      vx: number
      vy: number
      shields: number
      maxShields: number
      shipLevel: number
      lives: number
      dead: boolean
      invincible: number
      charging: boolean
      chargeTime: number
      powerups: Player['powerups']
      orbs: Orb[]
      drones: Array<{ x: number; y: number }>
      weaponSlots: PlayerWeapon[]
      activeWeaponIndex: number
      maxWeaponSlots: number
    }>
    bullets: Array<{
      id: number
      x: number
      y: number
      type: BulletType
      isEnemy: boolean
    }>
    beams: Array<{
      id: number
      x: number
      y: number
      width: number
      power: number
    }>
    missiles: Array<{
      id: number
      x: number
      y: number
      vx: number
      vy: number
    }>
    enemies: Array<{
      id: number
      type: EnemyType
      x: number
      y: number
      health: number
      maxHealth: number
      hasShield: boolean
      equippedWeapon?: WeaponType
    }>
    boss: {
      id: number
      type: BossType
      x: number
      y: number
      health: number
      maxHealth: number
      charging: boolean
      chargeTime: number
      twin?: { y: number }
      segments?: Array<{ y: number; hp: number }>
    } | null
    powerups: Array<{
      id: number
      x: number
      y: number
      type: PowerupType
      frame: number
    }>
    weaponDrops: Array<{
      id: number
      x: number
      y: number
      weaponType: WeaponType
      ammo: number
      frame: number
    }>
    particles: Array<{
      id: number
      x: number
      y: number
      colorIndex: number
      size: number
    }>
    score: number
    multiplier: number
    wave: number
    screenShake: number
    bossActive: boolean
    gameOver: boolean
  } {
    return {
      frame: this.state.frame,
      players: this.state.players.map((p) => ({
        id: p.id,
        playerId: p.playerId,
        x: fromFixed(p.x),
        y: fromFixed(p.y),
        vx: fromFixed(p.vx),
        vy: fromFixed(p.vy),
        shields: p.shields,
        maxShields: p.maxShields,
        shipLevel: p.shipLevel,
        lives: p.lives,
        dead: p.dead,
        invincible: p.invincible,
        charging: p.charging,
        chargeTime: p.chargeTime,
        powerups: { ...p.powerups },
        orbs: p.orbs.map((o) => ({ ...o })),
        drones: p.drones.map((d) => ({ x: d.x, y: d.y })),
        weaponSlots: p.weaponSlots.map((w) => ({ ...w })),
        activeWeaponIndex: p.activeWeaponIndex,
        maxWeaponSlots: p.maxWeaponSlots,
      })),
      bullets: this.state.bullets.map((b) => ({
        id: b.id,
        x: fromFixed(b.x),
        y: fromFixed(b.y),
        type: b.type,
        isEnemy: b.isEnemy,
      })),
      beams: this.state.beams.map((b) => ({
        id: b.id,
        x: fromFixed(b.x),
        y: fromFixed(b.y),
        width: fromFixed(b.width),
        power: b.power,
      })),
      missiles: this.state.missiles.map((m) => ({
        id: m.id,
        x: fromFixed(m.x),
        y: fromFixed(m.y),
        vx: fromFixed(m.vx),
        vy: fromFixed(m.vy),
      })),
      enemies: this.state.enemies.map((e) => ({
        id: e.id,
        type: e.type,
        x: fromFixed(e.x),
        y: fromFixed(e.y),
        health: e.health,
        maxHealth: e.maxHealth,
        hasShield: e.hasShield ?? false,
        equippedWeapon: e.equippedWeapon,
      })),
      boss: this.state.boss
        ? {
            id: this.state.boss.id,
            type: this.state.boss.type,
            x: fromFixed(this.state.boss.x),
            y: fromFixed(this.state.boss.y),
            health: this.state.boss.health,
            maxHealth: this.state.boss.maxHealth,
            charging: this.state.boss.charging ?? false,
            chargeTime: this.state.boss.chargeTime ?? 0,
            twin: this.state.boss.twin
              ? { y: this.state.boss.twin.y }
              : undefined,
            segments: this.state.boss.segments,
          }
        : null,
      powerups: this.state.powerups.map((p) => ({
        id: p.id,
        x: fromFixed(p.x),
        y: fromFixed(p.y),
        type: p.type,
        frame: p.frame,
      })),
      weaponDrops: this.state.weaponDrops.map((w) => ({
        id: w.id,
        x: fromFixed(w.x),
        y: fromFixed(w.y),
        weaponType: w.weaponType,
        ammo: w.ammo,
        frame: w.frame,
      })),
      particles: this.state.particles.map((p) => ({
        id: p.id,
        x: fromFixed(p.x),
        y: fromFixed(p.y),
        colorIndex: p.colorIndex,
        size: p.size,
      })),
      score: this.state.score,
      multiplier: this.state.multiplier,
      wave: this.state.wave,
      screenShake: this.state.screenShake,
      bossActive: this.state.bossActive,
      gameOver: this.state.gameOver,
    }
  }

  getChecksum(): number {
    let hash = this.state.frame
    for (const player of this.state.players) {
      hash ^= player.id
      hash ^= player.x
      hash ^= player.y
      hash ^= player.shields
      hash = (hash * 31) >>> 0
    }
    for (const enemy of this.state.enemies) {
      hash ^= enemy.id
      hash ^= enemy.x
      hash ^= enemy.y
      hash ^= enemy.health
      hash = (hash * 31) >>> 0
    }
    return hash
  }

  getFrame(): number {
    return this.state.frame
  }

  getPlayerIds(): string[] {
    return this.state.players.map((p) => p.playerId)
  }
}
