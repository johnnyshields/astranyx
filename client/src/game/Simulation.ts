/**
 * Deterministic Game Simulation
 *
 * CRITICAL: This simulation must be 100% deterministic.
 * Given the same inputs, it must produce the same output on all clients.
 *
 * Rules for determinism:
 * - No Math.random() - use seeded PRNG
 * - No Date.now() - use frame counter
 * - Fixed-point or careful float handling
 * - Same iteration order (use arrays, not objects/maps for entities)
 * - No async operations
 */

import type { PlayerInput } from '../network/LockstepNetcode.ts'

// Fixed-point math helpers (16.16 format)
const FP_SHIFT = 16
const FP_ONE = 1 << FP_SHIFT

function toFixed(n: number): number {
  return Math.round(n * FP_ONE)
}

function fromFixed(n: number): number {
  return n / FP_ONE
}

function mulFixed(a: number, b: number): number {
  return Math.round((a * b) / FP_ONE)
}

// Seeded PRNG (xorshift32)
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
}

// Entity types
export interface Entity {
  id: number
  type: 'player' | 'enemy' | 'bullet' | 'powerup'
  x: number  // Fixed-point
  y: number  // Fixed-point
  vx: number // Fixed-point
  vy: number // Fixed-point
  rotation: number
  health: number
  playerId?: string
  subtype?: string
  lifetime?: number
}

export interface SimulationState {
  frame: number
  entities: Entity[]
  nextEntityId: number
  rng: SeededRandom
  score: number[]  // Per-player scores
}

// Game constants (all in fixed-point)
const PLAYER_ACCEL = toFixed(2000)
const PLAYER_MAX_SPEED = toFixed(400)
const PLAYER_FRICTION = toFixed(0.92)
const PLAYER_FIRE_RATE = 6  // frames between shots
const BULLET_SPEED = toFixed(600)

const PLAY_AREA_WIDTH = toFixed(1000)
const PLAY_AREA_HEIGHT = toFixed(600)

// Player spawn positions
const SPAWN_POSITIONS = [
  { x: toFixed(-200), y: toFixed(50) },
  { x: toFixed(-200), y: toFixed(-50) },
  { x: toFixed(-250), y: toFixed(100) },
  { x: toFixed(-250), y: toFixed(-100) },
]

export class Simulation {
  private state: SimulationState
  private playerIds: string[]
  private playerFireTimers: Map<string, number> = new Map()

  constructor(playerIds: string[], seed: number = 12345) {
    this.playerIds = playerIds

    this.state = {
      frame: 0,
      entities: [],
      nextEntityId: 1,
      rng: new SeededRandom(seed),
      score: playerIds.map(() => 0),
    }

    // Spawn players
    playerIds.forEach((playerId, index) => {
      const spawn = SPAWN_POSITIONS[index % SPAWN_POSITIONS.length]!
      this.state.entities.push({
        id: this.state.nextEntityId++,
        type: 'player',
        x: spawn.x,
        y: spawn.y,
        vx: 0,
        vy: 0,
        rotation: 0,
        health: 100,
        playerId,
      })
      this.playerFireTimers.set(playerId, 0)
    })
  }

  /**
   * Advance simulation by one frame with given inputs
   * This is the core deterministic update
   */
  tick(inputs: Map<string, PlayerInput>): void {
    this.state.frame++

    // Update players
    for (const entity of this.state.entities) {
      if (entity.type === 'player' && entity.playerId) {
        const input = inputs.get(entity.playerId)
        if (input) {
          this.updatePlayer(entity, input)
        }
      }
    }

    // Update all other entities
    for (const entity of this.state.entities) {
      if (entity.type !== 'player') {
        this.updateEntity(entity)
      }
    }

    // Check collisions
    this.checkCollisions()

    // Remove dead entities
    this.state.entities = this.state.entities.filter(
      (e) => e.health > 0 && (e.lifetime === undefined || e.lifetime > 0)
    )

    // Spawn enemies (deterministic based on frame)
    this.maybeSpawnEnemies()
  }

  private updatePlayer(entity: Entity, input: PlayerInput): void {
    // Movement
    let ax = 0
    let ay = 0

    if (input.left && !input.right) ax = -PLAYER_ACCEL
    if (input.right && !input.left) ax = PLAYER_ACCEL
    if (input.up && !input.down) ay = PLAYER_ACCEL
    if (input.down && !input.up) ay = -PLAYER_ACCEL

    // Update velocity (fixed-point)
    entity.vx = mulFixed(entity.vx + ax, PLAYER_FRICTION)
    entity.vy = mulFixed(entity.vy + ay, PLAYER_FRICTION)

    // Clamp speed
    const speed = Math.sqrt(
      fromFixed(entity.vx) ** 2 + fromFixed(entity.vy) ** 2
    )
    const maxSpeed = fromFixed(PLAYER_MAX_SPEED)

    if (speed > maxSpeed) {
      const ratio = maxSpeed / speed
      entity.vx = toFixed(fromFixed(entity.vx) * ratio)
      entity.vy = toFixed(fromFixed(entity.vy) * ratio)
    }

    // Update position
    entity.x += entity.vx
    entity.y += entity.vy

    // Clamp to play area
    const halfWidth = PLAY_AREA_WIDTH / 2
    const halfHeight = PLAY_AREA_HEIGHT / 2
    entity.x = Math.max(-halfWidth + toFixed(30), Math.min(halfWidth - toFixed(30), entity.x))
    entity.y = Math.max(-halfHeight + toFixed(20), Math.min(halfHeight - toFixed(20), entity.y))

    // Visual rotation based on vertical velocity
    entity.rotation = -fromFixed(entity.vy) * 0.002
    entity.rotation = Math.max(-0.4, Math.min(0.4, entity.rotation))

    // Firing
    const fireTimer = this.playerFireTimers.get(entity.playerId!) ?? 0

    if (fireTimer > 0) {
      this.playerFireTimers.set(entity.playerId!, fireTimer - 1)
    }

    if (input.fire && fireTimer <= 0) {
      this.spawnBullet(entity)
      this.playerFireTimers.set(entity.playerId!, PLAYER_FIRE_RATE)
    }
  }

  private spawnBullet(player: Entity): void {
    this.state.entities.push({
      id: this.state.nextEntityId++,
      type: 'bullet',
      x: player.x + toFixed(30),
      y: player.y,
      vx: BULLET_SPEED,
      vy: 0,
      rotation: 0,
      health: 1,
      playerId: player.playerId,
      lifetime: 120,  // 2 seconds at 60fps
    })
  }

  private updateEntity(entity: Entity): void {
    // Update position
    entity.x += entity.vx
    entity.y += entity.vy

    // Decrement lifetime
    if (entity.lifetime !== undefined) {
      entity.lifetime--
    }

    // Remove if out of bounds
    const margin = toFixed(100)
    if (
      entity.x < -PLAY_AREA_WIDTH / 2 - margin ||
      entity.x > PLAY_AREA_WIDTH / 2 + margin ||
      entity.y < -PLAY_AREA_HEIGHT / 2 - margin ||
      entity.y > PLAY_AREA_HEIGHT / 2 + margin
    ) {
      entity.health = 0
    }

    // Enemy movement (simple sine wave)
    if (entity.type === 'enemy') {
      entity.vy = toFixed(Math.sin(this.state.frame * 0.05 + entity.id) * 100)
    }
  }

  private checkCollisions(): void {
    const bullets = this.state.entities.filter((e) => e.type === 'bullet' && e.playerId)
    const enemies = this.state.entities.filter((e) => e.type === 'enemy')
    const players = this.state.entities.filter((e) => e.type === 'player')

    // Bullet vs Enemy
    for (const bullet of bullets) {
      for (const enemy of enemies) {
        if (this.entitiesCollide(bullet, enemy, toFixed(20))) {
          bullet.health = 0
          enemy.health -= 25

          if (enemy.health <= 0) {
            // Award score to the player who shot
            const playerIndex = this.playerIds.indexOf(bullet.playerId!)
            if (playerIndex >= 0) {
              this.state.score[playerIndex] = (this.state.score[playerIndex] ?? 0) + 100
            }
          }
        }
      }
    }

    // Enemy vs Player
    for (const enemy of enemies) {
      for (const player of players) {
        if (this.entitiesCollide(enemy, player, toFixed(25))) {
          player.health -= 20
          enemy.health = 0
        }
      }
    }
  }

  private entitiesCollide(a: Entity, b: Entity, radius: number): boolean {
    const dx = a.x - b.x
    const dy = a.y - b.y
    const distSq = mulFixed(dx, dx) + mulFixed(dy, dy)
    const radiusSq = mulFixed(radius, radius)
    return distSq < radiusSq
  }

  private maybeSpawnEnemies(): void {
    // Spawn enemies every 60 frames (1 second)
    if (this.state.frame % 60 === 0 && this.state.frame > 0) {
      const y = toFixed(this.state.rng.nextRange(-250, 250))

      this.state.entities.push({
        id: this.state.nextEntityId++,
        type: 'enemy',
        x: PLAY_AREA_WIDTH / 2 + toFixed(50),
        y,
        vx: toFixed(-100 - this.state.rng.next() * 50),
        vy: 0,
        rotation: Math.PI,
        health: 50,
      })
    }
  }

  // State access (convert from fixed-point for rendering)
  getState(): {
    frame: number
    entities: Array<{
      id: number
      type: string
      x: number
      y: number
      vx: number
      vy: number
      rotation: number
      health: number
      playerId?: string
    }>
    score: number[]
  } {
    return {
      frame: this.state.frame,
      entities: this.state.entities.map((e) => ({
        id: e.id,
        type: e.type,
        x: fromFixed(e.x),
        y: fromFixed(e.y),
        vx: fromFixed(e.vx),
        vy: fromFixed(e.vy),
        rotation: e.rotation,
        health: e.health,
        playerId: e.playerId,
      })),
      score: [...this.state.score],
    }
  }

  /**
   * Generate checksum for desync detection
   */
  getChecksum(): number {
    let hash = this.state.frame
    for (const entity of this.state.entities) {
      hash ^= entity.id
      hash ^= entity.x
      hash ^= entity.y
      hash ^= entity.health
      hash = (hash * 31) >>> 0
    }
    return hash
  }

  getFrame(): number {
    return this.state.frame
  }

  getPlayerIds(): string[] {
    return this.playerIds
  }
}
