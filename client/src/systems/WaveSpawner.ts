import { SeededRandom } from '../math/SeededRandom.ts'

/**
 * Enemy types available in the game
 */
export type EnemyType =
  | 'grunt'
  | 'swerver'
  | 'shooter'
  | 'speeder'
  | 'mine'
  | 'bomber'
  | 'spiral'
  | 'tank'
  | 'sniper'
  | 'carrier'
  | 'shield'
  | 'splitter'
  | 'turret'
  | 'interceptor'
  | 'fighter'
  | 'scout'

/**
 * Boss types (0-5)
 */
export type BossType = 0 | 1 | 2 | 3 | 4 | 5

/**
 * Spawn pattern types
 */
export type SpawnPattern = 'line' | 'v' | 'swarm' | 'mixed' | 'rush' | 'surround'

/**
 * Spawn request for an enemy
 */
export interface EnemySpawn {
  type: EnemyType
  x: number
  y: number
}

/**
 * Spawn request for a boss
 */
export interface BossSpawn {
  type: BossType
  x: number
  y: number
}

/**
 * Result of a wave spawn
 */
export interface WaveSpawnResult {
  enemies: EnemySpawn[]
  boss?: BossSpawn
}

/**
 * Configuration for wave spawning
 */
export interface WaveConfig {
  worldHalfWidth: number
  worldHalfHeight: number
  spawnOffset: number
  waveInterval: number
  initialDelay: number
  minEnemiesForNextWave: number
  bossEveryWaves: number
}

const DEFAULT_CONFIG: WaveConfig = {
  worldHalfWidth: 1000,
  worldHalfHeight: 400,
  spawnOffset: 400,
  waveInterval: 6,
  initialDelay: 1.2,
  minEnemiesForNextWave: 3,
  bossEveryWaves: 5,
}

/**
 * Wave spawning system
 * Determines enemy unlocks, patterns, and spawn positions
 */
export class WaveSpawner {
  private config: WaveConfig

  constructor(config: Partial<WaveConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config }
  }

  /**
   * Get available enemy types for a given wave
   */
  getAvailableEnemies(wave: number): EnemyType[] {
    const enemies: EnemyType[] = ['grunt']

    if (wave >= 2) enemies.push('swerver')
    if (wave >= 3) enemies.push('shooter', 'speeder')
    if (wave >= 4) enemies.push('mine')
    if (wave >= 5) enemies.push('bomber', 'spiral')
    if (wave >= 7) enemies.push('tank', 'sniper')
    if (wave >= 9) enemies.push('carrier', 'shield')
    if (wave >= 11) enemies.push('splitter')

    return enemies
  }

  /**
   * Get available heavy enemy types for a wave
   */
  getHeavyEnemies(wave: number): EnemyType[] {
    return this.getAvailableEnemies(wave).filter(t =>
      ['tank', 'carrier', 'shield'].includes(t)
    )
  }

  /**
   * Check if a wave should spawn a boss
   */
  shouldSpawnBoss(wave: number): boolean {
    return wave > 0 && wave % this.config.bossEveryWaves === 0
  }

  /**
   * Get boss type for a wave
   */
  getBossType(wave: number): BossType {
    const bossNumber = Math.floor(wave / this.config.bossEveryWaves) - 1
    return Math.min(5, bossNumber) as BossType
  }

  /**
   * Check if wave should have special heavy spawn
   */
  shouldSpawnHeavy(wave: number): boolean {
    return wave >= 6 && wave % 3 === 0
  }

  /**
   * Calculate enemy count for a wave
   */
  getEnemyCount(wave: number): number {
    return 4 + Math.floor(wave * 0.8)
  }

  /**
   * Get spawn patterns available
   */
  getPatterns(): SpawnPattern[] {
    return ['line', 'v', 'swarm', 'mixed', 'rush', 'surround']
  }

  /**
   * Generate spawns for a pattern
   */
  generatePatternSpawns(
    pattern: SpawnPattern,
    wave: number,
    rng: SeededRandom
  ): EnemySpawn[] {
    const spawns: EnemySpawn[] = []
    const available = this.getAvailableEnemies(wave)
    const count = this.getEnemyCount(wave)
    const { worldHalfWidth: halfW, worldHalfHeight: halfH, spawnOffset } = this.config

    switch (pattern) {
      case 'line':
        for (let i = 0; i < count; i++) {
          const typeIndex = rng.nextInt(Math.min(available.length, 3))
          spawns.push({
            type: available[typeIndex]!,
            x: halfW + spawnOffset + i * 30,
            y: -halfH * 0.5 + rng.next() * halfH,
          })
        }
        break

      case 'v':
        for (let i = 0; i < 7; i++) {
          const yOff = Math.abs(i - 3) * 18
          spawns.push({
            type: 'grunt',
            x: halfW + spawnOffset + i * 20,
            y: yOff * (i < 3 ? -1 : 1),
          })
        }
        break

      case 'swarm':
        for (let i = 0; i < count; i++) {
          spawns.push({
            type: available[rng.nextInt(available.length)]!,
            x: halfW + spawnOffset + i * 25,
            y: (rng.next() - 0.5) * halfH * 1.6,
          })
        }
        break

      case 'mixed':
        spawns.push({ type: 'shooter', x: halfW + spawnOffset, y: -halfH * 0.5 })
        spawns.push({ type: 'shooter', x: halfW + spawnOffset, y: halfH * 0.5 })
        for (let i = 0; i < 4; i++) {
          spawns.push({
            type: 'grunt',
            x: halfW + spawnOffset + 30 + i * 35,
            y: (rng.next() - 0.5) * 40,
          })
        }
        break

      case 'rush':
        for (let i = 0; i < count + 3; i++) {
          spawns.push({
            type: 'speeder',
            x: halfW + spawnOffset + i * 40,
            y: (rng.next() - 0.5) * halfH * 1.6,
          })
        }
        break

      case 'surround':
        for (let i = 0; i < 6; i++) {
          spawns.push({
            type: available[rng.nextInt(available.length)]!,
            x: halfW + spawnOffset,
            y: (i - 2.5) * 80,
          })
        }
        break
    }

    return spawns
  }

  /**
   * Generate a complete wave spawn
   */
  generateWave(wave: number, rng: SeededRandom): WaveSpawnResult {
    const result: WaveSpawnResult = {
      enemies: [],
    }

    // Pick random pattern
    const patterns = this.getPatterns()
    const pattern = patterns[rng.nextInt(patterns.length)]!

    // Generate pattern spawns
    result.enemies = this.generatePatternSpawns(pattern, wave, rng)

    // Add heavy enemy if applicable
    if (this.shouldSpawnHeavy(wave)) {
      const heavies = this.getHeavyEnemies(wave)
      if (heavies.length > 0) {
        result.enemies.push({
          type: heavies[rng.nextInt(heavies.length)]!,
          x: this.config.worldHalfWidth + this.config.spawnOffset + 50,
          y: 0,
        })
      }
    }

    // Add boss if applicable
    if (this.shouldSpawnBoss(wave)) {
      result.boss = {
        type: this.getBossType(wave),
        x: this.config.worldHalfWidth + this.config.spawnOffset,
        y: 0,
      }
    }

    return result
  }

  /**
   * Check if it's time to spawn the next wave
   */
  shouldSpawnNextWave(
    wave: number,
    waveTimer: number,
    enemyCount: number,
    bossActive: boolean
  ): boolean {
    // Never spawn during boss fight
    if (bossActive) return false

    // Initial wave spawn
    if (wave === 1 && enemyCount === 0 && waveTimer > this.config.initialDelay) {
      return true
    }

    // Regular wave spawn
    if (waveTimer > this.config.waveInterval && enemyCount < this.config.minEnemiesForNextWave) {
      return true
    }

    return false
  }

  /**
   * Get configuration
   */
  getConfig(): WaveConfig {
    return { ...this.config }
  }

  /**
   * Update configuration
   */
  setConfig(config: Partial<WaveConfig>): void {
    this.config = { ...this.config, ...config }
  }
}

/**
 * Enemy stats configuration
 */
export interface EnemyStats {
  health: number
  speed: number
  score: number
  hasShield?: boolean
  shieldHealth?: number
  fireRate?: number
  behavior: 'straight' | 'sine' | 'circle' | 'dive' | 'chase' | 'stationary'
}

/**
 * Get default stats for an enemy type
 */
export function getEnemyStats(type: EnemyType): EnemyStats {
  switch (type) {
    case 'grunt':
      return { health: 20, speed: 2, score: 100, behavior: 'straight' }
    case 'swerver':
      return { health: 20, speed: 2.5, score: 150, behavior: 'sine' }
    case 'shooter':
      return { health: 30, speed: 1.5, score: 200, fireRate: 90, behavior: 'straight' }
    case 'speeder':
      return { health: 15, speed: 5, score: 120, behavior: 'straight' }
    case 'mine':
      return { health: 10, speed: 0, score: 50, behavior: 'stationary' }
    case 'bomber':
      return { health: 40, speed: 1.5, score: 250, fireRate: 120, behavior: 'straight' }
    case 'spiral':
      return { health: 35, speed: 2, score: 300, fireRate: 60, behavior: 'circle' }
    case 'tank':
      return { health: 100, speed: 1, score: 500, fireRate: 150, behavior: 'straight' }
    case 'sniper':
      return { health: 25, speed: 1, score: 350, fireRate: 180, behavior: 'stationary' }
    case 'carrier':
      return { health: 80, speed: 1, score: 600, behavior: 'straight' }
    case 'shield':
      return { health: 50, speed: 1.5, score: 400, hasShield: true, shieldHealth: 50, behavior: 'straight' }
    case 'splitter':
      return { health: 60, speed: 2, score: 450, behavior: 'straight' }
    case 'turret':
      return { health: 40, speed: 0, score: 200, fireRate: 90, behavior: 'stationary' }
    case 'interceptor':
      return { health: 30, speed: 4, score: 250, behavior: 'chase' }
    case 'fighter':
      return { health: 35, speed: 3, score: 300, fireRate: 60, behavior: 'dive' }
    case 'scout':
      return { health: 15, speed: 6, score: 100, behavior: 'straight' }
    default:
      return { health: 20, speed: 2, score: 100, behavior: 'straight' }
  }
}

/**
 * Boss stats configuration
 */
export interface BossStats {
  health: number
  score: number
  phases: number
}

/**
 * Get default stats for a boss type
 */
export function getBossStats(type: BossType): BossStats {
  switch (type) {
    case 0:
      return { health: 500, score: 5000, phases: 2 }
    case 1:
      return { health: 750, score: 7500, phases: 2 }
    case 2:
      return { health: 1000, score: 10000, phases: 3 }
    case 3:
      return { health: 1500, score: 15000, phases: 3 }
    case 4:
      return { health: 2000, score: 20000, phases: 4 }
    case 5:
      return { health: 3000, score: 30000, phases: 5 }
    default:
      return { health: 500, score: 5000, phases: 2 }
  }
}
