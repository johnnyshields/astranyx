import { describe, it, expect, beforeEach } from 'vitest'
import {
  WaveSpawner,
  type EnemyType,
  type BossType,
  getEnemyStats,
  getBossStats,
} from './WaveSpawner.ts'
import { SeededRandom } from '../math/SeededRandom.ts'

describe('WaveSpawner', () => {
  let spawner: WaveSpawner
  let rng: SeededRandom

  beforeEach(() => {
    spawner = new WaveSpawner()
    rng = new SeededRandom(12345)
  })

  describe('getAvailableEnemies', () => {
    it('should only have grunt on wave 1', () => {
      const enemies = spawner.getAvailableEnemies(1)
      expect(enemies).toEqual(['grunt'])
    })

    it('should add swerver on wave 2', () => {
      const enemies = spawner.getAvailableEnemies(2)
      expect(enemies).toContain('grunt')
      expect(enemies).toContain('swerver')
    })

    it('should add shooter and speeder on wave 3', () => {
      const enemies = spawner.getAvailableEnemies(3)
      expect(enemies).toContain('shooter')
      expect(enemies).toContain('speeder')
    })

    it('should add mine on wave 4', () => {
      const enemies = spawner.getAvailableEnemies(4)
      expect(enemies).toContain('mine')
    })

    it('should add bomber and spiral on wave 5', () => {
      const enemies = spawner.getAvailableEnemies(5)
      expect(enemies).toContain('bomber')
      expect(enemies).toContain('spiral')
    })

    it('should add tank and sniper on wave 7', () => {
      const enemies = spawner.getAvailableEnemies(7)
      expect(enemies).toContain('tank')
      expect(enemies).toContain('sniper')
    })

    it('should add carrier and shield on wave 9', () => {
      const enemies = spawner.getAvailableEnemies(9)
      expect(enemies).toContain('carrier')
      expect(enemies).toContain('shield')
    })

    it('should add splitter on wave 11', () => {
      const enemies = spawner.getAvailableEnemies(11)
      expect(enemies).toContain('splitter')
    })

    it('should have all enemies unlocked by wave 11', () => {
      const enemies = spawner.getAvailableEnemies(11)
      expect(enemies).toHaveLength(12) // All standard wave enemies
    })
  })

  describe('getHeavyEnemies', () => {
    it('should return empty array before wave 7', () => {
      expect(spawner.getHeavyEnemies(6)).toHaveLength(0)
    })

    it('should include tank after wave 7', () => {
      const heavies = spawner.getHeavyEnemies(7)
      expect(heavies).toContain('tank')
    })

    it('should include carrier and shield after wave 9', () => {
      const heavies = spawner.getHeavyEnemies(9)
      expect(heavies).toContain('tank')
      expect(heavies).toContain('carrier')
      expect(heavies).toContain('shield')
    })
  })

  describe('shouldSpawnBoss', () => {
    it('should spawn boss every 5 waves', () => {
      expect(spawner.shouldSpawnBoss(5)).toBe(true)
      expect(spawner.shouldSpawnBoss(10)).toBe(true)
      expect(spawner.shouldSpawnBoss(15)).toBe(true)
    })

    it('should not spawn boss on non-multiples of 5', () => {
      expect(spawner.shouldSpawnBoss(1)).toBe(false)
      expect(spawner.shouldSpawnBoss(3)).toBe(false)
      expect(spawner.shouldSpawnBoss(7)).toBe(false)
    })

    it('should not spawn boss on wave 0', () => {
      expect(spawner.shouldSpawnBoss(0)).toBe(false)
    })
  })

  describe('getBossType', () => {
    it('should return boss type based on wave', () => {
      expect(spawner.getBossType(5)).toBe(0)
      expect(spawner.getBossType(10)).toBe(1)
      expect(spawner.getBossType(15)).toBe(2)
      expect(spawner.getBossType(20)).toBe(3)
      expect(spawner.getBossType(25)).toBe(4)
      expect(spawner.getBossType(30)).toBe(5)
    })

    it('should cap at boss type 5', () => {
      expect(spawner.getBossType(35)).toBe(5)
      expect(spawner.getBossType(100)).toBe(5)
    })
  })

  describe('shouldSpawnHeavy', () => {
    it('should not spawn heavy before wave 6', () => {
      expect(spawner.shouldSpawnHeavy(3)).toBe(false)
    })

    it('should spawn heavy on multiples of 3 after wave 6', () => {
      expect(spawner.shouldSpawnHeavy(6)).toBe(true)
      expect(spawner.shouldSpawnHeavy(9)).toBe(true)
      expect(spawner.shouldSpawnHeavy(12)).toBe(true)
    })

    it('should not spawn heavy on non-multiples of 3', () => {
      expect(spawner.shouldSpawnHeavy(7)).toBe(false)
      expect(spawner.shouldSpawnHeavy(8)).toBe(false)
      expect(spawner.shouldSpawnHeavy(10)).toBe(false)
    })
  })

  describe('getEnemyCount', () => {
    it('should calculate enemy count based on wave', () => {
      expect(spawner.getEnemyCount(1)).toBe(4) // 4 + floor(0.8) = 4
      expect(spawner.getEnemyCount(5)).toBe(8) // 4 + floor(4) = 8
      expect(spawner.getEnemyCount(10)).toBe(12) // 4 + floor(8) = 12
    })
  })

  describe('generatePatternSpawns', () => {
    it('should generate line pattern', () => {
      const spawns = spawner.generatePatternSpawns('line', 5, rng)
      expect(spawns.length).toBeGreaterThan(0)
      // All spawns should be to the right
      for (const spawn of spawns) {
        expect(spawn.x).toBeGreaterThan(1000)
      }
    })

    it('should generate v pattern with 7 grunts', () => {
      const spawns = spawner.generatePatternSpawns('v', 5, rng)
      expect(spawns).toHaveLength(7)
      for (const spawn of spawns) {
        expect(spawn.type).toBe('grunt')
      }
    })

    it('should generate swarm pattern', () => {
      const spawns = spawner.generatePatternSpawns('swarm', 5, rng)
      expect(spawns.length).toBe(spawner.getEnemyCount(5))
    })

    it('should generate mixed pattern with shooters and grunts', () => {
      const spawns = spawner.generatePatternSpawns('mixed', 5, rng)
      const shooters = spawns.filter(s => s.type === 'shooter')
      const grunts = spawns.filter(s => s.type === 'grunt')
      expect(shooters).toHaveLength(2)
      expect(grunts).toHaveLength(4)
    })

    it('should generate rush pattern with speeders', () => {
      const spawns = spawner.generatePatternSpawns('rush', 5, rng)
      for (const spawn of spawns) {
        expect(spawn.type).toBe('speeder')
      }
    })

    it('should generate surround pattern with 6 enemies', () => {
      const spawns = spawner.generatePatternSpawns('surround', 5, rng)
      expect(spawns).toHaveLength(6)
    })
  })

  describe('generateWave', () => {
    it('should generate enemies for a wave', () => {
      const result = spawner.generateWave(1, rng)
      expect(result.enemies.length).toBeGreaterThan(0)
    })

    it('should include boss on wave 5', () => {
      const result = spawner.generateWave(5, rng)
      expect(result.boss).toBeDefined()
      expect(result.boss!.type).toBe(0)
    })

    it('should include boss on wave 10', () => {
      const result = spawner.generateWave(10, rng)
      expect(result.boss).toBeDefined()
      expect(result.boss!.type).toBe(1)
    })

    it('should not include boss on non-boss waves', () => {
      const result = spawner.generateWave(3, rng)
      expect(result.boss).toBeUndefined()
    })

    it('should include heavy enemy on wave 9', () => {
      const result = spawner.generateWave(9, rng)
      const heavyTypes = ['tank', 'carrier', 'shield']
      const hasHeavy = result.enemies.some(e => heavyTypes.includes(e.type))
      expect(hasHeavy).toBe(true)
    })

    it('should be deterministic with same seed', () => {
      const rng1 = new SeededRandom(99999)
      const rng2 = new SeededRandom(99999)

      const result1 = spawner.generateWave(7, rng1)
      const result2 = spawner.generateWave(7, rng2)

      expect(result1.enemies.length).toBe(result2.enemies.length)
      for (let i = 0; i < result1.enemies.length; i++) {
        expect(result1.enemies[i]!.type).toBe(result2.enemies[i]!.type)
        expect(result1.enemies[i]!.x).toBe(result2.enemies[i]!.x)
        expect(result1.enemies[i]!.y).toBe(result2.enemies[i]!.y)
      }
    })
  })

  describe('shouldSpawnNextWave', () => {
    it('should spawn initial wave after delay', () => {
      expect(spawner.shouldSpawnNextWave(1, 1.3, 0, false)).toBe(true)
    })

    it('should not spawn initial wave too early', () => {
      expect(spawner.shouldSpawnNextWave(1, 1.0, 0, false)).toBe(false)
    })

    it('should spawn next wave when timer expires and few enemies', () => {
      expect(spawner.shouldSpawnNextWave(5, 7, 2, false)).toBe(true)
    })

    it('should not spawn if too many enemies', () => {
      expect(spawner.shouldSpawnNextWave(5, 7, 10, false)).toBe(false)
    })

    it('should not spawn if timer not expired', () => {
      expect(spawner.shouldSpawnNextWave(5, 3, 2, false)).toBe(false)
    })

    it('should never spawn during boss fight', () => {
      expect(spawner.shouldSpawnNextWave(5, 10, 0, true)).toBe(false)
    })
  })

  describe('configuration', () => {
    it('should use default config', () => {
      const config = spawner.getConfig()
      expect(config.worldHalfWidth).toBe(1000)
      expect(config.bossEveryWaves).toBe(5)
    })

    it('should accept custom config', () => {
      const custom = new WaveSpawner({
        worldHalfWidth: 800,
        bossEveryWaves: 3,
      })

      expect(custom.getConfig().worldHalfWidth).toBe(800)
      expect(custom.getConfig().bossEveryWaves).toBe(3)
    })

    it('should allow config updates', () => {
      spawner.setConfig({ waveInterval: 10 })
      expect(spawner.getConfig().waveInterval).toBe(10)
    })
  })
})

describe('getEnemyStats', () => {
  it('should return stats for grunt', () => {
    const stats = getEnemyStats('grunt')
    expect(stats.health).toBe(20)
    expect(stats.speed).toBe(2)
    expect(stats.score).toBe(100)
    expect(stats.behavior).toBe('straight')
  })

  it('should return stats for tank', () => {
    const stats = getEnemyStats('tank')
    expect(stats.health).toBe(100)
    expect(stats.score).toBe(500)
    expect(stats.fireRate).toBeDefined()
  })

  it('should return stats for shield enemy', () => {
    const stats = getEnemyStats('shield')
    expect(stats.hasShield).toBe(true)
    expect(stats.shieldHealth).toBe(50)
  })

  it('should return stats for all enemy types', () => {
    const types: EnemyType[] = [
      'grunt', 'swerver', 'shooter', 'speeder', 'mine', 'bomber',
      'spiral', 'tank', 'sniper', 'carrier', 'shield', 'splitter',
      'turret', 'interceptor', 'fighter', 'scout',
    ]

    for (const type of types) {
      const stats = getEnemyStats(type)
      expect(stats.health).toBeGreaterThan(0)
      expect(stats.score).toBeGreaterThan(0)
      expect(stats.behavior).toBeDefined()
    }
  })

  it('should have different speeds for different enemies', () => {
    expect(getEnemyStats('speeder').speed).toBeGreaterThan(getEnemyStats('tank').speed)
    expect(getEnemyStats('scout').speed).toBeGreaterThan(getEnemyStats('grunt').speed)
  })

  it('should have different behaviors', () => {
    expect(getEnemyStats('swerver').behavior).toBe('sine')
    expect(getEnemyStats('spiral').behavior).toBe('circle')
    expect(getEnemyStats('interceptor').behavior).toBe('chase')
    expect(getEnemyStats('fighter').behavior).toBe('dive')
    expect(getEnemyStats('mine').behavior).toBe('stationary')
  })
})

describe('getBossStats', () => {
  it('should return stats for boss type 0', () => {
    const stats = getBossStats(0)
    expect(stats.health).toBe(500)
    expect(stats.score).toBe(5000)
    expect(stats.phases).toBe(2)
  })

  it('should return increasing health for later bosses', () => {
    const boss0 = getBossStats(0)
    const boss3 = getBossStats(3)
    const boss5 = getBossStats(5)

    expect(boss3.health).toBeGreaterThan(boss0.health)
    expect(boss5.health).toBeGreaterThan(boss3.health)
  })

  it('should return increasing phases for later bosses', () => {
    expect(getBossStats(0).phases).toBe(2)
    expect(getBossStats(2).phases).toBe(3)
    expect(getBossStats(4).phases).toBe(4)
    expect(getBossStats(5).phases).toBe(5)
  })

  it('should return stats for all boss types', () => {
    const types: BossType[] = [0, 1, 2, 3, 4, 5]

    for (const type of types) {
      const stats = getBossStats(type)
      expect(stats.health).toBeGreaterThan(0)
      expect(stats.score).toBeGreaterThan(0)
      expect(stats.phases).toBeGreaterThan(0)
    }
  })
})
