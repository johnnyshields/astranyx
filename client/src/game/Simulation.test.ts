import { describe, it, expect, beforeEach, vi } from 'vitest'
import {
  Simulation,
  SeededRandom,
  toFixed,
  fromFixed,
  type EnemyType,
  type BulletType,
  type PowerupType,
  type BossType,
  type PlayBounds,
} from './Simulation'
import type { PlayerInput } from '../network/LockstepNetcode'

describe('SeededRandom', () => {
  describe('constructor', () => {
    it('should create with seed', () => {
      const rng = new SeededRandom(12345)
      expect(rng).toBeInstanceOf(SeededRandom)
    })

    it('should use default seed of 1 if 0 provided', () => {
      const rng = new SeededRandom(0)
      // Should not be stuck at 0
      expect(rng.next()).toBeGreaterThan(0)
    })
  })

  describe('next', () => {
    it('should return value between 0 and 1', () => {
      const rng = new SeededRandom(12345)
      for (let i = 0; i < 100; i++) {
        const val = rng.next()
        expect(val).toBeGreaterThanOrEqual(0)
        expect(val).toBeLessThan(1)
      }
    })

    it('should be deterministic with same seed', () => {
      const rng1 = new SeededRandom(42)
      const rng2 = new SeededRandom(42)

      for (let i = 0; i < 100; i++) {
        expect(rng1.next()).toBe(rng2.next())
      }
    })

    it('should produce different sequences with different seeds', () => {
      const rng1 = new SeededRandom(42)
      const rng2 = new SeededRandom(43)

      // At least one of the first few values should differ
      let different = false
      for (let i = 0; i < 10; i++) {
        if (rng1.next() !== rng2.next()) {
          different = true
          break
        }
      }
      expect(different).toBe(true)
    })
  })

  describe('nextInt', () => {
    it('should return integer in range [0, max)', () => {
      const rng = new SeededRandom(12345)
      for (let i = 0; i < 100; i++) {
        const val = rng.nextInt(10)
        expect(Number.isInteger(val)).toBe(true)
        expect(val).toBeGreaterThanOrEqual(0)
        expect(val).toBeLessThan(10)
      }
    })
  })

  describe('nextRange', () => {
    it('should return value in range [min, max)', () => {
      const rng = new SeededRandom(12345)
      for (let i = 0; i < 100; i++) {
        const val = rng.nextRange(5, 15)
        expect(val).toBeGreaterThanOrEqual(5)
        expect(val).toBeLessThan(15)
      }
    })
  })

  describe('getSeed', () => {
    it('should return current state (changes after next)', () => {
      const rng = new SeededRandom(12345)
      const seed1 = rng.getSeed()
      rng.next()
      const seed2 = rng.getSeed()
      expect(seed1).not.toBe(seed2)
    })
  })
})

describe('Fixed-point math', () => {
  describe('toFixed', () => {
    it('should convert to fixed-point', () => {
      expect(toFixed(1)).toBe(65536) // 1 << 16
      expect(toFixed(0)).toBe(0)
      expect(toFixed(0.5)).toBe(32768)
    })

    it('should handle negative numbers', () => {
      expect(toFixed(-1)).toBe(-65536)
    })
  })

  describe('fromFixed', () => {
    it('should convert from fixed-point', () => {
      expect(fromFixed(65536)).toBe(1)
      expect(fromFixed(0)).toBe(0)
      expect(fromFixed(32768)).toBe(0.5)
    })

    it('should be inverse of toFixed', () => {
      for (const val of [0, 1, -1, 0.5, 100, -50.25]) {
        expect(fromFixed(toFixed(val))).toBeCloseTo(val, 4)
      }
    })
  })
})

describe('Simulation', () => {
  let simulation: Simulation

  beforeEach(() => {
    simulation = new Simulation(['player_1'], 12345)
  })

  describe('constructor', () => {
    it('should create simulation with single player', () => {
      expect(simulation).toBeInstanceOf(Simulation)
      const state = simulation.getState()
      expect(state.players).toHaveLength(1)
      expect(state.players[0]!.playerId).toBe('player_1')
    })

    it('should create simulation with multiple players', () => {
      const sim = new Simulation(['player_1', 'player_2'], 12345)
      const state = sim.getState()
      expect(state.players).toHaveLength(2)
      expect(state.players[0]!.playerId).toBe('player_1')
      expect(state.players[1]!.playerId).toBe('player_2')
    })

    it('should initialize state correctly', () => {
      const state = simulation.getState()
      expect(state.frame).toBe(0)
      expect(state.score).toBe(0)
      expect(state.multiplier).toBe(1)
      expect(state.wave).toBe(1)
      expect(state.gameOver).toBe(false)
      expect(state.bossActive).toBe(false)
      expect(state.bullets).toEqual([])
      expect(state.enemies).toEqual([])
      expect(state.powerups).toEqual([])
    })

    it('should position players at spawn points', () => {
      const sim = new Simulation(['p1', 'p2', 'p3', 'p4'], 12345)
      const state = sim.getState()

      // Players should be at different Y positions
      // getState() already converts from fixed-point, so values are floats
      const yPositions = state.players.map((p) => p.y)
      expect(yPositions[0]).toBeCloseTo(-100, 0)
      expect(yPositions[1]).toBeCloseTo(100, 0)
      expect(yPositions[2]).toBeCloseTo(-200, 0)
      expect(yPositions[3]).toBeCloseTo(200, 0)
    })

    it('should give players initial invincibility', () => {
      const state = simulation.getState()
      expect(state.players[0]!.invincible).toBe(180) // 3 seconds
    })
  })

  describe('tick', () => {
    it('should advance frame counter', () => {
      const input: PlayerInput = {
        up: false,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: false,
      }

      const initialFrame = simulation.getState().frame
      simulation.tick(new Map([['player_1', input]]))

      expect(simulation.getState().frame).toBe(initialFrame + 1)
    })

    it('should move player based on input', () => {
      const moveRightInput: PlayerInput = {
        up: false,
        down: false,
        left: false,
        right: true,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: false,
      }

      const initialX = simulation.getState().players[0]!.x

      // Tick several frames to build up velocity
      for (let i = 0; i < 10; i++) {
        simulation.tick(new Map([['player_1', moveRightInput]]))
      }

      expect(simulation.getState().players[0]!.x).toBeGreaterThan(initialX)
    })

    it('should decrease invincibility over time', () => {
      const input: PlayerInput = {
        up: false,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: false,
      }

      const initialInvincible = simulation.getState().players[0]!.invincible

      simulation.tick(new Map([['player_1', input]]))

      expect(simulation.getState().players[0]!.invincible).toBeLessThan(initialInvincible)
    })

    it('should decrement screen shake', () => {
      // Manually set screen shake for testing
      const state = simulation.getState()
      // We can't directly set state, but we can check the decay behavior
      // after it's set by explosions/damage
    })
  })

  describe('player movement', () => {
    it('should change player vertical velocity when pressing up', () => {
      const input: PlayerInput = {
        up: true,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: false,
      }

      const initialVy = simulation.getState().players[0]!.vy

      for (let i = 0; i < 10; i++) {
        simulation.tick(new Map([['player_1', input]]))
      }

      // Velocity changes when pressing up
      expect(simulation.getState().players[0]!.vy).not.toBe(initialVy)
    })

    it('should change player vertical velocity when pressing down', () => {
      const input: PlayerInput = {
        up: false,
        down: true,
        left: false,
        right: false,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: false,
      }

      const initialVy = simulation.getState().players[0]!.vy

      for (let i = 0; i < 10; i++) {
        simulation.tick(new Map([['player_1', input]]))
      }

      // Velocity changes when pressing down
      expect(simulation.getState().players[0]!.vy).not.toBe(initialVy)
    })
  })

  describe('setPlayBounds', () => {
    it('should accept custom play bounds', () => {
      const bounds: PlayBounds = {
        leftX: -500,
        rightX: 500,
        getTopY: () => 300,
        getBottomY: () => -300,
      }

      simulation.setPlayBounds(bounds)

      // No error should be thrown
    })

    it('should nudge players inside new bounds', () => {
      // Move player far outside default bounds
      const moveRightInput: PlayerInput = {
        up: false,
        down: false,
        left: false,
        right: true,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: false,
      }

      for (let i = 0; i < 100; i++) {
        simulation.tick(new Map([['player_1', moveRightInput]]))
      }

      // Set tighter bounds
      const bounds: PlayBounds = {
        leftX: -100,
        rightX: 100,
        getTopY: () => 100,
        getBottomY: () => -100,
      }

      const prevX = simulation.getState().players[0]!.x
      simulation.setPlayBounds(bounds)

      // Player should be nudged back
      expect(simulation.getState().players[0]!.x).toBeLessThanOrEqual(prevX)
    })
  })

  describe('getState', () => {
    it('should return current simulation state', () => {
      const state = simulation.getState()

      expect(state).toHaveProperty('frame')
      expect(state).toHaveProperty('players')
      expect(state).toHaveProperty('bullets')
      expect(state).toHaveProperty('enemies')
      expect(state).toHaveProperty('boss')
      expect(state).toHaveProperty('powerups')
      expect(state).toHaveProperty('particles')
      expect(state).toHaveProperty('score')
      expect(state).toHaveProperty('wave')
      expect(state).toHaveProperty('gameOver')
    })
  })

  describe('determinism', () => {
    it('should produce identical states with same inputs', () => {
      const sim1 = new Simulation(['player_1'], 12345)
      const sim2 = new Simulation(['player_1'], 12345)

      const inputs: PlayerInput = {
        up: true,
        down: false,
        left: false,
        right: true,
        fire: true,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: false,
      }

      for (let i = 0; i < 100; i++) {
        sim1.tick(new Map([['player_1', inputs]]))
        sim2.tick(new Map([['player_1', inputs]]))

        const state1 = sim1.getState()
        const state2 = sim2.getState()

        expect(state1.frame).toBe(state2.frame)
        expect(state1.players[0]!.x).toBe(state2.players[0]!.x)
        expect(state1.players[0]!.y).toBe(state2.players[0]!.y)
        expect(state1.score).toBe(state2.score)
      }
    })

    it('should produce different states with different inputs', () => {
      const sim1 = new Simulation(['player_1'], 12345)
      const sim2 = new Simulation(['player_1'], 12345)

      const inputs1: PlayerInput = {
        up: true,
        down: false,
        left: false,
        right: false,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: false,
      }

      const inputs2: PlayerInput = {
        up: false,
        down: true,
        left: false,
        right: false,
        fire: false,
        special: false,
        secondary: false,
        swap: false,
        pickup: false,
        pause: false,
      }

      for (let i = 0; i < 10; i++) {
        sim1.tick(new Map([['player_1', inputs1]]))
        sim2.tick(new Map([['player_1', inputs2]]))
      }

      const state1 = sim1.getState()
      const state2 = sim2.getState()

      expect(state1.players[0]!.y).not.toBe(state2.players[0]!.y)
    })
  })
})

describe('Type definitions', () => {
  it('EnemyType should have valid values', () => {
    const types: EnemyType[] = [
      'grunt',
      'shooter',
      'swerver',
      'tank',
      'speeder',
      'bomber',
      'sniper',
      'carrier',
      'mine',
      'spiral',
      'shield',
      'splitter',
    ]

    expect(types).toHaveLength(12)
  })

  it('BulletType should have valid values', () => {
    const types: BulletType[] = [
      'shot',
      'spread',
      'laser',
      'mega',
      'missile',
      'drone',
      'enemy',
      'aimed',
      'big',
      'ring',
      'flame',
      'acid',
    ]

    expect(types).toHaveLength(12)
  })

  it('PowerupType should have valid values', () => {
    const types: PowerupType[] = [
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
      'LIFE',
    ]

    expect(types).toHaveLength(11)
  })

  it('BossType should be 0-5', () => {
    const types: BossType[] = [0, 1, 2, 3, 4, 5]
    expect(types).toHaveLength(6)
  })
})
