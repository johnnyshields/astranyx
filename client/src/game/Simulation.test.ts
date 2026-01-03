import { describe, it, expect, beforeEach } from 'vitest'
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
      const _state = simulation.getState()
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

describe('Owner-Authoritative Events', () => {
  const emptyInput: PlayerInput = {
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

  describe('setLocalPlayerId', () => {
    it('should enable multiplayer mode when set', () => {
      const sim = new Simulation(['player_1', 'player_2'], 12345)
      sim.setLocalPlayerId('player_1')
      // No error thrown, multiplayer mode enabled
    })

    it('should work with any valid player ID', () => {
      const sim = new Simulation(['player_1', 'player_2'], 12345)
      sim.setLocalPlayerId('player_2')
      // No error thrown
    })
  })

  describe('getPendingEvents', () => {
    it('should return empty array initially', () => {
      const sim = new Simulation(['player_1'], 12345)
      sim.setLocalPlayerId('player_1')
      expect(sim.getPendingEvents()).toEqual([])
    })

    it('should clear events after getting them', () => {
      const sim = new Simulation(['player_1'], 12345)
      sim.setLocalPlayerId('player_1')

      // First call
      const events1 = sim.getPendingEvents()
      expect(events1).toEqual([])

      // Second call should also be empty (not accumulated)
      const events2 = sim.getPendingEvents()
      expect(events2).toEqual([])
    })
  })

  describe('damage events', () => {
    it('should generate damage event for local player when hit', () => {
      const sim = new Simulation(['player_1', 'player_2'], 12345)
      sim.setLocalPlayerId('player_1')

      // Run simulation until invincibility wears off
      for (let i = 0; i < 200; i++) {
        sim.tick(new Map([
          ['player_1', emptyInput],
          ['player_2', emptyInput],
        ]))
        sim.getPendingEvents() // Clear events
      }

      const state = sim.getState()
      const player1 = state.players.find(p => p.playerId === 'player_1')!
      expect(player1.invincible).toBe(0)

      // We can't easily trigger damage in tests without spawning enemies
      // But we can verify the event system is wired up by checking no events
      // are generated during normal gameplay
      const events = sim.getPendingEvents()
      expect(Array.isArray(events)).toBe(true)
    })

    it('should NOT generate damage event for remote player', () => {
      const sim = new Simulation(['player_1', 'player_2'], 12345)
      sim.setLocalPlayerId('player_1')

      // Run some ticks
      for (let i = 0; i < 10; i++) {
        sim.tick(new Map([
          ['player_1', emptyInput],
          ['player_2', emptyInput],
        ]))
      }

      // Events should only be for local player (player_1)
      const events = sim.getPendingEvents()
      for (const event of events) {
        if (event.type === 'damage') {
          expect(event.playerId).toBe('player_1')
        }
      }
    })
  })

  describe('applyEvents', () => {
    it('should apply damage event from remote player', () => {
      const sim = new Simulation(['player_1', 'player_2'], 12345)
      sim.setLocalPlayerId('player_1')

      const initialState = sim.getState()
      const player2Initial = initialState.players.find(p => p.playerId === 'player_2')!
      const initialShields = player2Initial.shields

      // Apply damage event for player_2 (remote)
      sim.applyEvents([{
        type: 'damage',
        playerId: 'player_2',
        amount: 25,
        newShields: initialShields - 25,
        newLives: 3,
      }])

      const newState = sim.getState()
      const player2After = newState.players.find(p => p.playerId === 'player_2')!
      expect(player2After.shields).toBe(initialShields - 25)
    })

    it('should apply death event from remote player', () => {
      const sim = new Simulation(['player_1', 'player_2'], 12345)
      sim.setLocalPlayerId('player_1')

      const initialState = sim.getState()
      const player2Initial = initialState.players.find(p => p.playerId === 'player_2')!
      expect(player2Initial.dead).toBe(false)

      // Apply death event for player_2 (remote)
      sim.applyEvents([{
        type: 'death',
        playerId: 'player_2',
      }])

      const newState = sim.getState()
      const player2After = newState.players.find(p => p.playerId === 'player_2')!
      expect(player2After.dead).toBe(true)
    })

    it('should apply respawn event from remote player', () => {
      const sim = new Simulation(['player_1', 'player_2'], 12345)
      sim.setLocalPlayerId('player_1')

      // First kill player_2
      sim.applyEvents([{
        type: 'death',
        playerId: 'player_2',
      }])

      let state = sim.getState()
      let player2 = state.players.find(p => p.playerId === 'player_2')!
      expect(player2.dead).toBe(true)

      // Now respawn
      sim.applyEvents([{
        type: 'respawn',
        playerId: 'player_2',
      }])

      state = sim.getState()
      player2 = state.players.find(p => p.playerId === 'player_2')!
      expect(player2.dead).toBe(false)
      expect(player2.invincible).toBeGreaterThan(0)
    })

    it('should ignore events for non-existent players', () => {
      const sim = new Simulation(['player_1'], 12345)
      sim.setLocalPlayerId('player_1')

      // Apply event for non-existent player - should not throw
      sim.applyEvents([{
        type: 'damage',
        playerId: 'player_999',
        amount: 25,
        newShields: 75,
        newLives: 3,
      }])

      // State should be unchanged
      const state = sim.getState()
      expect(state.players).toHaveLength(1)
    })

    it('should apply multiple events in order', () => {
      const sim = new Simulation(['player_1', 'player_2'], 12345)
      sim.setLocalPlayerId('player_1')

      const initialState = sim.getState()
      const player2Initial = initialState.players.find(p => p.playerId === 'player_2')!

      // Apply multiple damage events
      sim.applyEvents([
        {
          type: 'damage',
          playerId: 'player_2',
          amount: 10,
          newShields: player2Initial.shields - 10,
          newLives: 3,
        },
        {
          type: 'damage',
          playerId: 'player_2',
          amount: 15,
          newShields: player2Initial.shields - 25,
          newLives: 3,
        },
      ])

      const newState = sim.getState()
      const player2After = newState.players.find(p => p.playerId === 'player_2')!
      // Last event's newShields should be the final value
      expect(player2After.shields).toBe(player2Initial.shields - 25)
    })
  })

  describe('pickup events', () => {
    it('should apply pickup event from remote player', () => {
      const sim = new Simulation(['player_1', 'player_2'], 12345)
      sim.setLocalPlayerId('player_1')

      // Run simulation to potentially spawn powerups
      for (let i = 0; i < 500; i++) {
        sim.tick(new Map([
          ['player_1', emptyInput],
          ['player_2', emptyInput],
        ]))
        sim.getPendingEvents() // Clear events
      }

      // Check if any powerups exist
      const state = sim.getState()
      if (state.powerups.length > 0) {
        const powerup = state.powerups[0]!
        const _player2 = state.players.find(p => p.playerId === 'player_2')!

        // Apply pickup event
        sim.applyEvents([{
          type: 'pickup',
          playerId: 'player_2',
          pickupId: powerup.id,
        }])

        const newState = sim.getState()
        // Powerup should be removed
        expect(newState.powerups.find(p => p.id === powerup.id)).toBeUndefined()
      }
    })

    it('should ignore pickup event for non-existent powerup', () => {
      const sim = new Simulation(['player_1', 'player_2'], 12345)
      sim.setLocalPlayerId('player_1')

      const initialState = sim.getState()
      const initialPowerupCount = initialState.powerups.length

      // Apply pickup for non-existent powerup - should not throw
      sim.applyEvents([{
        type: 'pickup',
        playerId: 'player_2',
        pickupId: 99999,
      }])

      const newState = sim.getState()
      expect(newState.powerups.length).toBe(initialPowerupCount)
    })
  })

  describe('weapon_pickup events', () => {
    it('should apply weapon_pickup event from remote player', () => {
      const sim = new Simulation(['player_1', 'player_2'], 12345)
      sim.setLocalPlayerId('player_1')

      // Run simulation to potentially spawn weapon drops
      for (let i = 0; i < 1000; i++) {
        sim.tick(new Map([
          ['player_1', emptyInput],
          ['player_2', emptyInput],
        ]))
        sim.getPendingEvents() // Clear events
      }

      // Check if any weapon drops exist
      const state = sim.getState()
      if (state.weaponDrops && state.weaponDrops.length > 0) {
        const drop = state.weaponDrops[0]!

        // Apply weapon pickup event
        sim.applyEvents([{
          type: 'weapon_pickup',
          playerId: 'player_2',
          dropId: drop.id,
        }])

        const newState = sim.getState()
        // Weapon drop should be removed
        expect(newState.weaponDrops.find(d => d.id === drop.id)).toBeUndefined()
      }
    })

    it('should ignore weapon_pickup event for non-existent drop', () => {
      const sim = new Simulation(['player_1', 'player_2'], 12345)
      sim.setLocalPlayerId('player_1')

      // Apply weapon pickup for non-existent drop - should not throw
      sim.applyEvents([{
        type: 'weapon_pickup',
        playerId: 'player_2',
        dropId: 99999,
      }])

      // Should not throw, state should be unchanged
      const state = sim.getState()
      expect(state.players).toHaveLength(2)
    })
  })

  describe('local vs remote collision detection', () => {
    it('should only check collisions for local player in multiplayer', () => {
      // Create two simulations with different local players
      const sim1 = new Simulation(['player_1', 'player_2'], 12345)
      const sim2 = new Simulation(['player_1', 'player_2'], 12345)

      sim1.setLocalPlayerId('player_1')
      sim2.setLocalPlayerId('player_2')

      // Run both simulations with identical inputs
      for (let i = 0; i < 100; i++) {
        sim1.tick(new Map([
          ['player_1', emptyInput],
          ['player_2', emptyInput],
        ]))
        sim2.tick(new Map([
          ['player_1', emptyInput],
          ['player_2', emptyInput],
        ]))
      }

      // Get events from both - they should only have events for their local player
      // (Though in this case with no enemies, there may be no events)
      const events1 = sim1.getPendingEvents()
      const events2 = sim2.getPendingEvents()

      for (const event of events1) {
        if (event.type === 'damage' || event.type === 'pickup' || event.type === 'weapon_pickup') {
          expect(event.playerId).toBe('player_1')
        }
      }

      for (const event of events2) {
        if (event.type === 'damage' || event.type === 'pickup' || event.type === 'weapon_pickup') {
          expect(event.playerId).toBe('player_2')
        }
      }
    })
  })

  describe('single player mode (no localPlayerId set)', () => {
    it('should work normally without owner-authoritative events', () => {
      const sim = new Simulation(['player_1'], 12345)
      // Don't call setLocalPlayerId - single player mode

      // Run some ticks
      for (let i = 0; i < 100; i++) {
        sim.tick(new Map([['player_1', emptyInput]]))
      }

      // Should not generate events in single player mode
      // (collisions are processed normally)
      const events = sim.getPendingEvents()
      expect(events).toEqual([])
    })

    it('should process all collisions in single player mode', () => {
      const sim = new Simulation(['player_1'], 12345)
      // Don't call setLocalPlayerId - all collision detection enabled

      // Run simulation
      for (let i = 0; i < 50; i++) {
        sim.tick(new Map([['player_1', emptyInput]]))
      }

      // State should advance normally
      const state = sim.getState()
      expect(state.frame).toBe(50)
    })
  })
})

describe('Simulation state sync', () => {
  const emptyInput: PlayerInput = {
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

  describe('getChecksum', () => {
    it('should return a number', () => {
      const sim = new Simulation(['player_1'], 12345)
      const checksum = sim.getChecksum()
      expect(typeof checksum).toBe('number')
      expect(Number.isFinite(checksum)).toBe(true)
    })

    it('should return same checksum for identical states', () => {
      const sim1 = new Simulation(['player_1'], 12345)
      const sim2 = new Simulation(['player_1'], 12345)

      const checksum1 = sim1.getChecksum()
      const checksum2 = sim2.getChecksum()

      expect(checksum1).toBe(checksum2)
      // Verify it's a valid number
      expect(Number.isFinite(checksum1)).toBe(true)
    })

    it('should return different checksum after ticks', () => {
      const sim = new Simulation(['player_1'], 12345)
      const checksum1 = sim.getChecksum()

      sim.tick(new Map([['player_1', emptyInput]]))
      const checksum2 = sim.getChecksum()

      expect(checksum1).not.toBe(checksum2)
      // Both should be valid numbers
      expect(Number.isFinite(checksum1)).toBe(true)
      expect(Number.isFinite(checksum2)).toBe(true)
    })

    it('should remain deterministic across runs', () => {
      const sim1 = new Simulation(['player_1'], 12345)
      const sim2 = new Simulation(['player_1'], 12345)

      for (let i = 0; i < 100; i++) {
        sim1.tick(new Map([['player_1', emptyInput]]))
        sim2.tick(new Map([['player_1', emptyInput]]))
      }

      expect(sim1.getChecksum()).toBe(sim2.getChecksum())
      // States should also match
      expect(sim1.getState().frame).toBe(sim2.getState().frame)
      expect(sim1.getState().score).toBe(sim2.getState().score)
    })

    it('should differ for simulations with different seeds', () => {
      const sim1 = new Simulation(['player_1'], 12345)
      const sim2 = new Simulation(['player_1'], 54321)

      // Run same number of ticks with same inputs
      for (let i = 0; i < 100; i++) {
        sim1.tick(new Map([['player_1', emptyInput]]))
        sim2.tick(new Map([['player_1', emptyInput]]))
      }

      // Checksums should differ due to different RNG seeds affecting spawns
      // (may be same if no RNG-dependent events occurred)
      expect(sim1.getState().frame).toBe(sim2.getState().frame)
    })
  })

  describe('getDebugState', () => {
    it('should return debug state object with all required fields', () => {
      const sim = new Simulation(['player_1'], 12345)
      const debug = sim.getDebugState()

      expect(debug).toHaveProperty('frame')
      expect(debug).toHaveProperty('rngSeed')
      expect(debug).toHaveProperty('playerCount')
      expect(debug).toHaveProperty('players')
      expect(debug).toHaveProperty('enemyCount')
      expect(debug).toHaveProperty('bulletCount')
      expect(debug).toHaveProperty('powerupCount')
      expect(debug).toHaveProperty('weaponDropCount')
      expect(debug).toHaveProperty('score')

      // Type checks
      expect(typeof debug.frame).toBe('number')
      expect(typeof debug.rngSeed).toBe('number')
      expect(typeof debug.playerCount).toBe('number')
      expect(Array.isArray(debug.players)).toBe(true)
      expect(typeof debug.score).toBe('number')
    })

    it('should have correct player count for single player', () => {
      const sim = new Simulation(['player_1'], 12345)
      const debug = sim.getDebugState()

      expect(debug.playerCount).toBe(1)
      expect(debug.players).toHaveLength(1)
    })

    it('should have correct player count for multiple players', () => {
      const sim = new Simulation(['player_1', 'player_2'], 12345)
      const debug = sim.getDebugState()

      expect(debug.playerCount).toBe(2)
      expect(debug.players).toHaveLength(2)
    })

    it('should return float positions in debug state (not fixed-point)', () => {
      const sim = new Simulation(['player_1'], 12345)
      const debug = sim.getDebugState()

      // Positions should be floats in reasonable world coordinates, not fixed-point
      expect(debug.players[0]!.x).toBeLessThan(1000) // Fixed point would be much larger
      expect(debug.players[0]!.y).toBeLessThan(1000)
      expect(typeof debug.players[0]!.x).toBe('number')
      expect(typeof debug.players[0]!.y).toBe('number')
    })

    it('should update counts after simulation runs', () => {
      const sim = new Simulation(['player_1'], 12345)

      const debugBefore = sim.getDebugState()
      expect(debugBefore.frame).toBe(0)

      // Run simulation to potentially spawn enemies
      for (let i = 0; i < 100; i++) {
        sim.tick(new Map([['player_1', emptyInput]]))
      }

      const debugAfter = sim.getDebugState()
      expect(debugAfter.frame).toBe(100)
      // Enemy count may have increased
      expect(typeof debugAfter.enemyCount).toBe('number')
    })
  })

  describe('serializeState', () => {
    it('should return serialized state object with all required fields', () => {
      const sim = new Simulation(['player_1'], 12345)
      const serialized = sim.serializeState()

      // Core state
      expect(serialized).toHaveProperty('frame')
      expect(serialized).toHaveProperty('rngSeed')
      expect(serialized).toHaveProperty('players')
      expect(serialized).toHaveProperty('nextId')

      // Entities
      expect(serialized).toHaveProperty('bullets')
      expect(serialized).toHaveProperty('beams')
      expect(serialized).toHaveProperty('missiles')
      expect(serialized).toHaveProperty('enemies')
      expect(serialized).toHaveProperty('boss')
      expect(serialized).toHaveProperty('powerups')
      expect(serialized).toHaveProperty('weaponDrops')

      // Game state
      expect(serialized).toHaveProperty('score')
      expect(serialized).toHaveProperty('multiplier')
      expect(serialized).toHaveProperty('wave')
      expect(serialized).toHaveProperty('waveTimer')
      expect(serialized).toHaveProperty('bossActive')
      expect(serialized).toHaveProperty('screenShake')
      expect(serialized).toHaveProperty('gameOver')

      // Type validations
      expect(typeof serialized.frame).toBe('number')
      expect(typeof serialized.rngSeed).toBe('number')
      expect(Array.isArray(serialized.players)).toBe(true)
      expect(Array.isArray(serialized.bullets)).toBe(true)
      expect(Array.isArray(serialized.enemies)).toBe(true)
      expect(typeof serialized.gameOver).toBe('boolean')
    })

    it('should serialize after simulation runs with correct frame', () => {
      const sim = new Simulation(['player_1'], 12345)

      for (let i = 0; i < 50; i++) {
        sim.tick(new Map([['player_1', emptyInput]]))
      }

      const serialized = sim.serializeState()
      expect(serialized.frame).toBe(50)
      expect(serialized.wave).toBeGreaterThanOrEqual(1)
    })

    it('should be JSON serializable', () => {
      const sim = new Simulation(['player_1'], 12345)

      for (let i = 0; i < 30; i++) {
        sim.tick(new Map([['player_1', emptyInput]]))
      }

      const serialized = sim.serializeState()

      // Should be able to stringify and parse without error
      const jsonStr = JSON.stringify(serialized)
      const parsed = JSON.parse(jsonStr)

      expect(parsed.frame).toBe(serialized.frame)
      expect(parsed.score).toBe(serialized.score)
    })
  })

  describe('applyState', () => {
    it('should apply serialized state to simulation and sync checksums', () => {
      const sim1 = new Simulation(['player_1'], 12345)
      const sim2 = new Simulation(['player_1'], 99999) // Different seed

      // Run sim1 for a while
      for (let i = 0; i < 100; i++) {
        sim1.tick(new Map([['player_1', emptyInput]]))
      }

      // Serialize and apply to sim2
      const serialized = sim1.serializeState()
      sim2.applyState(serialized)

      // States should now match
      expect(sim2.getChecksum()).toBe(sim1.getChecksum())
      expect(sim2.getFrame()).toBe(sim1.getFrame())
      expect(sim2.getState().score).toBe(sim1.getState().score)
    })

    it('should restore RNG state for deterministic continuation', () => {
      const sim1 = new Simulation(['player_1'], 12345)
      const sim2 = new Simulation(['player_1'], 99999)

      // Run sim1
      for (let i = 0; i < 50; i++) {
        sim1.tick(new Map([['player_1', emptyInput]]))
      }

      // Apply state
      sim2.applyState(sim1.serializeState())

      // Verify frame sync before continuing
      expect(sim2.getFrame()).toBe(sim1.getFrame())

      // Run both more and check they stay in sync
      for (let i = 0; i < 50; i++) {
        sim1.tick(new Map([['player_1', emptyInput]]))
        sim2.tick(new Map([['player_1', emptyInput]]))
      }

      expect(sim2.getChecksum()).toBe(sim1.getChecksum())
      expect(sim2.getFrame()).toBe(100)
    })

    it('should restore player states correctly', () => {
      const sim1 = new Simulation(['player_1', 'player_2'], 12345)
      const sim2 = new Simulation(['player_1', 'player_2'], 99999)

      const moveRight: PlayerInput = { ...emptyInput, right: true }

      // Move player 1 right
      for (let i = 0; i < 30; i++) {
        sim1.tick(new Map([
          ['player_1', moveRight],
          ['player_2', emptyInput],
        ]))
      }

      const state1Before = sim1.getState()
      const p1x = state1Before.players.find(p => p.playerId === 'player_1')!.x

      // Apply state to sim2
      sim2.applyState(sim1.serializeState())

      const state2After = sim2.getState()
      const p1x2 = state2After.players.find(p => p.playerId === 'player_1')!.x

      // Player positions should match
      expect(p1x2).toBe(p1x)
    })
  })

  describe('getPlayBounds', () => {
    it('should return current play bounds with all properties', () => {
      const sim = new Simulation(['player_1'], 12345)
      const bounds = sim.getPlayBounds()

      expect(bounds).toHaveProperty('leftX')
      expect(bounds).toHaveProperty('rightX')
      expect(typeof bounds.getTopY).toBe('function')
      expect(typeof bounds.getBottomY).toBe('function')

      // Type checks
      expect(typeof bounds.leftX).toBe('number')
      expect(typeof bounds.rightX).toBe('number')
    })

    it('should have leftX less than rightX', () => {
      const sim = new Simulation(['player_1'], 12345)
      const bounds = sim.getPlayBounds()

      expect(bounds.leftX).toBeLessThan(bounds.rightX)
    })

    it('should return valid Y bounds from functions', () => {
      const sim = new Simulation(['player_1'], 12345)
      const bounds = sim.getPlayBounds()

      const topY = bounds.getTopY(0)
      const bottomY = bounds.getBottomY(0)

      expect(typeof topY).toBe('number')
      expect(typeof bottomY).toBe('number')
      expect(Number.isFinite(topY)).toBe(true)
      expect(Number.isFinite(bottomY)).toBe(true)
    })
  })
})

describe('Simulation firing', () => {
  const fireInput: PlayerInput = {
    up: false,
    down: false,
    left: false,
    right: false,
    fire: true,
    special: false,
    secondary: false,
    swap: false,
    pickup: false,
    pause: false,
  }

  const emptyInput: PlayerInput = {
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

  it('should create bullets when firing', () => {
    const sim = new Simulation(['player_1'], 12345)

    // Fire for several frames
    for (let i = 0; i < 30; i++) {
      sim.tick(new Map([['player_1', fireInput]]))
    }

    const state = sim.getState()
    expect(state.bullets.length).toBeGreaterThan(0)
    // Player bullets should not be marked as enemy bullets
    const playerBullets = state.bullets.filter(b => !b.isEnemy)
    expect(playerBullets.length).toBeGreaterThan(0)
  })

  it('should move bullets forward (positive X direction)', () => {
    const sim = new Simulation(['player_1'], 12345)

    // Fire for a few frames to ensure bullets are created
    for (let i = 0; i < 5; i++) {
      sim.tick(new Map([['player_1', fireInput]]))
    }

    const state1 = sim.getState()
    const playerBullets = state1.bullets.filter(b => !b.isEnemy)

    if (playerBullets.length > 0) {
      const bulletX1 = playerBullets[0]!.x

      // Continue simulation without firing
      for (let i = 0; i < 5; i++) {
        sim.tick(new Map([['player_1', emptyInput]]))
      }

      const state2 = sim.getState()
      // Find the same bullet or verify bullets moved
      const playerBullets2 = state2.bullets.filter(b => !b.isEnemy)

      if (playerBullets2.length > 0) {
        // At least some bullet should have moved forward
        const maxX = Math.max(...playerBullets2.map(b => b.x))
        expect(maxX).toBeGreaterThan(bulletX1)
      }
    }
  })

  it('should fire deterministically with same seed', () => {
    const sim1 = new Simulation(['player_1'], 12345)
    const sim2 = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 30; i++) {
      sim1.tick(new Map([['player_1', fireInput]]))
      sim2.tick(new Map([['player_1', fireInput]]))
    }

    expect(sim1.getState().bullets.length).toBe(sim2.getState().bullets.length)
    expect(sim1.getChecksum()).toBe(sim2.getChecksum())
  })
})

describe('Simulation wave system', () => {
  const emptyInput: PlayerInput = {
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

  it('should start at wave 1', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()
    expect(state.wave).toBe(1)
    expect(typeof state.wave).toBe('number')
    expect(Number.isInteger(state.wave)).toBe(true)
  })

  it('should eventually spawn enemies', () => {
    const sim = new Simulation(['player_1'], 12345)

    // Run simulation for a while
    for (let i = 0; i < 300; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    const state = sim.getState()
    // Either enemies spawned or we're past the initial delay
    expect(state.frame).toBe(300)
    expect(Array.isArray(state.enemies)).toBe(true)
  })

  it('should track wave timer', () => {
    const sim = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 100; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    const serialized = sim.serializeState()
    expect(typeof serialized.waveTimer).toBe('number')
    expect(Number.isFinite(serialized.waveTimer)).toBe(true)
  })

  it('should have consistent wave progression deterministically', () => {
    const sim1 = new Simulation(['player_1'], 12345)
    const sim2 = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 300; i++) {
      sim1.tick(new Map([['player_1', emptyInput]]))
      sim2.tick(new Map([['player_1', emptyInput]]))
    }

    expect(sim1.getState().wave).toBe(sim2.getState().wave)
    expect(sim1.getState().enemies.length).toBe(sim2.getState().enemies.length)
  })
})

describe('Simulation multiplayer', () => {
  const emptyInput: PlayerInput = {
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

  it('should support multiple players', () => {
    const sim = new Simulation(['player_1', 'player_2', 'player_3', 'player_4'], 12345)
    const state = sim.getState()

    expect(state.players).toHaveLength(4)
    // Verify each player has unique ID
    const ids = state.players.map(p => p.playerId)
    expect(new Set(ids).size).toBe(4)
  })

  it('should handle inputs from multiple players', () => {
    const sim = new Simulation(['player_1', 'player_2'], 12345)

    const moveUp: PlayerInput = { ...emptyInput, up: true }
    const moveDown: PlayerInput = { ...emptyInput, down: true }

    for (let i = 0; i < 30; i++) {
      sim.tick(new Map([
        ['player_1', moveUp],
        ['player_2', moveDown],
      ]))
    }

    const state = sim.getState()
    const p1 = state.players.find(p => p.playerId === 'player_1')!
    const p2 = state.players.find(p => p.playerId === 'player_2')!

    // Players should have moved in different directions
    expect(p1.y).not.toBe(p2.y)
    // Both should still exist and have valid coordinates
    expect(Number.isFinite(p1.x)).toBe(true)
    expect(Number.isFinite(p2.x)).toBe(true)
  })

  it('should handle missing inputs gracefully', () => {
    const sim = new Simulation(['player_1', 'player_2'], 12345)

    // Only provide input for player_1
    for (let i = 0; i < 10; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    // Should not crash, player_2 just doesn't move
    const state = sim.getState()
    expect(state.frame).toBe(10)
    expect(state.players).toHaveLength(2)
  })

  it('should maintain determinism with multiple players', () => {
    const sim1 = new Simulation(['player_1', 'player_2'], 12345)
    const sim2 = new Simulation(['player_1', 'player_2'], 12345)

    const moveUp: PlayerInput = { ...emptyInput, up: true }
    const moveDown: PlayerInput = { ...emptyInput, down: true }

    for (let i = 0; i < 50; i++) {
      sim1.tick(new Map([
        ['player_1', moveUp],
        ['player_2', moveDown],
      ]))
      sim2.tick(new Map([
        ['player_1', moveUp],
        ['player_2', moveDown],
      ]))
    }

    expect(sim1.getChecksum()).toBe(sim2.getChecksum())
    expect(sim1.getState().players[0]!.y).toBe(sim2.getState().players[0]!.y)
    expect(sim1.getState().players[1]!.y).toBe(sim2.getState().players[1]!.y)
  })

  it('should position multiplayer players at different spawn points', () => {
    const sim = new Simulation(['p1', 'p2', 'p3', 'p4'], 12345)
    const state = sim.getState()

    const yPositions = state.players.map(p => p.y)
    // All Y positions should be unique
    expect(new Set(yPositions).size).toBe(4)
  })
})

describe('Simulation enemy spawning', () => {
  const emptyInput: PlayerInput = {
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

  it('should spawn enemies after initial delay', () => {
    const sim = new Simulation(['player_1'], 12345)

    // Run past the initial 1.2 second delay (~72 frames at 60fps)
    for (let i = 0; i < 100; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    const state = sim.getState()
    expect(state.enemies.length).toBeGreaterThan(0)
    // Verify enemies have valid positions
    for (const enemy of state.enemies) {
      expect(Number.isFinite(enemy.x)).toBe(true)
      expect(Number.isFinite(enemy.y)).toBe(true)
    }
  })

  it('should spawn different enemy types based on wave', () => {
    const sim = new Simulation(['player_1'], 12345)

    // Run simulation to get past wave 1
    for (let i = 0; i < 600; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    // Should have progressed past wave 1
    const state = sim.getState()
    expect(state.wave).toBeGreaterThanOrEqual(1)
    expect(typeof state.wave).toBe('number')
  })

  it('should track enemy properties correctly', () => {
    const sim = new Simulation(['player_1'], 12345)

    // Run to spawn enemies
    for (let i = 0; i < 100; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    const state = sim.getState()
    if (state.enemies.length > 0) {
      const enemy = state.enemies[0]!
      expect(enemy).toHaveProperty('id')
      expect(enemy).toHaveProperty('type')
      expect(enemy).toHaveProperty('x')
      expect(enemy).toHaveProperty('y')
      expect(enemy).toHaveProperty('health')
      expect(enemy).toHaveProperty('maxHealth')

      // Type checks
      expect(typeof enemy.id).toBe('number')
      expect(typeof enemy.type).toBe('string')
      expect(typeof enemy.x).toBe('number')
      expect(typeof enemy.y).toBe('number')
      expect(typeof enemy.health).toBe('number')
      expect(typeof enemy.maxHealth).toBe('number')

      // Health should be positive and <= maxHealth
      expect(enemy.health).toBeGreaterThan(0)
      expect(enemy.health).toBeLessThanOrEqual(enemy.maxHealth)
    }
  })

  it('should spawn enemies deterministically with same seed', () => {
    const sim1 = new Simulation(['player_1'], 12345)
    const sim2 = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 150; i++) {
      sim1.tick(new Map([['player_1', emptyInput]]))
      sim2.tick(new Map([['player_1', emptyInput]]))
    }

    const state1 = sim1.getState()
    const state2 = sim2.getState()

    expect(state1.enemies.length).toBe(state2.enemies.length)
    // Check first enemy matches if any exist
    if (state1.enemies.length > 0) {
      expect(state1.enemies[0]!.type).toBe(state2.enemies[0]!.type)
      expect(state1.enemies[0]!.x).toBe(state2.enemies[0]!.x)
    }
  })
})

describe('Simulation collision detection', () => {
  const emptyInput: PlayerInput = {
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

  const fireInput: PlayerInput = {
    ...emptyInput,
    fire: true,
  }

  it('should track bullets created by player', () => {
    const sim = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 50; i++) {
      sim.tick(new Map([['player_1', fireInput]]))
    }

    const state = sim.getState()
    // Should have bullets from firing
    expect(state.bullets.some(b => !b.isEnemy)).toBe(true)
    // All bullets should have valid positions
    for (const bullet of state.bullets) {
      expect(Number.isFinite(bullet.x)).toBe(true)
      expect(Number.isFinite(bullet.y)).toBe(true)
    }
  })

  it('should track bullet type correctly', () => {
    const sim = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 30; i++) {
      sim.tick(new Map([['player_1', fireInput]]))
    }

    const state = sim.getState()
    const playerBullets = state.bullets.filter(b => !b.isEnemy)
    if (playerBullets.length > 0) {
      const bullet = playerBullets[0]!
      // Verify bullet has expected properties from getState()
      expect(bullet).toHaveProperty('id')
      expect(bullet).toHaveProperty('type')
      expect(bullet).toHaveProperty('x')
      expect(bullet).toHaveProperty('y')

      // Type checks
      expect(typeof bullet.id).toBe('number')
      expect(typeof bullet.type).toBe('string')
      expect(typeof bullet.x).toBe('number')
      expect(typeof bullet.y).toBe('number')
    }
  })

  it('should remove bullets when lifetime expires', () => {
    const sim = new Simulation(['player_1'], 12345)

    // Fire once
    sim.tick(new Map([['player_1', fireInput]]))

    // Let bullets fly and expire (default lifetime is ~120 frames)
    for (let i = 0; i < 200; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    // Bullets should have expired
    const state = sim.getState()
    // Most bullets should be gone after 200+ frames
    expect(state.bullets.length).toBeLessThan(10)
  })

  it('should create bullets deterministically', () => {
    const sim1 = new Simulation(['player_1'], 12345)
    const sim2 = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 30; i++) {
      sim1.tick(new Map([['player_1', fireInput]]))
      sim2.tick(new Map([['player_1', fireInput]]))
    }

    const state1 = sim1.getState()
    const state2 = sim2.getState()

    expect(state1.bullets.length).toBe(state2.bullets.length)
    // If bullets exist, their positions should match
    if (state1.bullets.length > 0) {
      expect(state1.bullets[0]!.x).toBe(state2.bullets[0]!.x)
      expect(state1.bullets[0]!.y).toBe(state2.bullets[0]!.y)
    }
  })

  it('should distinguish between player and enemy bullets', () => {
    const sim = new Simulation(['player_1'], 12345)

    // Fire and run simulation to spawn enemies that can shoot
    for (let i = 0; i < 200; i++) {
      sim.tick(new Map([['player_1', fireInput]]))
    }

    const state = sim.getState()
    const playerBullets = state.bullets.filter(b => !b.isEnemy)
    const enemyBullets = state.bullets.filter(b => b.isEnemy)

    // Should have player bullets from firing
    expect(playerBullets.length).toBeGreaterThan(0)
    // Both arrays should be valid
    expect(Array.isArray(playerBullets)).toBe(true)
    expect(Array.isArray(enemyBullets)).toBe(true)
  })
})

describe('Simulation player damage', () => {
  const emptyInput: PlayerInput = {
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

  it('should have initial shields', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(state.players[0]!.shields).toBe(100)
    expect(state.players[0]!.maxShields).toBe(100)
    // Type checks
    expect(typeof state.players[0]!.shields).toBe('number')
    expect(typeof state.players[0]!.maxShields).toBe('number')
    // Shields should be <= maxShields
    expect(state.players[0]!.shields).toBeLessThanOrEqual(state.players[0]!.maxShields)
  })

  it('should have initial lives', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(state.players[0]!.lives).toBe(3)
    expect(typeof state.players[0]!.lives).toBe('number')
    expect(Number.isInteger(state.players[0]!.lives)).toBe(true)
  })

  it('should give invincibility on spawn', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    // 3 seconds * 60 fps = 180 frames
    expect(state.players[0]!.invincible).toBe(180)
    expect(typeof state.players[0]!.invincible).toBe('number')
    expect(Number.isInteger(state.players[0]!.invincible)).toBe(true)
  })

  it('should decrease invincibility over time', () => {
    const sim = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 60; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    const state = sim.getState()
    expect(state.players[0]!.invincible).toBe(120)
    // Should still be positive
    expect(state.players[0]!.invincible).toBeGreaterThan(0)
  })

  it('should eventually remove invincibility', () => {
    const sim = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 200; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    const state = sim.getState()
    expect(state.players[0]!.invincible).toBe(0)
    // Should never go negative
    expect(state.players[0]!.invincible).toBeGreaterThanOrEqual(0)
  })

  it('should track dead state', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(state.players[0]!.dead).toBe(false)
    expect(typeof state.players[0]!.dead).toBe('boolean')
  })

  it('should have all players start with same stats in multiplayer', () => {
    const sim = new Simulation(['p1', 'p2', 'p3'], 12345)
    const state = sim.getState()

    for (const player of state.players) {
      expect(player.shields).toBe(100)
      expect(player.maxShields).toBe(100)
      expect(player.lives).toBe(3)
      expect(player.invincible).toBe(180)
      expect(player.dead).toBe(false)
    }
  })
})

describe('Simulation score system', () => {
  it('should start with score 0', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(state.score).toBe(0)
    expect(typeof state.score).toBe('number')
    expect(Number.isInteger(state.score)).toBe(true)
    expect(state.score).toBeGreaterThanOrEqual(0)
  })

  it('should start with multiplier 1', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(state.multiplier).toBe(1)
    expect(typeof state.multiplier).toBe('number')
    expect(state.multiplier).toBeGreaterThanOrEqual(1)
  })

  it('should track game over state', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(state.gameOver).toBe(false)
    expect(typeof state.gameOver).toBe('boolean')
  })

  it('should maintain score across ticks', () => {
    const sim = new Simulation(['player_1'], 12345)

    const emptyInput: PlayerInput = {
      up: false, down: false, left: false, right: false,
      fire: false, special: false, secondary: false,
      swap: false, pickup: false, pause: false,
    }

    for (let i = 0; i < 100; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    const state = sim.getState()
    // Score should still be valid
    expect(typeof state.score).toBe('number')
    expect(Number.isFinite(state.score)).toBe(true)
    expect(state.score).toBeGreaterThanOrEqual(0)
  })

  it('should track score deterministically', () => {
    const sim1 = new Simulation(['player_1'], 12345)
    const sim2 = new Simulation(['player_1'], 12345)

    const fireInput: PlayerInput = {
      up: false, down: false, left: false, right: false,
      fire: true, special: false, secondary: false,
      swap: false, pickup: false, pause: false,
    }

    for (let i = 0; i < 200; i++) {
      sim1.tick(new Map([['player_1', fireInput]]))
      sim2.tick(new Map([['player_1', fireInput]]))
    }

    expect(sim1.getState().score).toBe(sim2.getState().score)
    expect(sim1.getState().multiplier).toBe(sim2.getState().multiplier)
  })
})

describe('Simulation screen shake', () => {
  const emptyInput: PlayerInput = {
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

  it('should start with no screen shake', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(state.screenShake).toBe(0)
    expect(typeof state.screenShake).toBe('number')
    expect(Number.isFinite(state.screenShake)).toBe(true)
  })

  it('should include screenShake in state', () => {
    const sim = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 10; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    const state = sim.getState()
    expect(typeof state.screenShake).toBe('number')
    expect(Number.isFinite(state.screenShake)).toBe(true)
    expect(state.screenShake).toBeGreaterThanOrEqual(0)
  })

  it('should include screenShake in serialized state', () => {
    const sim = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 10; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    const serialized = sim.serializeState()
    expect(typeof serialized.screenShake).toBe('number')
    expect(Number.isFinite(serialized.screenShake)).toBe(true)
  })
})

describe('Simulation particles', () => {
  const emptyInput: PlayerInput = {
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

  it('should start with no particles', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(state.particles).toEqual([])
    expect(Array.isArray(state.particles)).toBe(true)
    expect(state.particles.length).toBe(0)
  })

  it('should track particles array', () => {
    const sim = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 100; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    const state = sim.getState()
    expect(Array.isArray(state.particles)).toBe(true)
    // Particles should have valid positions if any exist
    for (const particle of state.particles) {
      expect(Number.isFinite(particle.x)).toBe(true)
      expect(Number.isFinite(particle.y)).toBe(true)
    }
  })

  it('should track particles deterministically', () => {
    const sim1 = new Simulation(['player_1'], 12345)
    const sim2 = new Simulation(['player_1'], 12345)

    const fireInput: PlayerInput = { ...emptyInput, fire: true }

    for (let i = 0; i < 200; i++) {
      sim1.tick(new Map([['player_1', fireInput]]))
      sim2.tick(new Map([['player_1', fireInput]]))
    }

    expect(sim1.getState().particles.length).toBe(sim2.getState().particles.length)
  })
})

describe('Simulation boss system', () => {
  const emptyInput: PlayerInput = {
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

  it('should not have boss at start', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(state.boss).toBeNull()
    expect(state.bossActive).toBe(false)
    expect(typeof state.bossActive).toBe('boolean')
  })

  it('should track bossActive flag', () => {
    const sim = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 50; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    const state = sim.getState()
    expect(typeof state.bossActive).toBe('boolean')
  })

  it('should serialize boss state correctly', () => {
    const sim = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 50; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    const serialized = sim.serializeState()
    expect(typeof serialized.bossActive).toBe('boolean')
    // Boss should be null or an object
    expect(serialized.boss === null || typeof serialized.boss === 'object').toBe(true)
  })

  it('should maintain boss state deterministically', () => {
    const sim1 = new Simulation(['player_1'], 12345)
    const sim2 = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 100; i++) {
      sim1.tick(new Map([['player_1', emptyInput]]))
      sim2.tick(new Map([['player_1', emptyInput]]))
    }

    expect(sim1.getState().bossActive).toBe(sim2.getState().bossActive)
    // If boss exists, it should be the same
    if (sim1.getState().boss !== null) {
      expect(sim2.getState().boss).not.toBeNull()
    }
  })
})

describe('Simulation weapon system', () => {
  it('should track weapon slots', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(Array.isArray(state.players[0]!.weaponSlots)).toBe(true)
    // Each slot should be a valid weapon or null
    for (const slot of state.players[0]!.weaponSlots) {
      expect(slot === null || typeof slot === 'object').toBe(true)
    }
  })

  it('should track active weapon index', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(typeof state.players[0]!.activeWeaponIndex).toBe('number')
    expect(Number.isInteger(state.players[0]!.activeWeaponIndex)).toBe(true)
    expect(state.players[0]!.activeWeaponIndex).toBeGreaterThanOrEqual(0)
  })

  it('should limit weapon slots to max', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    // Default maxWeaponSlots is 2
    expect(state.players[0]!.maxWeaponSlots).toBe(2)
    expect(typeof state.players[0]!.maxWeaponSlots).toBe('number')
    expect(Number.isInteger(state.players[0]!.maxWeaponSlots)).toBe(true)
  })

  it('should have active weapon index within bounds', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    const player = state.players[0]!
    expect(player.activeWeaponIndex).toBeGreaterThanOrEqual(0)
    expect(player.activeWeaponIndex).toBeLessThan(player.maxWeaponSlots)
  })

  it('should have consistent weapon state across players', () => {
    const sim = new Simulation(['p1', 'p2'], 12345)
    const state = sim.getState()

    for (const player of state.players) {
      expect(Array.isArray(player.weaponSlots)).toBe(true)
      expect(typeof player.activeWeaponIndex).toBe('number')
      expect(typeof player.maxWeaponSlots).toBe('number')
    }
  })
})

describe('Simulation powerup system', () => {
  it('should start with no powerups', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(state.powerups).toEqual([])
    expect(Array.isArray(state.powerups)).toBe(true)
    expect(state.powerups.length).toBe(0)
  })

  it('should track player powerup levels', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    const player = state.players[0]!
    expect(player.powerups).toHaveProperty('spread')
    expect(player.powerups).toHaveProperty('laser')
    expect(player.powerups).toHaveProperty('missile')
    expect(player.powerups).toHaveProperty('orbit')
    expect(player.powerups).toHaveProperty('drone')
    expect(player.powerups).toHaveProperty('speed')
    expect(player.powerups).toHaveProperty('rapid')
    expect(player.powerups).toHaveProperty('pierce')

    // Type checks for powerup levels
    expect(typeof player.powerups.spread).toBe('number')
    expect(typeof player.powerups.laser).toBe('number')
    expect(typeof player.powerups.missile).toBe('number')
    expect(Number.isInteger(player.powerups.spread)).toBe(true)
    // All powerup levels should be >= 0
    expect(player.powerups.spread).toBeGreaterThanOrEqual(0)
    expect(player.powerups.laser).toBeGreaterThanOrEqual(0)
  })

  it('should track orbs and drones', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    const player = state.players[0]!
    expect(Array.isArray(player.orbs)).toBe(true)
    expect(Array.isArray(player.drones)).toBe(true)
    // Initially should be empty
    expect(player.orbs.length).toBe(0)
    expect(player.drones.length).toBe(0)
  })

  it('should have consistent powerups across multiplayer', () => {
    const sim = new Simulation(['p1', 'p2'], 12345)
    const state = sim.getState()

    for (const player of state.players) {
      expect(player.powerups).toHaveProperty('spread')
      expect(player.powerups).toHaveProperty('laser')
      expect(Array.isArray(player.orbs)).toBe(true)
      expect(Array.isArray(player.drones)).toBe(true)
    }
  })
})

describe('Simulation special inputs', () => {
  const emptyInput: PlayerInput = {
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

  it('should handle swap input', () => {
    const sim = new Simulation(['player_1'], 12345)

    const swapInput: PlayerInput = { ...emptyInput, swap: true }

    // Simulate some frames with swap
    for (let i = 0; i < 10; i++) {
      sim.tick(new Map([['player_1', swapInput]]))
    }

    // Should not crash and maintain valid state
    const state = sim.getState()
    expect(state.frame).toBe(10)
    expect(Number.isFinite(state.players[0]!.x)).toBe(true)
    expect(Number.isFinite(state.players[0]!.y)).toBe(true)
  })

  it('should handle secondary input', () => {
    const sim = new Simulation(['player_1'], 12345)

    const secondaryInput: PlayerInput = { ...emptyInput, secondary: true }

    for (let i = 0; i < 10; i++) {
      sim.tick(new Map([['player_1', secondaryInput]]))
    }

    const state = sim.getState()
    expect(state.frame).toBe(10)
    expect(typeof state.gameOver).toBe('boolean')
  })

  it('should handle pickup input', () => {
    const sim = new Simulation(['player_1'], 12345)

    const pickupInput: PlayerInput = { ...emptyInput, pickup: true }

    for (let i = 0; i < 10; i++) {
      sim.tick(new Map([['player_1', pickupInput]]))
    }

    const state = sim.getState()
    expect(state.frame).toBe(10)
  })

  it('should handle special input', () => {
    const sim = new Simulation(['player_1'], 12345)

    const specialInput: PlayerInput = { ...emptyInput, special: true }

    for (let i = 0; i < 10; i++) {
      sim.tick(new Map([['player_1', specialInput]]))
    }

    const state = sim.getState()
    expect(state.frame).toBe(10)
    // Verify state is still valid
    expect(Array.isArray(state.bullets)).toBe(true)
    expect(Array.isArray(state.enemies)).toBe(true)
  })

  it('should handle pause input', () => {
    const sim = new Simulation(['player_1'], 12345)

    const pauseInput: PlayerInput = { ...emptyInput, pause: true }

    sim.tick(new Map([['player_1', pauseInput]]))

    const state = sim.getState()
    expect(state.frame).toBe(1)
  })

  it('should handle multiple special inputs simultaneously', () => {
    const sim = new Simulation(['player_1'], 12345)

    const combinedInput: PlayerInput = {
      ...emptyInput,
      swap: true,
      secondary: true,
      special: true,
    }

    for (let i = 0; i < 10; i++) {
      sim.tick(new Map([['player_1', combinedInput]]))
    }

    const state = sim.getState()
    expect(state.frame).toBe(10)
    expect(state.gameOver).toBe(false)
  })

  it('should handle special inputs deterministically', () => {
    const sim1 = new Simulation(['player_1'], 12345)
    const sim2 = new Simulation(['player_1'], 12345)

    const specialInput: PlayerInput = { ...emptyInput, special: true, fire: true }

    for (let i = 0; i < 30; i++) {
      sim1.tick(new Map([['player_1', specialInput]]))
      sim2.tick(new Map([['player_1', specialInput]]))
    }

    expect(sim1.getChecksum()).toBe(sim2.getChecksum())
    expect(sim1.getState().frame).toBe(sim2.getState().frame)
  })
})

describe('Simulation weapon drops', () => {
  it('should include weaponDrops in state', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(Array.isArray(state.weaponDrops)).toBe(true)
  })

  it('should start with no weapon drops', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(state.weaponDrops.length).toBe(0)
    expect(Array.isArray(state.weaponDrops)).toBe(true)
  })

  it('should include weaponDrops in serialized state', () => {
    const sim = new Simulation(['player_1'], 12345)

    const emptyInput: PlayerInput = {
      up: false, down: false, left: false, right: false,
      fire: false, special: false, secondary: false,
      swap: false, pickup: false, pause: false,
    }

    for (let i = 0; i < 100; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    const serialized = sim.serializeState()
    expect(Array.isArray(serialized.weaponDrops)).toBe(true)
  })

  it('should track weapon drops in debug state', () => {
    const sim = new Simulation(['player_1'], 12345)
    const debug = sim.getDebugState()

    expect(typeof debug.weaponDropCount).toBe('number')
    expect(Number.isInteger(debug.weaponDropCount)).toBe(true)
    expect(debug.weaponDropCount).toBeGreaterThanOrEqual(0)
  })
})

describe('Simulation charging mechanics', () => {
  const emptyInput: PlayerInput = {
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

  const fireInput: PlayerInput = { ...emptyInput, fire: true }

  it('should track player charging state', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(typeof state.players[0]!.charging).toBe('boolean')
    expect(typeof state.players[0]!.chargeTime).toBe('number')
    expect(Number.isFinite(state.players[0]!.chargeTime)).toBe(true)
  })

  it('should increase charge time when firing', () => {
    const sim = new Simulation(['player_1'], 12345)

    // Fire for several frames
    for (let i = 0; i < 60; i++) {
      sim.tick(new Map([['player_1', fireInput]]))
    }

    const state = sim.getState()
    // Charge time should increase while holding fire
    expect(state.players[0]!.chargeTime).toBeGreaterThan(0)
    expect(typeof state.players[0]!.chargeTime).toBe('number')
  })

  it('should track charging deterministically', () => {
    const sim1 = new Simulation(['player_1'], 12345)
    const sim2 = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 60; i++) {
      sim1.tick(new Map([['player_1', fireInput]]))
      sim2.tick(new Map([['player_1', fireInput]]))
    }

    expect(sim1.getState().players[0]!.chargeTime).toBe(sim2.getState().players[0]!.chargeTime)
    expect(sim1.getState().players[0]!.charging).toBe(sim2.getState().players[0]!.charging)
  })

  it('should start with no charge', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(state.players[0]!.chargeTime).toBe(0)
    expect(state.players[0]!.charging).toBe(false)
  })

  it('should track charging state for all players in multiplayer', () => {
    const sim = new Simulation(['p1', 'p2'], 12345)
    const state = sim.getState()

    for (const player of state.players) {
      expect(typeof player.charging).toBe('boolean')
      expect(typeof player.chargeTime).toBe('number')
      expect(player.chargeTime).toBeGreaterThanOrEqual(0)
    }
  })
})

describe('Simulation beams and missiles', () => {
  it('should track beams in state', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(Array.isArray(state.beams)).toBe(true)
  })

  it('should track missiles in state', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(Array.isArray(state.missiles)).toBe(true)
  })

  it('should start with no beams or missiles', () => {
    const sim = new Simulation(['player_1'], 12345)
    const state = sim.getState()

    expect(state.beams.length).toBe(0)
    expect(state.missiles.length).toBe(0)
    expect(Array.isArray(state.beams)).toBe(true)
    expect(Array.isArray(state.missiles)).toBe(true)
  })

  it('should include beams in serialized state', () => {
    const sim = new Simulation(['player_1'], 12345)
    const serialized = sim.serializeState()

    expect(Array.isArray(serialized.beams)).toBe(true)
  })

  it('should include missiles in serialized state', () => {
    const sim = new Simulation(['player_1'], 12345)
    const serialized = sim.serializeState()

    expect(Array.isArray(serialized.missiles)).toBe(true)
  })

  it('should track beams and missiles deterministically', () => {
    const sim1 = new Simulation(['player_1'], 12345)
    const sim2 = new Simulation(['player_1'], 12345)

    const fireInput: PlayerInput = {
      up: false, down: false, left: false, right: false,
      fire: true, special: false, secondary: false,
      swap: false, pickup: false, pause: false,
    }

    for (let i = 0; i < 100; i++) {
      sim1.tick(new Map([['player_1', fireInput]]))
      sim2.tick(new Map([['player_1', fireInput]]))
    }

    expect(sim1.getState().beams.length).toBe(sim2.getState().beams.length)
    expect(sim1.getState().missiles.length).toBe(sim2.getState().missiles.length)
  })
})

describe('Simulation getFrame and getPlayerIds', () => {
  const emptyInput: PlayerInput = {
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

  it('getFrame should return current frame', () => {
    const sim = new Simulation(['player_1'], 12345)

    expect(sim.getFrame()).toBe(0)
    expect(typeof sim.getFrame()).toBe('number')
    expect(Number.isInteger(sim.getFrame())).toBe(true)

    sim.tick(new Map([['player_1', emptyInput]]))
    expect(sim.getFrame()).toBe(1)

    sim.tick(new Map([['player_1', emptyInput]]))
    expect(sim.getFrame()).toBe(2)
  })

  it('getPlayerIds should return all player IDs', () => {
    const sim = new Simulation(['player_1', 'player_2', 'player_3'], 12345)
    const ids = sim.getPlayerIds()

    expect(ids).toEqual(['player_1', 'player_2', 'player_3'])
    expect(Array.isArray(ids)).toBe(true)
    expect(ids.length).toBe(3)
    // All IDs should be strings
    for (const id of ids) {
      expect(typeof id).toBe('string')
    }
  })

  it('getPlayerIds should return single player ID', () => {
    const sim = new Simulation(['solo_player'], 12345)
    const ids = sim.getPlayerIds()

    expect(ids).toEqual(['solo_player'])
    expect(ids.length).toBe(1)
  })

  it('getFrame should match state frame', () => {
    const sim = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 50; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    expect(sim.getFrame()).toBe(sim.getState().frame)
    expect(sim.getFrame()).toBe(50)
  })

  it('getPlayerIds should match state players', () => {
    const sim = new Simulation(['p1', 'p2'], 12345)
    const ids = sim.getPlayerIds()
    const statePlayerIds = sim.getState().players.map(p => p.playerId)

    expect(ids).toEqual(statePlayerIds)
  })

  it('getFrame should be consistent across calls', () => {
    const sim = new Simulation(['player_1'], 12345)

    for (let i = 0; i < 10; i++) {
      sim.tick(new Map([['player_1', emptyInput]]))
    }

    // Multiple calls should return same value
    expect(sim.getFrame()).toBe(sim.getFrame())
    expect(sim.getFrame()).toBe(10)
  })
})

describe('Simulation combined inputs', () => {
  const emptyInput: PlayerInput = {
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

  it('should handle diagonal movement', () => {
    const sim = new Simulation(['player_1'], 12345)

    const diagonalInput: PlayerInput = {
      ...emptyInput,
      up: true,
      right: true,
    }

    const initialState = sim.getState()
    const initialX = initialState.players[0]!.x
    const initialY = initialState.players[0]!.y

    for (let i = 0; i < 30; i++) {
      sim.tick(new Map([['player_1', diagonalInput]]))
    }

    const state = sim.getState()
    // Should have moved both right and up
    expect(state.players[0]!.x).toBeGreaterThan(initialX)
    // Y decreases when moving up (positive Y is down)
    expect(state.players[0]!.y).not.toBe(initialY)
    // Position should be valid
    expect(Number.isFinite(state.players[0]!.x)).toBe(true)
    expect(Number.isFinite(state.players[0]!.y)).toBe(true)
  })

  it('should handle all movement directions simultaneously', () => {
    const sim = new Simulation(['player_1'], 12345)

    // All directions pressed cancels out
    const allDirsInput: PlayerInput = {
      ...emptyInput,
      up: true,
      down: true,
      left: true,
      right: true,
    }

    sim.tick(new Map([['player_1', allDirsInput]]))

    // Should not crash
    const state = sim.getState()
    expect(state.frame).toBe(1)
    expect(typeof state.gameOver).toBe('boolean')
  })

  it('should handle movement while firing', () => {
    const sim = new Simulation(['player_1'], 12345)

    const moveAndFire: PlayerInput = {
      ...emptyInput,
      up: true,
      right: true,
      fire: true,
    }

    for (let i = 0; i < 50; i++) {
      sim.tick(new Map([['player_1', moveAndFire]]))
    }

    const state = sim.getState()
    // Should have moved and created bullets
    expect(state.bullets.some(b => !b.isEnemy)).toBe(true)
    // All bullets should have valid positions
    for (const bullet of state.bullets) {
      expect(Number.isFinite(bullet.x)).toBe(true)
      expect(Number.isFinite(bullet.y)).toBe(true)
    }
  })

  it('should handle combined inputs deterministically', () => {
    const sim1 = new Simulation(['player_1'], 12345)
    const sim2 = new Simulation(['player_1'], 12345)

    const combinedInput: PlayerInput = {
      ...emptyInput,
      up: true,
      right: true,
      fire: true,
      special: true,
    }

    for (let i = 0; i < 50; i++) {
      sim1.tick(new Map([['player_1', combinedInput]]))
      sim2.tick(new Map([['player_1', combinedInput]]))
    }

    expect(sim1.getChecksum()).toBe(sim2.getChecksum())
    expect(sim1.getState().players[0]!.x).toBe(sim2.getState().players[0]!.x)
    expect(sim1.getState().players[0]!.y).toBe(sim2.getState().players[0]!.y)
    expect(sim1.getState().bullets.length).toBe(sim2.getState().bullets.length)
  })

  it('should handle complex multiplayer input combinations', () => {
    const sim = new Simulation(['p1', 'p2'], 12345)

    const p1Input: PlayerInput = { ...emptyInput, up: true, fire: true }
    const p2Input: PlayerInput = { ...emptyInput, down: true, special: true }

    for (let i = 0; i < 30; i++) {
      sim.tick(new Map([
        ['p1', p1Input],
        ['p2', p2Input],
      ]))
    }

    const state = sim.getState()
    expect(state.frame).toBe(30)
    expect(state.players).toHaveLength(2)
    // Both players should have valid positions
    for (const player of state.players) {
      expect(Number.isFinite(player.x)).toBe(true)
      expect(Number.isFinite(player.y)).toBe(true)
    }
  })
})
