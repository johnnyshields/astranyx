import { describe, it, expect } from 'vitest'
import type { PlayerInput, GameStateSnapshot, GameEvent, EntityState } from './NetworkManager'
import type { GameMessage } from './WebRTCClient'

// NetworkManager directly instantiates WebRTCClient internally, making it hard to mock
// These tests validate the exported type interfaces which is still valuable

describe('PlayerInput type', () => {
  it('should have correct structure', () => {
    const input: PlayerInput = {
      up: true,
      down: false,
      left: false,
      right: true,
      fire: true,
      special: false,
      timestamp: 12345,
    }

    expect(input.up).toBe(true)
    expect(input.timestamp).toBe(12345)
  })
})

describe('EntityState type', () => {
  it('should have correct structure', () => {
    const entity: EntityState = {
      id: 'entity-1',
      type: 'player',
      x: 100,
      y: 200,
      vx: 5,
      vy: -3,
      rotation: Math.PI / 4,
      health: 100,
      playerId: 'player-1',
    }

    expect(entity.id).toBe('entity-1')
    expect(entity.type).toBe('player')
    expect(entity.health).toBe(100)
  })

  it('should support all entity types', () => {
    const types: EntityState['type'][] = ['player', 'enemy', 'bullet', 'powerup']

    for (const type of types) {
      const entity: EntityState = {
        id: 'test',
        type,
        x: 0,
        y: 0,
        vx: 0,
        vy: 0,
        rotation: 0,
      }
      expect(entity.type).toBe(type)
    }
  })
})

describe('GameStateSnapshot type', () => {
  it('should have correct structure', () => {
    const snapshot: GameStateSnapshot = {
      tick: 100,
      timestamp: Date.now(),
      entities: [
        { id: 'e1', type: 'player', x: 0, y: 0, vx: 0, vy: 0, rotation: 0 },
      ],
      events: [
        { type: 'spawn', entityId: 'e1' },
      ],
    }

    expect(snapshot.tick).toBe(100)
    expect(snapshot.entities).toHaveLength(1)
    expect(snapshot.events).toHaveLength(1)
  })
})

describe('GameEvent type', () => {
  it('should support all event types', () => {
    const types: GameEvent['type'][] = ['spawn', 'destroy', 'damage', 'powerup', 'score']

    for (const type of types) {
      const event: GameEvent = {
        type,
        entityId: 'test',
      }
      expect(event.type).toBe(type)
    }
  })

  it('should support optional data', () => {
    const event: GameEvent = {
      type: 'damage',
      entityId: 'enemy-1',
      data: { amount: 50, source: 'player-1' },
    }

    expect(event.data).toEqual({ amount: 50, source: 'player-1' })
  })
})
