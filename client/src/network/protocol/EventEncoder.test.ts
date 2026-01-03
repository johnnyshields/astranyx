import { describe, it, expect } from 'vitest'
import {
  encodeEvents,
  decodeEvents,
  calculateEventsSize,
} from './EventEncoder'
import type { GameEvent, DamageEvent, DeathEvent, RespawnEvent, PickupEvent, WeaponPickupEvent, EnemyDamageEvent } from '../types'

function createPlayerOrder(): Map<string, number> {
  return new Map([
    ['player1', 0],
    ['player2', 1],
    ['player3', 2],
  ])
}

const playerIdByIndex = ['player1', 'player2', 'player3']

describe('EventEncoder', () => {
  describe('calculateEventsSize', () => {
    it('should return 1 for empty events', () => {
      expect(calculateEventsSize([])).toBe(1) // Just count byte
    })

    it('should calculate size for damage event', () => {
      const events: GameEvent[] = [
        { type: 'damage', playerId: 'player1', amount: 10, newShields: 90, newLives: 3 },
      ]
      const size = calculateEventsSize(events)
      expect(size).toBe(1 + 7) // count + damage event size
    })

    it('should calculate size for death event', () => {
      const events: GameEvent[] = [
        { type: 'death', playerId: 'player1' },
      ]
      const size = calculateEventsSize(events)
      expect(size).toBe(1 + 2) // count + death event size
    })

    it('should calculate size for respawn event', () => {
      const events: GameEvent[] = [
        { type: 'respawn', playerId: 'player1' },
      ]
      const size = calculateEventsSize(events)
      expect(size).toBe(1 + 2) // count + respawn event size
    })

    it('should calculate size for pickup event', () => {
      const events: GameEvent[] = [
        { type: 'pickup', playerId: 'player1', pickupId: 123 },
      ]
      const size = calculateEventsSize(events)
      expect(size).toBe(1 + 5) // count + pickup event size
    })

    it('should calculate size for weapon_pickup event', () => {
      const events: GameEvent[] = [
        { type: 'weapon_pickup', playerId: 'player1', dropId: 456 },
      ]
      const size = calculateEventsSize(events)
      expect(size).toBe(1 + 5) // count + weapon_pickup event size
    })

    it('should calculate size for enemy_damage event', () => {
      const events: GameEvent[] = [
        { type: 'enemy_damage', ownerId: 'player1', enemyId: 789, amount: 50, newHealth: 50, killed: false },
      ]
      const size = calculateEventsSize(events)
      expect(size).toBe(1 + 10) // count + enemy_damage event size
    })

    it('should calculate size for multiple events', () => {
      const events: GameEvent[] = [
        { type: 'death', playerId: 'player1' },
        { type: 'death', playerId: 'player2' },
      ]
      const size = calculateEventsSize(events)
      expect(size).toBe(1 + 2 + 2) // count + 2 death events
    })
  })

  describe('encodeEvents / decodeEvents', () => {
    const playerOrder = createPlayerOrder()

    function encodeAndDecode(events: GameEvent[]): GameEvent[] {
      const size = calculateEventsSize(events)
      const buffer = new ArrayBuffer(size)
      const view = new DataView(buffer)

      encodeEvents(view, 0, events, playerOrder)
      return decodeEvents(view, 0, size, playerIdByIndex)
    }

    it('should encode and decode empty events array', () => {
      const decoded = encodeAndDecode([])
      expect(decoded).toEqual([])
    })

    it('should encode and decode damage event', () => {
      const events: GameEvent[] = [
        { type: 'damage', playerId: 'player1', amount: 50, newShields: 50, newLives: 2 },
      ]

      const decoded = encodeAndDecode(events)

      expect(decoded.length).toBe(1)
      expect(decoded[0]!.type).toBe('damage')
      const damage = decoded[0]! as DamageEvent
      expect(damage.playerId).toBe('player1')
      expect(damage.amount).toBe(50)
      expect(damage.newShields).toBe(50)
      expect(damage.newLives).toBe(2)
    })

    it('should encode and decode death event', () => {
      const events: GameEvent[] = [
        { type: 'death', playerId: 'player2' },
      ]

      const decoded = encodeAndDecode(events)

      expect(decoded.length).toBe(1)
      expect(decoded[0]!.type).toBe('death')
      const death = decoded[0]! as DeathEvent
      expect(death.playerId).toBe('player2')
    })

    it('should encode and decode respawn event', () => {
      const events: GameEvent[] = [
        { type: 'respawn', playerId: 'player3' },
      ]

      const decoded = encodeAndDecode(events)

      expect(decoded.length).toBe(1)
      expect(decoded[0]!.type).toBe('respawn')
      const respawn = decoded[0]! as RespawnEvent
      expect(respawn.playerId).toBe('player3')
    })

    it('should encode and decode pickup event', () => {
      const events: GameEvent[] = [
        { type: 'pickup', playerId: 'player1', pickupId: 12345 },
      ]

      const decoded = encodeAndDecode(events)

      expect(decoded.length).toBe(1)
      expect(decoded[0]!.type).toBe('pickup')
      const pickup = decoded[0]! as PickupEvent
      expect(pickup.playerId).toBe('player1')
      expect(pickup.pickupId).toBe(12345)
    })

    it('should encode and decode weapon_pickup event', () => {
      const events: GameEvent[] = [
        { type: 'weapon_pickup', playerId: 'player2', dropId: 67890 },
      ]

      const decoded = encodeAndDecode(events)

      expect(decoded.length).toBe(1)
      expect(decoded[0]!.type).toBe('weapon_pickup')
      const weaponPickup = decoded[0]! as WeaponPickupEvent
      expect(weaponPickup.playerId).toBe('player2')
      expect(weaponPickup.dropId).toBe(67890)
    })

    it('should encode and decode enemy_damage event', () => {
      const events: GameEvent[] = [
        { type: 'enemy_damage', ownerId: 'player1', enemyId: 999, amount: 100, newHealth: 0, killed: true },
      ]

      const decoded = encodeAndDecode(events)

      expect(decoded.length).toBe(1)
      expect(decoded[0]!.type).toBe('enemy_damage')
      const enemyDamage = decoded[0]! as EnemyDamageEvent
      expect(enemyDamage.ownerId).toBe('player1')
      expect(enemyDamage.enemyId).toBe(999)
      expect(enemyDamage.amount).toBe(100)
      expect(enemyDamage.newHealth).toBe(0)
      expect(enemyDamage.killed).toBe(true)
    })

    it('should encode and decode enemy_damage event with killed=false', () => {
      const events: GameEvent[] = [
        { type: 'enemy_damage', ownerId: 'player2', enemyId: 500, amount: 25, newHealth: 75, killed: false },
      ]

      const decoded = encodeAndDecode(events)
      const enemyDamage = decoded[0]! as EnemyDamageEvent
      expect(enemyDamage.killed).toBe(false)
    })

    it('should encode and decode multiple events', () => {
      const events: GameEvent[] = [
        { type: 'damage', playerId: 'player1', amount: 10, newShields: 90, newLives: 3 },
        { type: 'death', playerId: 'player2' },
        { type: 'respawn', playerId: 'player2' },
        { type: 'pickup', playerId: 'player3', pickupId: 100 },
      ]

      const decoded = encodeAndDecode(events)

      expect(decoded.length).toBe(4)
      expect(decoded[0]!.type).toBe('damage')
      expect(decoded[1]!.type).toBe('death')
      expect(decoded[2]!.type).toBe('respawn')
      expect(decoded[3]!.type).toBe('pickup')
    })

    it('should handle large pickup IDs (24-bit)', () => {
      const events: GameEvent[] = [
        { type: 'pickup', playerId: 'player1', pickupId: 0xFFFFFF }, // Max 24-bit
      ]

      const decoded = encodeAndDecode(events)
      const pickup = decoded[0] as PickupEvent
      expect(pickup.pickupId).toBe(0xFFFFFF)
    })

    it('should handle large drop IDs (24-bit)', () => {
      const events: GameEvent[] = [
        { type: 'weapon_pickup', playerId: 'player1', dropId: 0xABCDEF },
      ]

      const decoded = encodeAndDecode(events)
      const weaponPickup = decoded[0] as WeaponPickupEvent
      expect(weaponPickup.dropId).toBe(0xABCDEF)
    })

    it('should handle large enemy IDs (24-bit)', () => {
      const events: GameEvent[] = [
        { type: 'enemy_damage', ownerId: 'player1', enemyId: 0x123456, amount: 50, newHealth: 50, killed: false },
      ]

      const decoded = encodeAndDecode(events)
      const enemyDamage = decoded[0] as EnemyDamageEvent
      expect(enemyDamage.enemyId).toBe(0x123456)
    })

    it('should handle large damage amounts (16-bit)', () => {
      const events: GameEvent[] = [
        { type: 'damage', playerId: 'player1', amount: 65535, newShields: 65535, newLives: 255 },
      ]

      const decoded = encodeAndDecode(events)
      const damage = decoded[0] as DamageEvent
      expect(damage.amount).toBe(65535)
      expect(damage.newShields).toBe(65535)
      expect(damage.newLives).toBe(255)
    })

    it('should handle unknown player gracefully', () => {
      const unknownPlayerOrder = new Map([['player1', 0]])
      const events: GameEvent[] = [
        { type: 'death', playerId: 'unknown' },
      ]

      const size = calculateEventsSize(events)
      const buffer = new ArrayBuffer(size)
      const view = new DataView(buffer)

      encodeEvents(view, 0, events, unknownPlayerOrder)
      const decoded = decodeEvents(view, 0, size, ['player1'])

      // Unknown player maps to index 0, which decodes to player1
      expect((decoded[0] as DeathEvent).playerId).toBe('player1')
    })

    it('should handle missing player index gracefully', () => {
      const events: GameEvent[] = [
        { type: 'death', playerId: 'player3' },
      ]

      const size = calculateEventsSize(events)
      const buffer = new ArrayBuffer(size)
      const view = new DataView(buffer)

      encodeEvents(view, 0, events, playerOrder)
      // Decode with shorter player list
      const decoded = decodeEvents(view, 0, size, ['player1'])

      // Should create fallback player ID
      expect((decoded[0] as DeathEvent).playerId).toBe('player_2')
    })
  })

  describe('offset handling', () => {
    const playerOrder = createPlayerOrder()

    it('should return correct offset after encoding', () => {
      const events: GameEvent[] = [
        { type: 'death', playerId: 'player1' },
      ]

      const buffer = new ArrayBuffer(100)
      const view = new DataView(buffer)

      const newOffset = encodeEvents(view, 10, events, playerOrder)

      // 1 byte count + 2 bytes death event = 3 bytes
      expect(newOffset).toBe(10 + 3)
    })

    it('should handle non-zero starting offset', () => {
      const events: GameEvent[] = [
        { type: 'respawn', playerId: 'player2' },
      ]

      const buffer = new ArrayBuffer(100)
      const view = new DataView(buffer)

      // Write some data before
      view.setUint32(0, 0xDEADBEEF)

      const startOffset = 4
      encodeEvents(view, startOffset, events, playerOrder)
      const decoded = decodeEvents(view, startOffset, 100 - startOffset, playerIdByIndex)

      expect(decoded.length).toBe(1)
      expect(decoded[0]!.type).toBe('respawn')
    })
  })

  describe('boundary conditions', () => {
    const playerOrder = createPlayerOrder()

    it('should handle exactly 255 events', () => {
      const events: GameEvent[] = []
      for (let i = 0; i < 255; i++) {
        events.push({ type: 'death', playerId: 'player1' })
      }

      const size = calculateEventsSize(events)
      const buffer = new ArrayBuffer(size)
      const view = new DataView(buffer)

      encodeEvents(view, 0, events, playerOrder)
      const decoded = decodeEvents(view, 0, size, playerIdByIndex)

      expect(decoded.length).toBe(255)
    })

    it('should truncate to 255 events if more provided', () => {
      const events: GameEvent[] = []
      for (let i = 0; i < 300; i++) {
        events.push({ type: 'death', playerId: 'player1' })
      }

      // Calculate size only considers 255
      const size = calculateEventsSize(events.slice(0, 255)) + 45 * 2 // Extra buffer space (won't be used)
      const buffer = new ArrayBuffer(size)
      const view = new DataView(buffer)

      encodeEvents(view, 0, events, playerOrder)
      const decoded = decodeEvents(view, 0, size, playerIdByIndex)

      expect(decoded.length).toBe(255)
    })

    it('should handle zero amount in damage', () => {
      const events: GameEvent[] = [
        { type: 'damage', playerId: 'player1', amount: 0, newShields: 0, newLives: 0 },
      ]

      const size = calculateEventsSize(events)
      const buffer = new ArrayBuffer(size)
      const view = new DataView(buffer)

      encodeEvents(view, 0, events, playerOrder)
      const decoded = decodeEvents(view, 0, size, playerIdByIndex)

      const damage = decoded[0] as DamageEvent
      expect(damage.amount).toBe(0)
      expect(damage.newShields).toBe(0)
      expect(damage.newLives).toBe(0)
    })
  })
})
