/**
 * EventEncoder - Binary encoding for GameEvent messages
 *
 * Event format:
 * [1 byte type] [payload...]
 *
 * Event types:
 * 0x0 = damage (7 bytes)
 * 0x1 = death (2 bytes)
 * 0x2 = respawn (2 bytes)
 * 0x3 = pickup (5 bytes)
 * 0x4 = weapon_pickup (5 bytes)
 * 0x5 = enemy_damage (10 bytes)
 */

import type { GameEvent, DamageEvent, DeathEvent, RespawnEvent, PickupEvent, WeaponPickupEvent, EnemyDamageEvent } from '../types.ts'

// Event type IDs
const EVENT_TYPE_DAMAGE = 0x0
const EVENT_TYPE_DEATH = 0x1
const EVENT_TYPE_RESPAWN = 0x2
const EVENT_TYPE_PICKUP = 0x3
const EVENT_TYPE_WEAPON_PICKUP = 0x4
const EVENT_TYPE_ENEMY_DAMAGE = 0x5

// Event sizes (including type byte)
const EVENT_SIZE_DAMAGE = 7
const EVENT_SIZE_DEATH = 2
const EVENT_SIZE_RESPAWN = 2
const EVENT_SIZE_PICKUP = 5
const EVENT_SIZE_WEAPON_PICKUP = 5
const EVENT_SIZE_ENEMY_DAMAGE = 10

/**
 * Calculate total size needed for events array
 */
export function calculateEventsSize(events: GameEvent[]): number {
  let size = 1 // Event count byte
  for (const event of events) {
    size += getEventSize(event)
  }
  return size
}

/**
 * Get size of a single event
 */
function getEventSize(event: GameEvent): number {
  switch (event.type) {
    case 'damage': return EVENT_SIZE_DAMAGE
    case 'death': return EVENT_SIZE_DEATH
    case 'respawn': return EVENT_SIZE_RESPAWN
    case 'pickup': return EVENT_SIZE_PICKUP
    case 'weapon_pickup': return EVENT_SIZE_WEAPON_PICKUP
    case 'enemy_damage': return EVENT_SIZE_ENEMY_DAMAGE
    default: return 0
  }
}

/**
 * Encode events array to binary
 * @param view DataView to write to
 * @param offset Starting offset
 * @param events Events to encode
 * @param playerOrder Map of player ID to index
 * @returns New offset after writing
 */
export function encodeEvents(
  view: DataView,
  offset: number,
  events: GameEvent[],
  playerOrder: Map<string, number>
): number {
  // Event count (max 255 events per frame)
  view.setUint8(offset++, Math.min(events.length, 255))

  for (const event of events.slice(0, 255)) {
    offset = encodeEvent(view, offset, event, playerOrder)
  }

  return offset
}

/**
 * Encode a single event
 */
function encodeEvent(
  view: DataView,
  offset: number,
  event: GameEvent,
  playerOrder: Map<string, number>
): number {
  switch (event.type) {
    case 'damage':
      return encodeDamageEvent(view, offset, event, playerOrder)
    case 'death':
      return encodeDeathEvent(view, offset, event, playerOrder)
    case 'respawn':
      return encodeRespawnEvent(view, offset, event, playerOrder)
    case 'pickup':
      return encodePickupEvent(view, offset, event, playerOrder)
    case 'weapon_pickup':
      return encodeWeaponPickupEvent(view, offset, event, playerOrder)
    case 'enemy_damage':
      return encodeEnemyDamageEvent(view, offset, event, playerOrder)
    default:
      return offset
  }
}

function encodeDamageEvent(
  view: DataView,
  offset: number,
  event: DamageEvent,
  playerOrder: Map<string, number>
): number {
  view.setUint8(offset++, EVENT_TYPE_DAMAGE)
  view.setUint8(offset++, playerOrder.get(event.playerId) ?? 0)
  view.setUint16(offset, event.amount, true); offset += 2
  view.setUint16(offset, event.newShields, true); offset += 2
  view.setUint8(offset++, event.newLives)
  return offset
}

function encodeDeathEvent(
  view: DataView,
  offset: number,
  event: DeathEvent,
  playerOrder: Map<string, number>
): number {
  view.setUint8(offset++, EVENT_TYPE_DEATH)
  view.setUint8(offset++, playerOrder.get(event.playerId) ?? 0)
  return offset
}

function encodeRespawnEvent(
  view: DataView,
  offset: number,
  event: RespawnEvent,
  playerOrder: Map<string, number>
): number {
  view.setUint8(offset++, EVENT_TYPE_RESPAWN)
  view.setUint8(offset++, playerOrder.get(event.playerId) ?? 0)
  return offset
}

function encodePickupEvent(
  view: DataView,
  offset: number,
  event: PickupEvent,
  playerOrder: Map<string, number>
): number {
  view.setUint8(offset++, EVENT_TYPE_PICKUP)
  view.setUint8(offset++, playerOrder.get(event.playerId) ?? 0)
  // 24-bit pickup ID (little-endian)
  view.setUint8(offset++, event.pickupId & 0xFF)
  view.setUint8(offset++, (event.pickupId >> 8) & 0xFF)
  view.setUint8(offset++, (event.pickupId >> 16) & 0xFF)
  return offset
}

function encodeWeaponPickupEvent(
  view: DataView,
  offset: number,
  event: WeaponPickupEvent,
  playerOrder: Map<string, number>
): number {
  view.setUint8(offset++, EVENT_TYPE_WEAPON_PICKUP)
  view.setUint8(offset++, playerOrder.get(event.playerId) ?? 0)
  // 24-bit drop ID (little-endian)
  view.setUint8(offset++, event.dropId & 0xFF)
  view.setUint8(offset++, (event.dropId >> 8) & 0xFF)
  view.setUint8(offset++, (event.dropId >> 16) & 0xFF)
  return offset
}

function encodeEnemyDamageEvent(
  view: DataView,
  offset: number,
  event: EnemyDamageEvent,
  playerOrder: Map<string, number>
): number {
  view.setUint8(offset++, EVENT_TYPE_ENEMY_DAMAGE)
  view.setUint8(offset++, playerOrder.get(event.ownerId) ?? 0)
  // 24-bit enemy ID (little-endian)
  view.setUint8(offset++, event.enemyId & 0xFF)
  view.setUint8(offset++, (event.enemyId >> 8) & 0xFF)
  view.setUint8(offset++, (event.enemyId >> 16) & 0xFF)
  view.setUint16(offset, event.amount, true); offset += 2
  view.setUint16(offset, event.newHealth, true); offset += 2
  view.setUint8(offset++, event.killed ? 1 : 0)
  return offset
}

/**
 * Decode events array from binary
 * @param view DataView to read from
 * @param offset Starting offset
 * @param maxLength Maximum bytes to read
 * @param playerIdByIndex Array mapping index to player ID
 * @returns Decoded events array
 */
export function decodeEvents(
  view: DataView,
  offset: number,
  maxLength: number,
  playerIdByIndex: string[]
): GameEvent[] {
  const events: GameEvent[] = []
  const endOffset = offset + maxLength

  if (offset >= endOffset) return events

  const count = view.getUint8(offset++)

  for (let i = 0; i < count && offset < endOffset; i++) {
    const eventType = view.getUint8(offset++)
    const result = decodeEvent(view, offset - 1, eventType, playerIdByIndex)
    if (result.event) {
      events.push(result.event)
    }
    offset = result.newOffset
  }

  return events
}

function decodeEvent(
  view: DataView,
  offset: number,
  eventType: number,
  playerIdByIndex: string[]
): { event: GameEvent | null; newOffset: number } {
  offset++ // Skip type byte (already read)

  switch (eventType) {
    case EVENT_TYPE_DAMAGE: {
      const playerIndex = view.getUint8(offset++)
      const amount = view.getUint16(offset, true); offset += 2
      const newShields = view.getUint16(offset, true); offset += 2
      const newLives = view.getUint8(offset++)
      return {
        event: {
          type: 'damage',
          playerId: playerIdByIndex[playerIndex] ?? `player_${playerIndex}`,
          amount,
          newShields,
          newLives,
        },
        newOffset: offset,
      }
    }

    case EVENT_TYPE_DEATH: {
      const playerIndex = view.getUint8(offset++)
      return {
        event: {
          type: 'death',
          playerId: playerIdByIndex[playerIndex] ?? `player_${playerIndex}`,
        },
        newOffset: offset,
      }
    }

    case EVENT_TYPE_RESPAWN: {
      const playerIndex = view.getUint8(offset++)
      return {
        event: {
          type: 'respawn',
          playerId: playerIdByIndex[playerIndex] ?? `player_${playerIndex}`,
        },
        newOffset: offset,
      }
    }

    case EVENT_TYPE_PICKUP: {
      const playerIndex = view.getUint8(offset++)
      const pickupId = view.getUint8(offset++) |
                       (view.getUint8(offset++) << 8) |
                       (view.getUint8(offset++) << 16)
      return {
        event: {
          type: 'pickup',
          playerId: playerIdByIndex[playerIndex] ?? `player_${playerIndex}`,
          pickupId,
        },
        newOffset: offset,
      }
    }

    case EVENT_TYPE_WEAPON_PICKUP: {
      const playerIndex = view.getUint8(offset++)
      const dropId = view.getUint8(offset++) |
                     (view.getUint8(offset++) << 8) |
                     (view.getUint8(offset++) << 16)
      return {
        event: {
          type: 'weapon_pickup',
          playerId: playerIdByIndex[playerIndex] ?? `player_${playerIndex}`,
          dropId,
        },
        newOffset: offset,
      }
    }

    case EVENT_TYPE_ENEMY_DAMAGE: {
      const ownerIndex = view.getUint8(offset++)
      const enemyId = view.getUint8(offset++) |
                      (view.getUint8(offset++) << 8) |
                      (view.getUint8(offset++) << 16)
      const amount = view.getUint16(offset, true); offset += 2
      const newHealth = view.getUint16(offset, true); offset += 2
      const killed = view.getUint8(offset++) === 1
      return {
        event: {
          type: 'enemy_damage',
          ownerId: playerIdByIndex[ownerIndex] ?? `player_${ownerIndex}`,
          enemyId,
          amount,
          newHealth,
          killed,
        },
        newOffset: offset,
      }
    }

    default:
      return { event: null, newOffset: offset }
  }
}
