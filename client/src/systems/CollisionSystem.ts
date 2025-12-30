/**
 * Collision result types
 */
export interface CollisionResult {
  type: 'bullet_enemy' | 'bullet_boss' | 'beam_enemy' | 'beam_boss' |
        'missile_enemy' | 'missile_boss' | 'orb_enemy' | 'orb_bullet' |
        'enemy_bullet_player' | 'enemy_player'
  entityA: number  // ID of first entity
  entityB: number  // ID of second entity
  damage: number
}

/**
 * Collision shape types
 */
export type CollisionShape =
  | { type: 'circle'; radius: number }
  | { type: 'box'; halfWidth: number; halfHeight: number }
  | { type: 'beam'; direction: 'right' | 'left'; height: number }

/**
 * Interface for collidable entities
 */
export interface CollidableEntity {
  id: number
  x: number  // World position
  y: number
  shape: CollisionShape
  layer: CollisionLayer
  damage?: number
  pierce?: number
  hitEntities?: Set<number>
}

/**
 * Collision layers determine what can collide with what
 */
export type CollisionLayer =
  | 'player_bullet'
  | 'enemy_bullet'
  | 'player'
  | 'enemy'
  | 'boss'
  | 'orb'
  | 'beam'
  | 'missile'

/**
 * Collision matrix defines which layers can collide
 */
const COLLISION_MATRIX: Record<CollisionLayer, CollisionLayer[]> = {
  player_bullet: ['enemy', 'boss'],
  enemy_bullet: ['player'],
  player: ['enemy', 'enemy_bullet'],
  enemy: ['player_bullet', 'player', 'beam', 'missile', 'orb'],
  boss: ['player_bullet', 'beam', 'missile'],
  orb: ['enemy', 'enemy_bullet'],
  beam: ['enemy', 'boss'],
  missile: ['enemy', 'boss'],
}

/**
 * Check if two collision layers can interact
 */
export function canCollide(layerA: CollisionLayer, layerB: CollisionLayer): boolean {
  return COLLISION_MATRIX[layerA]?.includes(layerB) ?? false
}

/**
 * Circle vs circle collision
 */
export function circleVsCircle(
  x1: number, y1: number, r1: number,
  x2: number, y2: number, r2: number
): boolean {
  const dx = x2 - x1
  const dy = y2 - y1
  const distSq = dx * dx + dy * dy
  const radiusSum = r1 + r2
  return distSq < radiusSum * radiusSum
}

/**
 * Box vs box collision (AABB)
 */
export function boxVsBox(
  x1: number, y1: number, hw1: number, hh1: number,
  x2: number, y2: number, hw2: number, hh2: number
): boolean {
  return (
    Math.abs(x1 - x2) < hw1 + hw2 &&
    Math.abs(y1 - y2) < hh1 + hh2
  )
}

/**
 * Circle vs box collision
 */
export function circleVsBox(
  cx: number, cy: number, r: number,
  bx: number, by: number, hw: number, hh: number
): boolean {
  // Find closest point on box to circle center
  const closestX = Math.max(bx - hw, Math.min(cx, bx + hw))
  const closestY = Math.max(by - hh, Math.min(cy, by + hh))

  const dx = cx - closestX
  const dy = cy - closestY

  return dx * dx + dy * dy < r * r
}

/**
 * Point in box check
 */
export function pointInBox(
  px: number, py: number,
  bx: number, by: number, hw: number, hh: number
): boolean {
  return Math.abs(px - bx) < hw && Math.abs(py - by) < hh
}

/**
 * Beam collision (hits everything to the right within height)
 */
export function beamHits(
  beamX: number, beamY: number, beamHeight: number,
  targetX: number, targetY: number, targetRadius: number
): boolean {
  // Target must be to the right of beam origin
  if (targetX <= beamX) return false
  // Target must be within beam height
  return Math.abs(targetY - beamY) < beamHeight + targetRadius
}

/**
 * Generic shape vs shape collision
 */
export function shapesCollide(
  x1: number, y1: number, shape1: CollisionShape,
  x2: number, y2: number, shape2: CollisionShape
): boolean {
  // Handle beam specially
  if (shape1.type === 'beam') {
    const targetRadius = shape2.type === 'circle' ? shape2.radius :
                         shape2.type === 'box' ? Math.max(shape2.halfWidth, shape2.halfHeight) : 0
    if (shape1.direction === 'right') {
      return beamHits(x1, y1, shape1.height, x2, y2, targetRadius)
    } else {
      return beamHits(-x1, y1, shape1.height, -x2, y2, targetRadius)
    }
  }

  if (shape2.type === 'beam') {
    const targetRadius = shape1.type === 'circle' ? shape1.radius :
                         shape1.type === 'box' ? Math.max(shape1.halfWidth, shape1.halfHeight) : 0
    if (shape2.direction === 'right') {
      return beamHits(x2, y2, shape2.height, x1, y1, targetRadius)
    } else {
      return beamHits(-x2, y2, shape2.height, -x1, y1, targetRadius)
    }
  }

  // Circle vs Circle
  if (shape1.type === 'circle' && shape2.type === 'circle') {
    return circleVsCircle(x1, y1, shape1.radius, x2, y2, shape2.radius)
  }

  // Box vs Box
  if (shape1.type === 'box' && shape2.type === 'box') {
    return boxVsBox(
      x1, y1, shape1.halfWidth, shape1.halfHeight,
      x2, y2, shape2.halfWidth, shape2.halfHeight
    )
  }

  // Circle vs Box
  if (shape1.type === 'circle' && shape2.type === 'box') {
    return circleVsBox(
      x1, y1, shape1.radius,
      x2, y2, shape2.halfWidth, shape2.halfHeight
    )
  }

  if (shape1.type === 'box' && shape2.type === 'circle') {
    return circleVsBox(
      x2, y2, shape2.radius,
      x1, y1, shape1.halfWidth, shape1.halfHeight
    )
  }

  return false
}

/**
 * Collision detection system
 */
export class CollisionSystem {
  /**
   * Check collision between two entities
   */
  checkCollision(a: CollidableEntity, b: CollidableEntity): boolean {
    // Check layer compatibility
    if (!canCollide(a.layer, b.layer)) return false

    // Check if already hit (for piercing projectiles)
    if (a.hitEntities?.has(b.id)) return false
    if (b.hitEntities?.has(a.id)) return false

    return shapesCollide(a.x, a.y, a.shape, b.x, b.y, b.shape)
  }

  /**
   * Find all collisions in a set of entities
   */
  findCollisions(entities: CollidableEntity[]): Array<[CollidableEntity, CollidableEntity]> {
    const collisions: Array<[CollidableEntity, CollidableEntity]> = []

    for (let i = 0; i < entities.length; i++) {
      for (let j = i + 1; j < entities.length; j++) {
        const a = entities[i]!
        const b = entities[j]!

        if (this.checkCollision(a, b)) {
          collisions.push([a, b])
        }
      }
    }

    return collisions
  }

  /**
   * Find all entities from groupB that collide with any entity from groupA
   * More efficient when you know which groups to check
   */
  findGroupCollisions(
    groupA: CollidableEntity[],
    groupB: CollidableEntity[]
  ): Array<[CollidableEntity, CollidableEntity]> {
    const collisions: Array<[CollidableEntity, CollidableEntity]> = []

    for (const a of groupA) {
      for (const b of groupB) {
        if (this.checkCollision(a, b)) {
          collisions.push([a, b])
        }
      }
    }

    return collisions
  }

  /**
   * Find first collision for an entity against a group
   */
  findFirstCollision(
    entity: CollidableEntity,
    targets: CollidableEntity[]
  ): CollidableEntity | null {
    for (const target of targets) {
      if (this.checkCollision(entity, target)) {
        return target
      }
    }
    return null
  }

  /**
   * Find all entities that collide with a point
   */
  findAtPoint(x: number, y: number, entities: CollidableEntity[]): CollidableEntity[] {
    return entities.filter(entity => {
      if (entity.shape.type === 'circle') {
        const dx = x - entity.x
        const dy = y - entity.y
        return dx * dx + dy * dy < entity.shape.radius * entity.shape.radius
      } else if (entity.shape.type === 'box') {
        return pointInBox(x, y, entity.x, entity.y, entity.shape.halfWidth, entity.shape.halfHeight)
      }
      return false
    })
  }

  /**
   * Check if a point is inside any entity in a group
   */
  pointInAny(x: number, y: number, entities: CollidableEntity[]): boolean {
    return this.findAtPoint(x, y, entities).length > 0
  }
}

/**
 * Hitbox sizes for different entity types
 */
export const HITBOX_SIZES = {
  player: { halfWidth: 8, halfHeight: 6 },
  enemy: {
    scout: 20,
    fighter: 20,
    interceptor: 20,
    speeder: 18,
    bomber: 25,
    tank: 30,
    carrier: 35,
    mine: 15,
    turret: 25,
    shield: 22,
  },
  boss: {
    0: 40,
    1: 40,
    2: 40,
    3: 40,
    4: 55,
    5: 50,
  },
  bullet: {
    default: 6,
    big: 10,
    mega: 12,
    ring: 4,
    flame: 5,
  },
  orb: 8,
  beam: 25,
} as const

/**
 * Create collision shape for common entity types
 */
export function createPlayerShape(): CollisionShape {
  return { type: 'box', halfWidth: HITBOX_SIZES.player.halfWidth, halfHeight: HITBOX_SIZES.player.halfHeight }
}

export function createEnemyShape(enemyType: keyof typeof HITBOX_SIZES.enemy): CollisionShape {
  return { type: 'circle', radius: HITBOX_SIZES.enemy[enemyType] }
}

export function createBossShape(bossType: keyof typeof HITBOX_SIZES.boss): CollisionShape {
  return { type: 'circle', radius: HITBOX_SIZES.boss[bossType] }
}

export function createBulletShape(bulletType?: string): CollisionShape {
  const radius = bulletType && bulletType in HITBOX_SIZES.bullet
    ? HITBOX_SIZES.bullet[bulletType as keyof typeof HITBOX_SIZES.bullet]
    : HITBOX_SIZES.bullet.default
  return { type: 'circle', radius }
}

export function createBeamShape(): CollisionShape {
  return { type: 'beam', direction: 'right', height: HITBOX_SIZES.beam }
}

export function createOrbShape(): CollisionShape {
  return { type: 'circle', radius: HITBOX_SIZES.orb }
}
