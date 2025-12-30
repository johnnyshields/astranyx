# Entity Class Extraction

## Summary

Extracted 5 major entity/system classes from the monolithic Simulation.ts (3120 lines) into standalone, testable modules with comprehensive test coverage. This continues the file structure hardening effort.

## Files Created

### Entities (`src/entities/`)

| File | Lines | Tests | Description |
|------|-------|-------|-------------|
| `Player.ts` | 318 | 46 | Player entity with weapons, powerups, orbs, drones |
| `Player.test.ts` | 300 | - | Comprehensive player tests |
| `Enemy.ts` | 213 | 34 | Enemy entity with 12 types, behaviors, shields |
| `Enemy.test.ts` | 258 | - | Enemy type/behavior tests |
| `Boss.ts` | 268 | 40 | Boss entity with 6 types, phases, segments |
| `Boss.test.ts` | 340 | - | Boss mechanics tests |
| `Powerup.ts` | 178 | 28 | Powerup with 11 types, rarity weights |
| `Powerup.test.ts` | 240 | - | Powerup spawning/effects tests |

### Systems (`src/systems/`)

| File | Lines | Tests | Description |
|------|-------|-------|-------------|
| `ParticleSystem.ts` | 217 | 27 | Particle emitters, effects |
| `ParticleSystem.test.ts` | 200 | - | Particle system tests |

## Key Design Patterns

### Entity Hierarchy

```
Entity (base class)
├── Player
├── Enemy (implements Collidable)
├── Boss (implements Collidable)
├── Powerup (implements Collidable)
└── Bullet (already existed)
```

### Data-Driven Stats

Each entity type uses static lookup tables:

```typescript
// Enemy example
export const ENEMY_STATS: Record<EnemyType, EnemyStats> = {
  grunt: { health: 20, speed: 2, points: 100, behavior: 'straight' },
  shooter: { health: 30, speed: 1.5, points: 150, behavior: 'stationary' },
  // ... 12 types total
}

// Boss example
export const BOSS_STATS: Record<BossType, BossStats> = {
  0: { health: 500, points: 5000, phases: 2 },   // CLASSIC
  1: { health: 600, points: 7000, phases: 3 },   // TWIN
  // ... 6 types total
}
```

### Factory Methods

```typescript
// Simple creation
Enemy.create(id, type, x, y)

// With weapon drop
Enemy.createWithWeapon(id, type, x, y, weaponType)

// Wave-based boss selection
Boss.getTypeForWave(waveNumber)

// Rarity-weighted powerup spawning
Powerup.getRandomType(randomValue)
```

### Type-Specific Mechanics

Boss class handles type-specific initialization:

```typescript
class Boss {
  twin: BossTwin | null       // TWIN boss (type 1)
  segments: BossSegment[]     // WALL boss (type 3)
  charging: boolean           // LASER boss (type 2)
}
```

## Test Coverage

- **Total tests**: 571 (up from 396)
- **New tests**: 175 for extracted entities/systems
- All tests passing
- TypeScript strict mode passing

## Enemy Behaviors

```typescript
type EnemyBehavior =
  | 'straight'    // Move left at constant speed
  | 'sine'        // Sinusoidal vertical movement
  | 'circle'      // Circular orbit pattern
  | 'dive'        // Dive toward player position
  | 'chase'       // Continuous player tracking
  | 'stationary'  // Hold position
```

## Powerup System

11 powerup types with rarity-weighted spawning:

| Type | Rarity | Category |
|------|--------|----------|
| SHIELD | 0.20 | Stat |
| LIFE | 0.05 | Stat |
| SPEED | 0.15 | Stat |
| VULCAN | 0.10 | Weapon |
| SPREAD | 0.08 | Weapon |
| LASER | 0.06 | Weapon |
| MISSILE | 0.07 | Weapon |
| BOMB | 0.05 | Weapon |
| ORB | 0.08 | Companion |
| DRONE | 0.06 | Companion |
| CHARGE | 0.10 | Stat |

## Migration Notes

The extracted classes are designed to match existing interface shapes in Simulation.ts. Integration requires:

1. Import new classes
2. Replace inline object creation with class instantiation
3. Use static methods for spawning/selection logic

The Simulation.ts file still contains the game loop and orchestration logic - these extractions provide reusable, testable building blocks.
