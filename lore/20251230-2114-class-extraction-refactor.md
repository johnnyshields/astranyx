# Class Extraction Refactor

## Summary

Hard refactor of the Astranyx client to extract reusable classes from procedural code. Added Vitest for testing, resulting in 396 tests across 11 test files.

## Test Setup

Installed Vitest with happy-dom environment:

```bash
bun add -d vitest @vitest/coverage-v8 happy-dom
```

```typescript
// vitest.config.ts
export default defineConfig({
  test: {
    globals: true,
    environment: 'happy-dom',
    include: ['src/**/*.test.ts'],
  },
})
```

## Extracted Classes

### Math (`src/math/`)

| Class | Tests | Purpose |
|-------|-------|---------|
| `SeededRandom` | 19 | Deterministic xorshift32 PRNG for P2P lockstep |
| `FixedPoint` | 33 | 16.16 fixed-point math utilities |
| `Vector2` | 49 | 2D vector with full math operations |
| `Matrix4` | 36 | 4x4 matrix for 3D transforms, perspective, lookAt |

**SeededRandom** - Critical for deterministic P2P simulation:
```typescript
const rng = new SeededRandom(12345)
rng.next()      // 0-1 float
rng.nextInt(10) // 0-9 integer
rng.getSeed()   // Current state for sync
```

**FixedPoint** - Prevents floating-point drift in simulation:
```typescript
const fixed = FixedPoint.fromFloat(3.14159)
const result = FixedPoint.mul(fixed, FixedPoint.fromInt(2))
const back = FixedPoint.toFloat(result)
```

### Graphics (`src/graphics/`)

| Class | Tests | Purpose |
|-------|-------|---------|
| `MeshBuilder` | 16 | Fluent mesh building with primitives |

```typescript
const mesh = new MeshBuilder()
  .addBox(10, 10, 10)
  .addCylinder(5, 20, 8)
  .build()
```

### Weapons (`src/game/weapons/`)

| Class | Tests | Purpose |
|-------|-------|---------|
| `WeaponTypes` | - | Type definitions for 16 weapons |
| `WeaponRegistry` | 26 | Central weapon configuration and stats |

```typescript
const stats = WeaponRegistry.getStats('spreadGun')
const available = WeaponRegistry.getAvailableWeapons(wave)
const isContinuous = WeaponRegistry.isContinuous('laser')
```

**Ammo Types**: Normal (infinite), Energy (regenerates), Missile (limited), Special

### Entities (`src/entities/`)

| Class | Tests | Purpose |
|-------|-------|---------|
| `Entity` | - | Abstract base with position, velocity |
| `Bullet` | 14 | Projectile with pierce mechanics |
| `DamageableEntity` | - | Health management helper |

```typescript
class Bullet extends Entity implements Collidable {
  consumePierce(): boolean  // Returns true if bullet survives
  hasHit(id): boolean       // For pierce tracking
  recordHit(id): void
}
```

### Core (`src/core/`)

| Class | Tests | Purpose |
|-------|-------|---------|
| `Camera` | 29 | 2.5D Einhänder-style camera with tilt |
| `InputMapper` | 55 | Configurable input mapping |

**Camera** - Handles perspective tilt and play bounds:
```typescript
camera.setTiltAngleDegrees(20)
camera.worldToNDC(x, y, z)  // Project to screen
camera.ndcToWorld(x, y)     // Unproject to z=0
const bounds = camera.getPlayBounds()
```

**InputMapper** - Separates input logic from DOM events:
```typescript
const p1 = InputMapper.forPlayer1()  // WASD + mouse + gamepad
const p2 = InputMapper.forPlayer2()  // Arrows + numpad
const state = p1.getState(inputSource)
```

### Systems (`src/systems/`)

| Class | Tests | Purpose |
|-------|-------|---------|
| `CollisionSystem` | 67 | Shape-based collision detection |
| `WaveSpawner` | 52 | Wave spawning logic and enemy unlocks |

**CollisionSystem** - Layer-based collision with multiple shapes:
```typescript
const system = new CollisionSystem()
system.checkCollision(entityA, entityB)
system.findGroupCollisions(bullets, enemies)

// Shapes: circle, box, beam
// Layers: player_bullet, enemy_bullet, player, enemy, boss, orb, beam, missile
```

**WaveSpawner** - Deterministic wave generation:
```typescript
const spawner = new WaveSpawner()
const enemies = spawner.getAvailableEnemies(wave)
const result = spawner.generateWave(wave, rng)
// result.enemies: EnemySpawn[]
// result.boss?: BossSpawn
```

## Directory Structure

```
src/
├── boot/           # NEW: Loading system
├── core/
│   ├── Camera.ts        # NEW
│   ├── Camera.test.ts   # NEW
│   ├── InputMapper.ts   # NEW
│   └── InputMapper.test.ts
├── entities/
│   ├── Entity.ts        # NEW
│   ├── Bullet.ts        # NEW
│   └── Bullet.test.ts   # NEW
├── game/
│   └── weapons/
│       ├── WeaponTypes.ts     # NEW
│       ├── WeaponRegistry.ts  # NEW
│       └── WeaponRegistry.test.ts
├── graphics/
│   ├── MeshBuilder.ts      # NEW
│   └── MeshBuilder.test.ts # NEW
├── math/
│   ├── SeededRandom.ts     # NEW
│   ├── SeededRandom.test.ts
│   ├── FixedPoint.ts       # NEW
│   ├── FixedPoint.test.ts
│   ├── Vector2.ts          # NEW
│   ├── Vector2.test.ts
│   ├── Matrix4.ts          # NEW
│   ├── Matrix4.test.ts
│   └── index.ts
└── systems/
    ├── CollisionSystem.ts      # NEW
    ├── CollisionSystem.test.ts
    ├── WaveSpawner.ts          # NEW
    └── WaveSpawner.test.ts
```

## Test Results

```
 ✓ src/math/SeededRandom.test.ts (19 tests)
 ✓ src/math/FixedPoint.test.ts (33 tests)
 ✓ src/math/Vector2.test.ts (49 tests)
 ✓ src/math/Matrix4.test.ts (36 tests)
 ✓ src/graphics/MeshBuilder.test.ts (16 tests)
 ✓ src/game/weapons/WeaponRegistry.test.ts (26 tests)
 ✓ src/entities/Bullet.test.ts (14 tests)
 ✓ src/core/Camera.test.ts (29 tests)
 ✓ src/core/InputMapper.test.ts (55 tests)
 ✓ src/systems/CollisionSystem.test.ts (67 tests)
 ✓ src/systems/WaveSpawner.test.ts (52 tests)

Test Files: 11 passed
Tests: 396 passed
```

## Design Decisions

1. **No mixins**: Originally tried TypeScript mixins for Damageable/Collidable but they don't work well with abstract base classes. Switched to helper classes and interfaces.

2. **Type-only imports**: Used `import type` for types to satisfy `verbatimModuleSyntax`.

3. **Determinism first**: SeededRandom and FixedPoint ensure P2P lockstep stays in sync.

4. **Layer-based collision**: More flexible than hardcoded pairs, easy to extend.

5. **Factory methods**: `Bullet.createPlayerShot()`, `InputMapper.forPlayer1()` for common configurations.

## Future Work

- Extract Player, Enemy, Boss entity classes
- Move more logic from Simulation.ts to systems
- Add tests for Renderer and Game classes (need WebGL mocking)
