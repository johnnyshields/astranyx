# Rapier Visual Effects System

## Overview

Added Rapier3D physics engine to the client for **visual effects only**. This provides satisfying debris explosions and particle physics without affecting gameplay determinism.

## Critical Design Decision

```
┌─────────────────────────────────────────────────┐
│      astranyx-core (DETERMINISTIC)              │
│  - Circle collision for gameplay                │
│  - Simple velocity-based movement               │
│  - SeededRandom for reproducibility             │
│  - NO Rapier, NO external physics               │
│  - Synced via P2P lockstep                      │
└─────────────────────┬───────────────────────────┘
                      │ Events (death, hit)
                      ▼
┌─────────────────────────────────────────────────┐
│    astranyx-client VisualEffects (Rapier)       │
│  - Debris physics (gravity, rotation, bounce)   │
│  - Spark particles                              │
│  - NOT synced across clients                    │
│  - Each player sees different debris            │
│  - Full SIMD/parallel for performance           │
└─────────────────────────────────────────────────┘
```

## Why This Architecture

### Rapier Determinism is Fragile

Rapier offers `enhanced-determinism` but:
- Cannot use SIMD or parallel features (2-3x slower)
- Must use `nalgebra::RealField` math, not `f32::sin()`
- Requires identical initialization order
- One mistake anywhere breaks cross-platform sync

### Visual Effects Don't Need Sync

- Players don't notice if debris falls differently
- Explosions are "fire and forget"
- No gameplay impact = no sync required

### Performance Benefit

Without determinism constraints:
- Full SIMD acceleration
- Parallel collision detection
- Faster debris physics

## Implementation

### Dependencies (`crates/client/Cargo.toml`)
```toml
rapier3d = "0.22"  # No enhanced-determinism needed
rand = "0.8"       # Non-deterministic RNG for variety
```

### VisualEffects Module (`crates/client/src/effects.rs`)

```rust
pub enum EffectEvent {
    EnemyDeath { position: Vec3, velocity: Vec3, size: f32 },
    PlayerHit { position: Vec3 },
    Explosion { position: Vec3, intensity: f32 },
    Impact { position: Vec3, normal: Vec3 },
}

pub struct VisualEffects {
    physics_pipeline: PhysicsPipeline,
    rigid_body_set: RigidBodySet,
    collider_set: ColliderSet,
    debris: Vec<Debris>,
    // ... other Rapier components
}

impl VisualEffects {
    pub fn spawn_effect(&mut self, event: EffectEvent);
    pub fn update(&mut self, dt: f32);
    pub fn get_debris(&self) -> impl Iterator<Item = DebrisRenderData>;
}
```

### Integration in Game Loop

```rust
// Detect enemy deaths by comparing before/after tick
let enemies_before: HashMap<EntityId, (Vec2, Vec2)> = ...;
simulation.tick(&inputs);
let enemies_after: HashSet<EntityId> = ...;

for (id, (pos, vel)) in &enemies_before {
    if !enemies_after.contains(id) {
        visual_effects.spawn_effect(EffectEvent::EnemyDeath {
            position: Vec3::new(pos.x, pos.y, 0.0),
            velocity: Vec3::new(vel.x, vel.y, 0.0),
            size: 20.0,
        });
    }
}

// Update physics (runs at render framerate, not sim rate)
visual_effects.update(delta);
```

### Debris Properties

- 5-8 chunks per enemy death
- Random velocity spread based on enemy velocity
- Random angular velocity for tumbling
- Gravity: -200 units/sec²
- Linear damping: 0.5 (air resistance)
- Lifetime: 0.5-1.5 seconds with fade out
- Colors: Orange/yellow/red gradient

## What NOT to Do

**NEVER use Rapier in astranyx-core:**
- Player movement
- Enemy AI/movement
- Projectile physics
- Collision detection for damage
- Any state that affects gameplay

**Signs you're doing it wrong:**
- Importing `rapier3d` in core crate
- Physics affecting `GameState`
- Trying to sync Rapier state

## Future Extensions

Could add:
- Screen shake (client-side camera offset)
- Ragdolls for FPS mode deaths
- Destructible scenery (visual only)
- Particle trails (engine exhaust, bullet tracers)

All purely visual, never affecting gameplay state.
