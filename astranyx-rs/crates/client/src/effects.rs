//! Client-side visual effects using Rapier physics.
//!
//! These effects are NOT deterministic and NOT synced across clients.
//! Each client renders its own debris, particles, etc.

use glam::Vec3;
use rand::Rng;
use rapier3d::prelude::*;

/// Visual effect event from game simulation.
#[derive(Debug, Clone)]
pub enum EffectEvent {
    /// Enemy destroyed at position with velocity.
    EnemyDeath {
        position: Vec3,
        velocity: Vec3,
        size: f32,
    },
    /// Player hit (smaller effect).
    PlayerHit {
        position: Vec3,
    },
    /// Explosion (boss death, etc).
    Explosion {
        position: Vec3,
        intensity: f32,
    },
    /// Projectile impact.
    Impact {
        position: Vec3,
        normal: Vec3,
    },
}

/// A debris chunk with physics body.
struct Debris {
    handle: RigidBodyHandle,
    lifetime: f32,
    max_lifetime: f32,
    color: [f32; 4],
    size: f32,
}

/// Client-side visual effects system.
pub struct VisualEffects {
    /// Rapier physics pipeline.
    physics_pipeline: PhysicsPipeline,
    /// Gravity and other parameters.
    integration_parameters: IntegrationParameters,
    /// Island manager.
    island_manager: IslandManager,
    /// Broad phase collision detection.
    broad_phase: DefaultBroadPhase,
    /// Narrow phase collision detection.
    narrow_phase: NarrowPhase,
    /// Impulse joints.
    impulse_joint_set: ImpulseJointSet,
    /// Multibody joints.
    multibody_joint_set: MultibodyJointSet,
    /// Continuous collision detection solver.
    ccd_solver: CCDSolver,
    /// Query pipeline for raycasts.
    query_pipeline: QueryPipeline,
    /// Rigid body set.
    rigid_body_set: RigidBodySet,
    /// Collider set.
    collider_set: ColliderSet,
    /// Active debris particles.
    debris: Vec<Debris>,
    /// RNG for effect variations.
    rng: rand::rngs::ThreadRng,
}

impl VisualEffects {
    /// Create a new visual effects system.
    pub fn new() -> Self {
        let mut integration_parameters = IntegrationParameters::default();
        integration_parameters.dt = 1.0 / 60.0; // 60 FPS for smooth effects

        Self {
            physics_pipeline: PhysicsPipeline::new(),
            integration_parameters,
            island_manager: IslandManager::new(),
            broad_phase: DefaultBroadPhase::new(),
            narrow_phase: NarrowPhase::new(),
            impulse_joint_set: ImpulseJointSet::new(),
            multibody_joint_set: MultibodyJointSet::new(),
            ccd_solver: CCDSolver::new(),
            query_pipeline: QueryPipeline::new(),
            rigid_body_set: RigidBodySet::new(),
            collider_set: ColliderSet::new(),
            debris: Vec::new(),
            rng: rand::thread_rng(),
        }
    }

    /// Process an effect event.
    pub fn spawn_effect(&mut self, event: EffectEvent) {
        match event {
            EffectEvent::EnemyDeath { position, velocity, size } => {
                self.spawn_debris(position, velocity, size, 5, 8);
            }
            EffectEvent::PlayerHit { position } => {
                self.spawn_debris(position, Vec3::ZERO, 10.0, 2, 4);
            }
            EffectEvent::Explosion { position, intensity } => {
                let count = (intensity * 10.0) as usize;
                self.spawn_debris(position, Vec3::ZERO, 30.0 * intensity, count.min(20), count.min(20) + 5);
            }
            EffectEvent::Impact { position, normal } => {
                self.spawn_sparks(position, normal, 3);
            }
        }
    }

    /// Spawn debris chunks.
    fn spawn_debris(&mut self, position: Vec3, base_velocity: Vec3, spread: f32, min_count: usize, max_count: usize) {
        let count = self.rng.gen_range(min_count..=max_count);

        for _ in 0..count {
            // Random velocity with spread
            let vx = base_velocity.x + self.rng.gen_range(-spread..spread);
            let vy = base_velocity.y + self.rng.gen_range(-spread..spread);
            let vz = self.rng.gen_range(-spread * 0.5..spread * 0.5);

            // Random size
            let size = self.rng.gen_range(2.0..8.0);

            // Random angular velocity
            let ang_vel = vector![
                self.rng.gen_range(-10.0..10.0),
                self.rng.gen_range(-10.0..10.0),
                self.rng.gen_range(-10.0..10.0)
            ];

            // Create rigid body
            let rigid_body = RigidBodyBuilder::dynamic()
                .translation(vector![position.x, position.y, position.z])
                .linvel(vector![vx, vy, vz])
                .angvel(ang_vel)
                .linear_damping(0.5)
                .angular_damping(0.3)
                .build();

            let handle = self.rigid_body_set.insert(rigid_body);

            // Create collider (small box)
            let collider = ColliderBuilder::cuboid(size * 0.5, size * 0.5, size * 0.5)
                .restitution(0.3)
                .friction(0.5)
                .build();

            self.collider_set.insert_with_parent(collider, handle, &mut self.rigid_body_set);

            // Random color (orange/yellow/red for explosions)
            let color = [
                self.rng.gen_range(0.8..1.0),
                self.rng.gen_range(0.3..0.7),
                self.rng.gen_range(0.0..0.2),
                1.0,
            ];

            let lifetime = self.rng.gen_range(0.5..1.5);

            self.debris.push(Debris {
                handle,
                lifetime,
                max_lifetime: lifetime,
                color,
                size,
            });
        }
    }

    /// Spawn spark particles (smaller, faster).
    fn spawn_sparks(&mut self, position: Vec3, normal: Vec3, count: usize) {
        for _ in 0..count {
            // Velocity in hemisphere around normal
            let spread = 50.0;
            let vx = normal.x * 30.0 + self.rng.gen_range(-spread..spread);
            let vy = normal.y * 30.0 + self.rng.gen_range(-spread..spread);
            let vz = normal.z * 30.0 + self.rng.gen_range(-spread..spread);

            let rigid_body = RigidBodyBuilder::dynamic()
                .translation(vector![position.x, position.y, position.z])
                .linvel(vector![vx, vy, vz])
                .linear_damping(2.0)
                .gravity_scale(0.5)
                .build();

            let handle = self.rigid_body_set.insert(rigid_body);

            // Sparks are yellow/white
            let color = [
                1.0,
                self.rng.gen_range(0.8..1.0),
                self.rng.gen_range(0.5..0.9),
                1.0,
            ];

            self.debris.push(Debris {
                handle,
                lifetime: self.rng.gen_range(0.2..0.5),
                max_lifetime: 0.5,
                color,
                size: self.rng.gen_range(1.0..3.0),
            });
        }
    }

    /// Update physics and remove expired debris.
    pub fn update(&mut self, dt: f32) {
        // Step physics
        self.integration_parameters.dt = dt;

        self.physics_pipeline.step(
            &vector![0.0, -200.0, 0.0], // Gravity (downward)
            &self.integration_parameters,
            &mut self.island_manager,
            &mut self.broad_phase,
            &mut self.narrow_phase,
            &mut self.rigid_body_set,
            &mut self.collider_set,
            &mut self.impulse_joint_set,
            &mut self.multibody_joint_set,
            &mut self.ccd_solver,
            Some(&mut self.query_pipeline),
            &(),
            &(),
        );

        // Update lifetimes and remove expired
        let rigid_body_set = &mut self.rigid_body_set;
        let collider_set = &mut self.collider_set;
        let island_manager = &mut self.island_manager;
        let impulse_joint_set = &mut self.impulse_joint_set;
        let multibody_joint_set = &mut self.multibody_joint_set;

        self.debris.retain_mut(|debris| {
            debris.lifetime -= dt;
            if debris.lifetime <= 0.0 {
                // Remove rigid body and its colliders
                rigid_body_set.remove(
                    debris.handle,
                    island_manager,
                    collider_set,
                    impulse_joint_set,
                    multibody_joint_set,
                    true,
                );
                false
            } else {
                true
            }
        });
    }

    /// Get debris for rendering.
    pub fn get_debris(&self) -> impl Iterator<Item = DebrisRenderData> + '_ {
        self.debris.iter().filter_map(|debris| {
            let body = self.rigid_body_set.get(debris.handle)?;
            let pos = body.translation();
            let rot = body.rotation();

            // Fade out as lifetime decreases
            let alpha = (debris.lifetime / debris.max_lifetime).clamp(0.0, 1.0);
            let mut color = debris.color;
            color[3] = alpha;

            Some(DebrisRenderData {
                position: Vec3::new(pos.x, pos.y, pos.z),
                rotation: [rot.i, rot.j, rot.k, rot.w],
                size: debris.size,
                color,
            })
        })
    }

    /// Get the number of active debris particles.
    pub fn debris_count(&self) -> usize {
        self.debris.len()
    }

    /// Clear all effects.
    pub fn clear(&mut self) {
        for debris in self.debris.drain(..) {
            self.rigid_body_set.remove(
                debris.handle,
                &mut self.island_manager,
                &mut self.collider_set,
                &mut self.impulse_joint_set,
                &mut self.multibody_joint_set,
                true,
            );
        }
    }
}

impl Default for VisualEffects {
    fn default() -> Self {
        Self::new()
    }
}

/// Data needed to render a debris particle.
#[derive(Debug, Clone, Copy)]
pub struct DebrisRenderData {
    pub position: Vec3,
    pub rotation: [f32; 4], // Quaternion (i, j, k, w)
    pub size: f32,
    pub color: [f32; 4], // RGBA
}
