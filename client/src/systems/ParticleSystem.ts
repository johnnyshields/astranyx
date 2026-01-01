/**
 * Particle for visual effects
 */
export interface Particle {
  id: number
  x: number
  y: number
  vx: number
  vy: number
  life: number
  maxLife: number
  colorIndex: number
  size: number
}

/**
 * Particle emitter configuration
 */
export interface EmitterConfig {
  x: number
  y: number
  count: number
  speed: number
  speedVariation?: number
  size: number
  sizeVariation?: number
  life: number
  lifeVariation?: number
  colorIndex?: number
  spread?: number  // Angle spread in radians (default: full circle)
  direction?: number  // Base direction in radians
}

/**
 * Particle system for managing visual effects
 */
export class ParticleSystem {
  private particles: Particle[] = []
  private nextId: number = 1
  private maxParticles: number

  constructor(maxParticles: number = 1000) {
    this.maxParticles = maxParticles
  }

  /**
   * Get all active particles
   */
  getParticles(): readonly Particle[] {
    return this.particles
  }

  /**
   * Get particle count
   */
  getCount(): number {
    return this.particles.length
  }

  /**
   * Emit particles in a burst
   */
  emit(config: EmitterConfig, randomFn: () => number): void {
    const {
      x, y, count, speed, size, life, colorIndex = 0,
      speedVariation = 0.5,
      sizeVariation = 0.5,
      lifeVariation = 0.3,
      spread = Math.PI * 2,
      direction = 0,
    } = config

    for (let i = 0; i < count; i++) {
      // Check max particles
      if (this.particles.length >= this.maxParticles) {
        // Remove oldest particles to make room
        this.particles.shift()
      }

      // Random angle within spread
      const angle = direction + (randomFn() - 0.5) * spread

      // Random speed variation
      const particleSpeed = speed * (1 + (randomFn() - 0.5) * speedVariation * 2)

      // Random size variation
      const particleSize = size * (1 + (randomFn() - 0.5) * sizeVariation * 2)

      // Random life variation
      const particleLife = Math.round(life * (1 + (randomFn() - 0.5) * lifeVariation * 2))

      this.particles.push({
        id: this.nextId++,
        x,
        y,
        vx: Math.cos(angle) * particleSpeed,
        vy: Math.sin(angle) * particleSpeed,
        life: particleLife,
        maxLife: particleLife,
        colorIndex,
        size: particleSize,
      })
    }
  }

  /**
   * Emit explosion effect
   */
  emitExplosion(x: number, y: number, size: number, randomFn: () => number): void {
    this.emit({
      x,
      y,
      count: Math.round(size * 2),
      speed: size * 3,
      size: size * 0.5,
      life: 30,
      colorIndex: Math.floor(randomFn() * 3),  // Random warm color
      spread: Math.PI * 2,
    }, randomFn)
  }

  /**
   * Emit spark effect (directional)
   */
  emitSparks(
    x: number,
    y: number,
    direction: number,
    count: number,
    randomFn: () => number
  ): void {
    this.emit({
      x,
      y,
      count,
      speed: 100,
      size: 2,
      life: 20,
      colorIndex: 1,  // Yellow/orange
      spread: Math.PI / 4,
      direction,
    }, randomFn)
  }

  /**
   * Emit trail effect (for missiles, etc.)
   */
  emitTrail(x: number, y: number, randomFn: () => number): void {
    this.emit({
      x,
      y,
      count: 2,
      speed: 20,
      speedVariation: 0.8,
      size: 3,
      sizeVariation: 0.5,
      life: 15,
      lifeVariation: 0.5,
      colorIndex: 2,  // Fire color
      spread: Math.PI / 2,
      direction: Math.PI,  // Behind (left)
    }, randomFn)
  }

  /**
   * Emit hit effect
   */
  emitHit(x: number, y: number, randomFn: () => number): void {
    this.emit({
      x,
      y,
      count: 5,
      speed: 50,
      size: 2,
      life: 10,
      colorIndex: 0,
    }, randomFn)
  }

  /**
   * Emit powerup collect effect
   */
  emitCollect(x: number, y: number, colorIndex: number, randomFn: () => number): void {
    this.emit({
      x,
      y,
      count: 15,
      speed: 80,
      size: 4,
      life: 25,
      colorIndex,
      spread: Math.PI * 2,
    }, randomFn)
  }

  /**
   * Update all particles
   */
  update(dt: number): void {
    const frameTime = dt * 60

    for (const particle of this.particles) {
      // Move
      particle.x += particle.vx * dt
      particle.y += particle.vy * dt

      // Friction
      particle.vx *= 0.98
      particle.vy *= 0.98

      // Age
      particle.life -= frameTime
    }

    // Remove dead particles
    this.particles = this.particles.filter(p => p.life > 0)
  }

  /**
   * Clear all particles
   */
  clear(): void {
    this.particles = []
  }

  /**
   * Get particle opacity based on remaining life
   */
  static getOpacity(particle: Particle): number {
    return Math.max(0, particle.life / particle.maxLife)
  }

  /**
   * Get particle scale based on remaining life (shrinks as it dies)
   */
  static getScale(particle: Particle): number {
    return 0.3 + 0.7 * (particle.life / particle.maxLife)
  }
}

/**
 * Predefined color palettes for particles
 */
export const PARTICLE_COLORS = {
  explosion: [
    [1.0, 0.8, 0.2],  // Yellow
    [1.0, 0.5, 0.1],  // Orange
    [1.0, 0.2, 0.1],  // Red
  ],
  spark: [
    [1.0, 1.0, 0.5],  // Bright yellow
    [1.0, 0.8, 0.3],  // Gold
  ],
  plasma: [
    [0.2, 0.8, 1.0],  // Cyan
    [0.5, 0.5, 1.0],  // Light blue
    [0.8, 0.2, 1.0],  // Purple
  ],
  shield: [
    [0.2, 1.0, 0.5],  // Green
    [0.5, 1.0, 0.8],  // Teal
  ],
} as const

/**
 * Get RGB color for a particle color index
 */
export function getParticleColor(colorIndex: number): [number, number, number] {
  const colors = PARTICLE_COLORS.explosion
  return colors[colorIndex % colors.length] as [number, number, number]
}
