import { describe, it, expect, beforeEach } from 'vitest'
import {
  ParticleSystem,
  PARTICLE_COLORS,
  getParticleColor,
} from './ParticleSystem.ts'

describe('ParticleSystem', () => {
  let system: ParticleSystem
  let mockRandom: () => number

  beforeEach(() => {
    system = new ParticleSystem(100)
    // Deterministic "random" for testing
    let seed = 0
    mockRandom = () => {
      seed = (seed + 0.3) % 1
      return seed
    }
  })

  describe('constructor', () => {
    it('should create empty particle system', () => {
      expect(system.getCount()).toBe(0)
      expect(system.getParticles()).toHaveLength(0)
    })

    it('should respect max particles limit', () => {
      const small = new ParticleSystem(10)
      small.emit({
        x: 0, y: 0, count: 20, speed: 10, size: 1, life: 10,
      }, mockRandom)

      expect(small.getCount()).toBeLessThanOrEqual(10)
    })
  })

  describe('emit', () => {
    it('should create particles', () => {
      system.emit({
        x: 100,
        y: 50,
        count: 5,
        speed: 10,
        size: 2,
        life: 30,
      }, mockRandom)

      expect(system.getCount()).toBe(5)
    })

    it('should set particle properties', () => {
      system.emit({
        x: 100,
        y: 50,
        count: 1,
        speed: 10,
        size: 5,
        life: 30,
        colorIndex: 2,
      }, mockRandom)

      const particle = system.getParticles()[0]!
      expect(particle.x).toBe(100)
      expect(particle.y).toBe(50)
      expect(particle.colorIndex).toBe(2)
      expect(particle.life).toBeGreaterThan(0)
      expect(particle.maxLife).toBeGreaterThan(0)
    })

    it('should apply speed variation', () => {
      system.emit({
        x: 0, y: 0, count: 10, speed: 100, size: 1, life: 10,
        speedVariation: 0.5,
      }, mockRandom)

      const particles = system.getParticles()
      const speeds = particles.map(p => Math.sqrt(p.vx * p.vx + p.vy * p.vy))

      // Should have variation
      const minSpeed = Math.min(...speeds)
      const maxSpeed = Math.max(...speeds)
      expect(maxSpeed).toBeGreaterThan(minSpeed)
    })

    it('should apply directional spread', () => {
      system.emit({
        x: 0, y: 0, count: 10, speed: 100, size: 1, life: 10,
        direction: 0,
        spread: Math.PI / 4,  // 45 degrees
      }, mockRandom)

      const particles = system.getParticles()
      for (const p of particles) {
        const angle = Math.atan2(p.vy, p.vx)
        // Should be within spread range
        expect(Math.abs(angle)).toBeLessThanOrEqual(Math.PI / 4 + 0.1)
      }
    })
  })

  describe('emitExplosion', () => {
    it('should emit explosion particles', () => {
      system.emitExplosion(100, 50, 10, mockRandom)
      expect(system.getCount()).toBe(20)  // size * 2
    })
  })

  describe('emitSparks', () => {
    it('should emit directional sparks', () => {
      system.emitSparks(100, 50, 0, 5, mockRandom)
      expect(system.getCount()).toBe(5)

      // Sparks should generally move right (direction 0)
      const particles = system.getParticles()
      for (const p of particles) {
        expect(p.vx).toBeGreaterThan(0)
      }
    })
  })

  describe('emitTrail', () => {
    it('should emit trail particles', () => {
      system.emitTrail(100, 50, mockRandom)
      expect(system.getCount()).toBe(2)
    })
  })

  describe('emitHit', () => {
    it('should emit hit particles', () => {
      system.emitHit(100, 50, mockRandom)
      expect(system.getCount()).toBe(5)
    })
  })

  describe('emitCollect', () => {
    it('should emit collect particles with color', () => {
      system.emitCollect(100, 50, 3, mockRandom)
      expect(system.getCount()).toBe(15)

      const particle = system.getParticles()[0]!
      expect(particle.colorIndex).toBe(3)
    })
  })

  describe('update', () => {
    it('should move particles', () => {
      system.emit({
        x: 0, y: 0, count: 1, speed: 60, size: 1, life: 100,
        direction: 0,
        spread: 0,
      }, () => 0.5)

      const particle = system.getParticles()[0]!
      const startX = particle.x

      system.update(1 / 60)

      expect(particle.x).toBeGreaterThan(startX)
    })

    it('should reduce particle life', () => {
      system.emit({
        x: 0, y: 0, count: 1, speed: 10, size: 1, life: 30,
      }, mockRandom)

      const particle = system.getParticles()[0]!
      const startLife = particle.life

      system.update(1 / 60)

      expect(particle.life).toBeLessThan(startLife)
    })

    it('should apply friction', () => {
      system.emit({
        x: 0, y: 0, count: 1, speed: 100, size: 1, life: 100,
        direction: 0,
        spread: 0,
      }, () => 0.5)

      const particle = system.getParticles()[0]!
      const startVx = particle.vx

      system.update(1 / 60)

      expect(particle.vx).toBeLessThan(startVx)
    })

    it('should remove dead particles', () => {
      system.emit({
        x: 0, y: 0, count: 5, speed: 10, size: 1, life: 1,
      }, mockRandom)

      expect(system.getCount()).toBe(5)

      // Update enough to kill particles
      system.update(1)

      expect(system.getCount()).toBe(0)
    })
  })

  describe('clear', () => {
    it('should remove all particles', () => {
      system.emit({
        x: 0, y: 0, count: 10, speed: 10, size: 1, life: 100,
      }, mockRandom)

      expect(system.getCount()).toBe(10)

      system.clear()

      expect(system.getCount()).toBe(0)
    })
  })

  describe('static methods', () => {
    describe('getOpacity', () => {
      it('should return full opacity at start', () => {
        const particle = {
          id: 1, x: 0, y: 0, vx: 0, vy: 0,
          life: 30, maxLife: 30, colorIndex: 0, size: 1,
        }
        expect(ParticleSystem.getOpacity(particle)).toBe(1)
      })

      it('should return partial opacity as particle ages', () => {
        const particle = {
          id: 1, x: 0, y: 0, vx: 0, vy: 0,
          life: 15, maxLife: 30, colorIndex: 0, size: 1,
        }
        expect(ParticleSystem.getOpacity(particle)).toBe(0.5)
      })

      it('should return 0 when dead', () => {
        const particle = {
          id: 1, x: 0, y: 0, vx: 0, vy: 0,
          life: 0, maxLife: 30, colorIndex: 0, size: 1,
        }
        expect(ParticleSystem.getOpacity(particle)).toBe(0)
      })
    })

    describe('getScale', () => {
      it('should return full scale at start', () => {
        const particle = {
          id: 1, x: 0, y: 0, vx: 0, vy: 0,
          life: 30, maxLife: 30, colorIndex: 0, size: 1,
        }
        expect(ParticleSystem.getScale(particle)).toBe(1)
      })

      it('should shrink as particle ages', () => {
        const particle = {
          id: 1, x: 0, y: 0, vx: 0, vy: 0,
          life: 0, maxLife: 30, colorIndex: 0, size: 1,
        }
        expect(ParticleSystem.getScale(particle)).toBe(0.3)
      })
    })
  })
})

describe('PARTICLE_COLORS', () => {
  it('should have explosion colors', () => {
    expect(PARTICLE_COLORS.explosion).toHaveLength(3)
  })

  it('should have spark colors', () => {
    expect(PARTICLE_COLORS.spark).toHaveLength(2)
  })

  it('should have plasma colors', () => {
    expect(PARTICLE_COLORS.plasma).toHaveLength(3)
  })

  it('should have shield colors', () => {
    expect(PARTICLE_COLORS.shield).toHaveLength(2)
  })
})

describe('getParticleColor', () => {
  it('should return RGB array', () => {
    const color = getParticleColor(0)
    expect(color).toHaveLength(3)
    expect(color[0]).toBeGreaterThanOrEqual(0)
    expect(color[0]).toBeLessThanOrEqual(1)
  })

  it('should wrap around for large indices', () => {
    const color0 = getParticleColor(0)
    const color3 = getParticleColor(3)
    expect(color0).toEqual(color3)
  })
})
