import { describe, it, expect, beforeEach } from 'vitest'
import { Player } from './Player.ts'

describe('Player', () => {
  let player: Player

  beforeEach(() => {
    player = Player.create(1, 'player_1', 100, 50)
  })

  describe('constructor', () => {
    it('should create player with correct initial values', () => {
      expect(player.id).toBe(1)
      expect(player.playerId).toBe('player_1')
      expect(player.x).toBe(100)
      expect(player.y).toBe(50)
      expect(player.lives).toBe(3)
      expect(player.shields).toBe(100)
      expect(player.maxShields).toBe(100)
      expect(player.shipLevel).toBe(1)
      expect(player.dead).toBe(false)
    })

    it('should accept custom config', () => {
      const custom = new Player(2, {
        playerId: 'player_2',
        x: 200,
        y: 100,
        lives: 5,
        maxShields: 200,
        maxWeaponSlots: 3,
      })

      expect(custom.lives).toBe(5)
      expect(custom.maxShields).toBe(200)
      expect(custom.shields).toBe(200)
      expect(custom.maxWeaponSlots).toBe(3)
    })
  })

  describe('getCollisionRadius', () => {
    it('should return player collision radius', () => {
      expect(player.getCollisionRadius()).toBe(8)
    })
  })

  describe('canTakeDamage', () => {
    it('should return true when alive and not invincible', () => {
      expect(player.canTakeDamage()).toBe(true)
    })

    it('should return false when dead', () => {
      player.dead = true
      expect(player.canTakeDamage()).toBe(false)
    })

    it('should return false when invincible', () => {
      player.invincible = 60
      expect(player.canTakeDamage()).toBe(false)
    })
  })

  describe('takeDamage', () => {
    it('should reduce shields', () => {
      player.takeDamage(30)
      expect(player.shields).toBe(70)
    })

    it('should return false if player survives', () => {
      expect(player.takeDamage(30)).toBe(false)
      expect(player.dead).toBe(false)
    })

    it('should kill player when shields depleted', () => {
      expect(player.takeDamage(100)).toBe(true)
      expect(player.dead).toBe(true)
      expect(player.shields).toBe(0)
    })

    it('should reduce lives on death', () => {
      player.takeDamage(150)
      expect(player.lives).toBe(2)
    })

    it('should not damage when invincible', () => {
      player.invincible = 60
      player.takeDamage(50)
      expect(player.shields).toBe(100)
    })

    it('should set respawn timer on death with lives remaining', () => {
      player.takeDamage(100)
      expect(player.respawnTimer).toBe(120)
    })
  })

  describe('respawn', () => {
    it('should reset player state', () => {
      player.takeDamage(100)  // Kill player
      player.respawn(0, 0)

      expect(player.dead).toBe(false)
      expect(player.shields).toBe(100)
      expect(player.invincible).toBe(180)
      expect(player.respawnTimer).toBe(0)
    })

    it('should set position', () => {
      player.respawn(200, 150)
      expect(player.x).toBe(200)
      expect(player.y).toBe(150)
    })

    it('should reset velocity', () => {
      player.vx = 10
      player.vy = 5
      player.respawn(0, 0)
      expect(player.vx).toBe(0)
      expect(player.vy).toBe(0)
    })
  })

  describe('heal', () => {
    it('should restore shields', () => {
      player.shields = 50
      player.heal(30)
      expect(player.shields).toBe(80)
    })

    it('should not exceed max shields', () => {
      player.shields = 90
      player.heal(50)
      expect(player.shields).toBe(100)
    })
  })

  describe('getShieldPercent', () => {
    it('should return shield percentage', () => {
      player.shields = 75
      expect(player.getShieldPercent()).toBe(0.75)
    })

    it('should return 0 when shields empty', () => {
      player.shields = 0
      expect(player.getShieldPercent()).toBe(0)
    })
  })

  describe('upgradeShip', () => {
    it('should increase ship level', () => {
      player.upgradeShip()
      expect(player.shipLevel).toBe(2)
    })

    it('should increase max shields', () => {
      player.upgradeShip()
      expect(player.maxShields).toBe(120)
      expect(player.shields).toBe(120)
    })

    it('should cap at level 5', () => {
      for (let i = 0; i < 10; i++) {
        player.upgradeShip()
      }
      expect(player.shipLevel).toBe(5)
    })
  })

  describe('powerups', () => {
    it('should add powerup', () => {
      player.addPowerup('spread', 2)
      expect(player.powerups.spread).toBe(2)
    })

    it('should cap powerups at 10', () => {
      player.addPowerup('laser', 15)
      expect(player.powerups.laser).toBe(10)
    })

    it('should add orbs when orbit powerup added', () => {
      player.addPowerup('orbit', 2)
      expect(player.orbs.length).toBe(2)
    })

    it('should add drones when drone powerup added', () => {
      player.addPowerup('drone', 2)
      expect(player.drones.length).toBe(2)
    })

    it('should cap drones at 4', () => {
      player.addPowerup('drone', 10)
      expect(player.drones.length).toBe(4)
    })
  })

  describe('speed and fire rate multipliers', () => {
    it('should calculate speed multiplier', () => {
      player.powerups.speed = 5
      expect(player.getSpeedMultiplier()).toBe(1.5)
    })

    it('should calculate fire rate multiplier', () => {
      player.powerups.rapid = 4
      expect(player.getFireRateMultiplier()).toBeCloseTo(1.6)
    })

    it('should return pierce count', () => {
      player.powerups.pierce = 3
      expect(player.getPierceCount()).toBe(3)
    })
  })

  describe('weapon system', () => {
    it('should start with no weapons', () => {
      expect(player.weaponSlots).toHaveLength(0)
      expect(player.getActiveWeapon()).toBeNull()
    })

    it('should equip weapon', () => {
      player.equipWeapon('spread_small', 50, 100)
      expect(player.weaponSlots).toHaveLength(1)
      expect(player.getActiveWeapon()?.type).toBe('spread_small')
    })

    it('should equip multiple weapons up to max slots', () => {
      player.equipWeapon('spread_small', 50, 100)
      player.equipWeapon('laser_small', 100, 200)
      expect(player.weaponSlots).toHaveLength(2)
      expect(player.activeWeaponIndex).toBe(1)
    })

    it('should replace active weapon when slots full', () => {
      player.equipWeapon('spread_small', 50, 100)
      player.equipWeapon('laser_small', 100, 200)
      player.equipWeapon('missile', 10, 20)
      expect(player.weaponSlots).toHaveLength(2)
      expect(player.weaponSlots[1]?.type).toBe('missile')
    })

    it('should cycle weapons', () => {
      player.equipWeapon('spread_small', 50, 100)
      player.equipWeapon('laser_small', 100, 200)
      player.activeWeaponIndex = 0

      player.cycleWeapon()
      expect(player.activeWeaponIndex).toBe(1)

      player.cycleWeapon()
      expect(player.activeWeaponIndex).toBe(0)
    })

    it('should use ammo', () => {
      player.equipWeapon('spread_small', 50, 100)
      expect(player.useAmmo(10)).toBe(true)
      expect(player.getActiveWeapon()?.ammo).toBe(40)
    })

    it('should fail to use ammo when insufficient', () => {
      player.equipWeapon('spread_small', 5, 100)
      expect(player.useAmmo(10)).toBe(false)
      expect(player.getActiveWeapon()?.ammo).toBe(5)
    })

    it('should remove empty weapons', () => {
      player.equipWeapon('spread_small', 0, 100)
      player.equipWeapon('laser_small', 50, 200)
      player.removeEmptyWeapons()
      expect(player.weaponSlots).toHaveLength(1)
      expect(player.weaponSlots[0]?.type).toBe('laser_small')
    })
  })

  describe('update', () => {
    it('should decrement cooldowns', () => {
      player.shootCooldown = 10
      player.invincible = 20
      player.baseGunCooldown = 5

      player.update(1 / 60)

      expect(player.shootCooldown).toBe(9)
      expect(player.invincible).toBe(19)
      expect(player.baseGunCooldown).toBe(4)
    })

    it('should increment frame', () => {
      player.update(1 / 60)
      expect(player.frame).toBe(1)
    })

    it('should update orb angles', () => {
      player.addPowerup('orbit', 1)
      const initialAngle = player.orbs[0]!.angle

      player.update(1 / 60)

      expect(player.orbs[0]!.angle).toBeGreaterThan(initialAngle)
    })

    it('should decrement respawn timer when dead', () => {
      player.dead = true
      player.respawnTimer = 60

      player.update(1 / 60)

      expect(player.respawnTimer).toBe(59)
    })

    it('should not update cooldowns when dead', () => {
      player.dead = true
      player.shootCooldown = 10

      player.update(1 / 60)

      expect(player.shootCooldown).toBe(10)
    })
  })

  describe('isDead', () => {
    it('should return false when alive', () => {
      expect(player.isDead()).toBe(false)
    })

    it('should return false when dead but has lives', () => {
      player.dead = true
      player.lives = 2
      expect(player.isDead()).toBe(false)
    })

    it('should return true when dead with no lives', () => {
      player.dead = true
      player.lives = 0
      expect(player.isDead()).toBe(true)
    })
  })
})
