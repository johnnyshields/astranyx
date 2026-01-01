import { describe, it, expect, beforeEach } from 'vitest'
import {
  InputMapper,
  type InputSource,
  PLAYER1_BINDINGS,
  PLAYER2_BINDINGS,
  COMBINED_BINDINGS,
  DEFAULT_GAMEPAD_MAPPING,
  isGameKey,
  GAME_KEYS,
} from './InputMapper.ts'

/**
 * Mock input source for testing
 */
class MockInputSource implements InputSource {
  private keysDown = new Set<string>()
  private keysPressed = new Set<string>()
  private mouseDown = new Set<number>()
  private axes = new Map<number, number>()
  private buttons = new Map<number, boolean>()
  private buttonsPressed = new Map<number, boolean>()

  pressKey(code: string): void {
    this.keysDown.add(code)
    this.keysPressed.add(code)
  }

  holdKey(code: string): void {
    this.keysDown.add(code)
  }

  releaseKey(code: string): void {
    this.keysDown.delete(code)
    this.keysPressed.delete(code)
  }

  pressMouse(button: number): void {
    this.mouseDown.add(button)
  }

  releaseMouse(button: number): void {
    this.mouseDown.delete(button)
  }

  setAxis(index: number, value: number): void {
    this.axes.set(index, value)
  }

  setButton(index: number, pressed: boolean): void {
    this.buttons.set(index, pressed)
  }

  setButtonPressed(index: number, pressed: boolean): void {
    this.buttonsPressed.set(index, pressed)
  }

  clearFrame(): void {
    this.keysPressed.clear()
    this.buttonsPressed.clear()
  }

  isKeyDown(code: string): boolean {
    return this.keysDown.has(code)
  }

  isKeyPressed(code: string): boolean {
    return this.keysPressed.has(code)
  }

  isMouseDown(button: number): boolean {
    return this.mouseDown.has(button)
  }

  getGamepadAxis(index: number): number {
    return this.axes.get(index) ?? 0
  }

  getGamepadButton(index: number): boolean {
    return this.buttons.get(index) ?? false
  }

  getGamepadButtonPressed(index: number): boolean {
    return this.buttonsPressed.get(index) ?? false
  }
}

describe('InputMapper', () => {
  let mapper: InputMapper
  let source: MockInputSource

  beforeEach(() => {
    mapper = new InputMapper()
    source = new MockInputSource()
  })

  describe('constructor', () => {
    it('should use combined bindings by default', () => {
      const bindings = mapper.getBindings()
      expect(bindings.up).toEqual(COMBINED_BINDINGS.up)
    })

    it('should enable mouse and gamepad by default', () => {
      source.pressMouse(0)
      const state = mapper.getState(source)
      expect(state.fire).toBe(true)
    })

    it('should accept custom bindings', () => {
      const custom = new InputMapper({ bindings: PLAYER1_BINDINGS })
      expect(custom.getBindings().up).toEqual(['KeyW'])
    })
  })

  describe('keyboard movement', () => {
    it('should detect up from W key', () => {
      source.holdKey('KeyW')
      expect(mapper.getState(source).up).toBe(true)
    })

    it('should detect up from Arrow key with combined bindings', () => {
      source.holdKey('ArrowUp')
      expect(mapper.getState(source).up).toBe(true)
    })

    it('should detect down from S key', () => {
      source.holdKey('KeyS')
      expect(mapper.getState(source).down).toBe(true)
    })

    it('should detect left from A key', () => {
      source.holdKey('KeyA')
      expect(mapper.getState(source).left).toBe(true)
    })

    it('should detect right from D key', () => {
      source.holdKey('KeyD')
      expect(mapper.getState(source).right).toBe(true)
    })

    it('should not detect movement when keys released', () => {
      source.holdKey('KeyW')
      source.releaseKey('KeyW')
      expect(mapper.getState(source).up).toBe(false)
    })
  })

  describe('keyboard actions', () => {
    it('should detect fire from Space', () => {
      source.holdKey('Space')
      expect(mapper.getState(source).fire).toBe(true)
    })

    it('should detect secondary from Shift', () => {
      source.holdKey('ShiftLeft')
      expect(mapper.getState(source).secondary).toBe(true)
    })

    it('should detect swap from Q (edge triggered)', () => {
      source.pressKey('KeyQ')
      expect(mapper.getState(source).swap).toBe(true)

      source.clearFrame()
      expect(mapper.getState(source).swap).toBe(false)
    })

    it('should detect pickup from E (edge triggered)', () => {
      source.pressKey('KeyE')
      expect(mapper.getState(source).pickup).toBe(true)

      source.clearFrame()
      expect(mapper.getState(source).pickup).toBe(false)
    })

    it('should detect pause from Escape (edge triggered)', () => {
      source.pressKey('Escape')
      expect(mapper.getState(source).pause).toBe(true)

      source.clearFrame()
      expect(mapper.getState(source).pause).toBe(false)
    })
  })

  describe('mouse input', () => {
    it('should detect fire from left mouse', () => {
      source.pressMouse(0)
      expect(mapper.getState(source).fire).toBe(true)
    })

    it('should detect secondary from right mouse', () => {
      source.pressMouse(2)
      expect(mapper.getState(source).secondary).toBe(true)
    })

    it('should not use mouse when disabled', () => {
      mapper.setUseMouse(false)
      source.pressMouse(0)
      expect(mapper.getState(source).fire).toBe(false)
    })
  })

  describe('gamepad input', () => {
    it('should detect up from negative Y axis', () => {
      source.setAxis(1, -0.8)
      expect(mapper.getState(source).up).toBe(true)
    })

    it('should detect down from positive Y axis', () => {
      source.setAxis(1, 0.8)
      expect(mapper.getState(source).down).toBe(true)
    })

    it('should detect left from negative X axis', () => {
      source.setAxis(0, -0.8)
      expect(mapper.getState(source).left).toBe(true)
    })

    it('should detect right from positive X axis', () => {
      source.setAxis(0, 0.8)
      expect(mapper.getState(source).right).toBe(true)
    })

    it('should apply deadzone', () => {
      source.setAxis(0, 0.1) // Below default 0.15 deadzone
      expect(mapper.getState(source).right).toBe(false)

      source.setAxis(0, 0.2) // Above deadzone
      expect(mapper.getState(source).right).toBe(true)
    })

    it('should detect fire from A button', () => {
      source.setButton(0, true)
      expect(mapper.getState(source).fire).toBe(true)
    })

    it('should detect secondary from RB button', () => {
      source.setButton(5, true)
      expect(mapper.getState(source).secondary).toBe(true)
    })

    it('should detect swap from LB button (edge triggered)', () => {
      source.setButtonPressed(4, true)
      expect(mapper.getState(source).swap).toBe(true)
    })

    it('should detect pickup from Y button (edge triggered)', () => {
      source.setButtonPressed(2, true)
      expect(mapper.getState(source).pickup).toBe(true)
    })

    it('should detect pause from Start button (edge triggered)', () => {
      source.setButtonPressed(9, true)
      expect(mapper.getState(source).pause).toBe(true)
    })

    it('should not use gamepad when disabled', () => {
      mapper.setUseGamepad(false)
      source.setAxis(0, 1)
      source.setButton(0, true)
      expect(mapper.getState(source).right).toBe(false)
      expect(mapper.getState(source).fire).toBe(false)
    })
  })

  describe('combined input', () => {
    it('should combine keyboard and mouse', () => {
      source.holdKey('KeyW')
      source.pressMouse(0)

      const state = mapper.getState(source)
      expect(state.up).toBe(true)
      expect(state.fire).toBe(true)
    })

    it('should combine keyboard and gamepad', () => {
      source.holdKey('KeyA')
      source.setButton(0, true)

      const state = mapper.getState(source)
      expect(state.left).toBe(true)
      expect(state.fire).toBe(true)
    })

    it('should combine all input methods', () => {
      source.holdKey('KeyW')
      source.setAxis(0, 1)
      source.pressMouse(0)

      const state = mapper.getState(source)
      expect(state.up).toBe(true)
      expect(state.right).toBe(true)
      expect(state.fire).toBe(true)
    })
  })

  describe('special always returns false', () => {
    it('should always have special as false', () => {
      source.holdKey('Space')
      source.pressMouse(0)
      source.setButton(0, true)

      expect(mapper.getState(source).special).toBe(false)
    })
  })

  describe('factory methods', () => {
    describe('forPlayer1', () => {
      it('should use player 1 bindings', () => {
        const p1 = InputMapper.forPlayer1()
        expect(p1.getBindings().up).toEqual(['KeyW'])
      })

      it('should enable mouse', () => {
        const p1 = InputMapper.forPlayer1()
        source.pressMouse(0)
        expect(p1.getState(source).fire).toBe(true)
      })

      it('should enable gamepad', () => {
        const p1 = InputMapper.forPlayer1()
        source.setButton(0, true)
        expect(p1.getState(source).fire).toBe(true)
      })
    })

    describe('forPlayer2', () => {
      it('should use player 2 bindings', () => {
        const p2 = InputMapper.forPlayer2()
        expect(p2.getBindings().up).toEqual(['ArrowUp'])
      })

      it('should disable mouse', () => {
        const p2 = InputMapper.forPlayer2()
        source.pressMouse(0)
        expect(p2.getState(source).fire).toBe(false)
      })

      it('should disable gamepad', () => {
        const p2 = InputMapper.forPlayer2()
        source.setButton(0, true)
        expect(p2.getState(source).fire).toBe(false)
      })

      it('should use arrow keys for movement', () => {
        const p2 = InputMapper.forPlayer2()
        source.holdKey('ArrowUp')
        source.holdKey('ArrowLeft')
        expect(p2.getState(source).up).toBe(true)
        expect(p2.getState(source).left).toBe(true)
      })

      it('should use numpad for fire', () => {
        const p2 = InputMapper.forPlayer2()
        source.holdKey('Numpad0')
        expect(p2.getState(source).fire).toBe(true)
      })
    })
  })

  describe('configuration', () => {
    it('should allow changing bindings', () => {
      mapper.setBindings(PLAYER2_BINDINGS)

      source.holdKey('ArrowUp')
      expect(mapper.getState(source).up).toBe(true)

      source.holdKey('KeyW')
      expect(mapper.getState(source).up).toBe(true) // Still works from arrow
    })

    it('should allow custom gamepad mapping', () => {
      mapper.setGamepadMapping({
        ...DEFAULT_GAMEPAD_MAPPING,
        fireButton: 1, // Change fire to B button
        deadzone: 0.3,
      })

      source.setButton(0, true)
      expect(mapper.getState(source).fire).toBe(false) // A no longer fires

      source.setButton(1, true)
      expect(mapper.getState(source).fire).toBe(true) // B now fires

      source.setAxis(0, 0.25)
      expect(mapper.getState(source).right).toBe(false) // Higher deadzone
    })
  })
})

describe('isGameKey', () => {
  it('should identify movement keys', () => {
    expect(isGameKey('KeyW')).toBe(true)
    expect(isGameKey('KeyA')).toBe(true)
    expect(isGameKey('KeyS')).toBe(true)
    expect(isGameKey('KeyD')).toBe(true)
    expect(isGameKey('ArrowUp')).toBe(true)
    expect(isGameKey('ArrowDown')).toBe(true)
    expect(isGameKey('ArrowLeft')).toBe(true)
    expect(isGameKey('ArrowRight')).toBe(true)
  })

  it('should identify action keys', () => {
    expect(isGameKey('Space')).toBe(true)
    expect(isGameKey('ShiftLeft')).toBe(true)
    expect(isGameKey('ShiftRight')).toBe(true)
    expect(isGameKey('KeyQ')).toBe(true)
    expect(isGameKey('KeyE')).toBe(true)
    expect(isGameKey('Escape')).toBe(true)
  })

  it('should identify numpad keys', () => {
    expect(isGameKey('Numpad0')).toBe(true)
    expect(isGameKey('Numpad1')).toBe(true)
    expect(isGameKey('Numpad2')).toBe(true)
    expect(isGameKey('Digit0')).toBe(true)
  })

  it('should not identify non-game keys', () => {
    expect(isGameKey('KeyF')).toBe(false)
    expect(isGameKey('Enter')).toBe(false)
    expect(isGameKey('Tab')).toBe(false)
    expect(isGameKey('Backspace')).toBe(false)
  })
})

describe('GAME_KEYS', () => {
  it('should contain all expected keys', () => {
    expect(GAME_KEYS).toContain('KeyW')
    expect(GAME_KEYS).toContain('Space')
    expect(GAME_KEYS).toContain('Escape')
    expect(GAME_KEYS.length).toBeGreaterThan(15)
  })
})

describe('binding presets', () => {
  describe('PLAYER1_BINDINGS', () => {
    it('should use WASD for movement', () => {
      expect(PLAYER1_BINDINGS.up).toContain('KeyW')
      expect(PLAYER1_BINDINGS.down).toContain('KeyS')
      expect(PLAYER1_BINDINGS.left).toContain('KeyA')
      expect(PLAYER1_BINDINGS.right).toContain('KeyD')
    })

    it('should use Space for fire', () => {
      expect(PLAYER1_BINDINGS.fire).toContain('Space')
    })
  })

  describe('PLAYER2_BINDINGS', () => {
    it('should use Arrow keys for movement', () => {
      expect(PLAYER2_BINDINGS.up).toContain('ArrowUp')
      expect(PLAYER2_BINDINGS.down).toContain('ArrowDown')
      expect(PLAYER2_BINDINGS.left).toContain('ArrowLeft')
      expect(PLAYER2_BINDINGS.right).toContain('ArrowRight')
    })

    it('should use Numpad for fire', () => {
      expect(PLAYER2_BINDINGS.fire).toContain('Numpad0')
    })

    it('should have no pause binding', () => {
      expect(PLAYER2_BINDINGS.pause).toHaveLength(0)
    })
  })

  describe('COMBINED_BINDINGS', () => {
    it('should combine WASD and Arrow keys', () => {
      expect(COMBINED_BINDINGS.up).toContain('KeyW')
      expect(COMBINED_BINDINGS.up).toContain('ArrowUp')
    })
  })
})

describe('DEFAULT_GAMEPAD_MAPPING', () => {
  it('should have standard Xbox-style mapping', () => {
    expect(DEFAULT_GAMEPAD_MAPPING.moveAxisX).toBe(0)
    expect(DEFAULT_GAMEPAD_MAPPING.moveAxisY).toBe(1)
    expect(DEFAULT_GAMEPAD_MAPPING.fireButton).toBe(0) // A
    expect(DEFAULT_GAMEPAD_MAPPING.secondaryButton).toBe(5) // RB
    expect(DEFAULT_GAMEPAD_MAPPING.swapButton).toBe(4) // LB
    expect(DEFAULT_GAMEPAD_MAPPING.pickupButton).toBe(2) // Y
    expect(DEFAULT_GAMEPAD_MAPPING.pauseButton).toBe(9) // Start
  })

  it('should have reasonable deadzone', () => {
    expect(DEFAULT_GAMEPAD_MAPPING.deadzone).toBe(0.15)
  })
})
