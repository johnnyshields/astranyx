import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest'
import { Input } from './Input'

describe('Input', () => {
  let input: Input

  beforeEach(() => {
    input = new Input()
  })

  afterEach(() => {
    input.destroy()
  })

  describe('initialization', () => {
    it('should register event listeners on init', () => {
      const addSpy = vi.spyOn(window, 'addEventListener')
      input.init()
      expect(addSpy).toHaveBeenCalledWith('keydown', expect.any(Function))
      expect(addSpy).toHaveBeenCalledWith('keyup', expect.any(Function))
      expect(addSpy).toHaveBeenCalledWith('mousedown', expect.any(Function))
      expect(addSpy).toHaveBeenCalledWith('mouseup', expect.any(Function))
      expect(addSpy).toHaveBeenCalledWith('contextmenu', expect.any(Function))
      expect(addSpy).toHaveBeenCalledWith('gamepadconnected', expect.any(Function))
      expect(addSpy).toHaveBeenCalledWith('gamepaddisconnected', expect.any(Function))
      expect(addSpy).toHaveBeenCalledWith('blur', expect.any(Function))
    })

    it('should remove event listeners on destroy', () => {
      const removeSpy = vi.spyOn(window, 'removeEventListener')
      input.init()
      input.destroy()
      expect(removeSpy).toHaveBeenCalledWith('keydown', expect.any(Function))
      expect(removeSpy).toHaveBeenCalledWith('keyup', expect.any(Function))
      expect(removeSpy).toHaveBeenCalledWith('mousedown', expect.any(Function))
      expect(removeSpy).toHaveBeenCalledWith('mouseup', expect.any(Function))
      expect(removeSpy).toHaveBeenCalledWith('contextmenu', expect.any(Function))
      expect(removeSpy).toHaveBeenCalledWith('gamepadconnected', expect.any(Function))
      expect(removeSpy).toHaveBeenCalledWith('gamepaddisconnected', expect.any(Function))
      expect(removeSpy).toHaveBeenCalledWith('blur', expect.any(Function))
    })
  })

  describe('keyboard input', () => {
    beforeEach(() => {
      input.init()
    })

    it('should track key down state', () => {
      expect(input.isKeyDown('KeyW')).toBe(false)

      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'KeyW' }))
      expect(input.isKeyDown('KeyW')).toBe(true)

      window.dispatchEvent(new KeyboardEvent('keyup', { code: 'KeyW' }))
      expect(input.isKeyDown('KeyW')).toBe(false)
    })

    it('should track key pressed state (edge trigger)', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'KeyW' }))
      expect(input.isKeyPressed('KeyW')).toBe(true)

      // Second keydown should not trigger pressed again
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'KeyW' }))
      expect(input.isKeyPressed('KeyW')).toBe(true)

      input.clearFrameState()
      expect(input.isKeyPressed('KeyW')).toBe(false)
      expect(input.isKeyDown('KeyW')).toBe(true) // Still held
    })

    it('should track key released state', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'KeyW' }))
      expect(input.isKeyReleased('KeyW')).toBe(false)

      window.dispatchEvent(new KeyboardEvent('keyup', { code: 'KeyW' }))
      expect(input.isKeyReleased('KeyW')).toBe(true)

      input.clearFrameState()
      expect(input.isKeyReleased('KeyW')).toBe(false)
    })

    it('should prevent default for game keys', () => {
      const event = new KeyboardEvent('keydown', { code: 'Space' })
      const preventSpy = vi.spyOn(event, 'preventDefault')
      window.dispatchEvent(event)
      expect(preventSpy).toHaveBeenCalled()
    })

    it('should not prevent default for non-game keys', () => {
      const event = new KeyboardEvent('keydown', { code: 'KeyZ' })
      const preventSpy = vi.spyOn(event, 'preventDefault')
      window.dispatchEvent(event)
      expect(preventSpy).not.toHaveBeenCalled()
    })
  })

  describe('mouse input', () => {
    beforeEach(() => {
      input.init()
    })

    it('should track mouse button down state', () => {
      expect(input.isMouseDown(0)).toBe(false)

      window.dispatchEvent(new MouseEvent('mousedown', { button: 0 }))
      expect(input.isMouseDown(0)).toBe(true)

      window.dispatchEvent(new MouseEvent('mouseup', { button: 0 }))
      expect(input.isMouseDown(0)).toBe(false)
    })

    it('should track mouse pressed state (edge trigger)', () => {
      window.dispatchEvent(new MouseEvent('mousedown', { button: 0 }))
      expect(input.isMousePressed(0)).toBe(true)

      // Second mousedown should not trigger pressed again
      window.dispatchEvent(new MouseEvent('mousedown', { button: 0 }))
      expect(input.isMousePressed(0)).toBe(true)

      input.clearFrameState()
      expect(input.isMousePressed(0)).toBe(false)
      expect(input.isMouseDown(0)).toBe(true) // Still held
    })

    it('should prevent context menu', () => {
      const event = new MouseEvent('contextmenu')
      const preventSpy = vi.spyOn(event, 'preventDefault')
      window.dispatchEvent(event)
      expect(preventSpy).toHaveBeenCalled()
    })

    it('should track right mouse button', () => {
      window.dispatchEvent(new MouseEvent('mousedown', { button: 2 }))
      expect(input.isMouseDown(2)).toBe(true)

      window.dispatchEvent(new MouseEvent('mouseup', { button: 2 }))
      expect(input.isMouseDown(2)).toBe(false)
    })
  })

  describe('blur handling', () => {
    beforeEach(() => {
      input.init()
    })

    it('should clear all inputs on blur', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'KeyW' }))
      window.dispatchEvent(new MouseEvent('mousedown', { button: 0 }))

      expect(input.isKeyDown('KeyW')).toBe(true)
      expect(input.isMouseDown(0)).toBe(true)

      window.dispatchEvent(new Event('blur'))

      expect(input.isKeyDown('KeyW')).toBe(false)
      expect(input.isMouseDown(0)).toBe(false)
    })
  })

  describe('getPlayer1State', () => {
    beforeEach(() => {
      input.init()
    })

    it('should return correct state for WASD movement', () => {
      let state = input.getPlayer1State()
      expect(state.up).toBe(false)
      expect(state.down).toBe(false)
      expect(state.left).toBe(false)
      expect(state.right).toBe(false)

      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'KeyW' }))
      state = input.getPlayer1State()
      expect(state.up).toBe(true)

      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'KeyS' }))
      state = input.getPlayer1State()
      expect(state.down).toBe(true)

      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'KeyA' }))
      state = input.getPlayer1State()
      expect(state.left).toBe(true)

      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'KeyD' }))
      state = input.getPlayer1State()
      expect(state.right).toBe(true)
    })

    it('should return correct state for fire (Space)', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'Space' }))
      const state = input.getPlayer1State()
      expect(state.fire).toBe(true)
    })

    it('should return correct state for fire (Left Mouse)', () => {
      window.dispatchEvent(new MouseEvent('mousedown', { button: 0 }))
      const state = input.getPlayer1State()
      expect(state.fire).toBe(true)
    })

    it('should return correct state for secondary fire (Shift)', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'ShiftLeft' }))
      const state = input.getPlayer1State()
      expect(state.secondary).toBe(true)
    })

    it('should return correct state for secondary fire (Right Mouse)', () => {
      window.dispatchEvent(new MouseEvent('mousedown', { button: 2 }))
      const state = input.getPlayer1State()
      expect(state.secondary).toBe(true)
    })

    it('should return correct state for swap (Q)', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'KeyQ' }))
      const state = input.getPlayer1State()
      expect(state.swap).toBe(true)
    })

    it('should return correct state for pickup (E)', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'KeyE' }))
      const state = input.getPlayer1State()
      expect(state.pickup).toBe(true)
    })

    it('should return correct state for pause (Escape)', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'Escape' }))
      const state = input.getPlayer1State()
      expect(state.pause).toBe(true)
    })

    it('should always have special as false', () => {
      const state = input.getPlayer1State()
      expect(state.special).toBe(false)
    })
  })

  describe('getPlayer2State', () => {
    beforeEach(() => {
      input.init()
    })

    it('should return correct state for arrow key movement', () => {
      let state = input.getPlayer2State()
      expect(state.up).toBe(false)
      expect(state.down).toBe(false)
      expect(state.left).toBe(false)
      expect(state.right).toBe(false)

      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'ArrowUp' }))
      state = input.getPlayer2State()
      expect(state.up).toBe(true)

      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'ArrowDown' }))
      state = input.getPlayer2State()
      expect(state.down).toBe(true)

      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'ArrowLeft' }))
      state = input.getPlayer2State()
      expect(state.left).toBe(true)

      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'ArrowRight' }))
      state = input.getPlayer2State()
      expect(state.right).toBe(true)
    })

    it('should return correct state for fire (Numpad0)', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'Numpad0' }))
      const state = input.getPlayer2State()
      expect(state.fire).toBe(true)
    })

    it('should return correct state for fire (Digit0)', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'Digit0' }))
      const state = input.getPlayer2State()
      expect(state.fire).toBe(true)
    })

    it('should return correct state for secondary fire (ShiftRight)', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'ShiftRight' }))
      const state = input.getPlayer2State()
      expect(state.secondary).toBe(true)
    })

    it('should return correct state for swap (Numpad1)', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'Numpad1' }))
      const state = input.getPlayer2State()
      expect(state.swap).toBe(true)
    })

    it('should return correct state for pickup (Numpad2)', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'Numpad2' }))
      const state = input.getPlayer2State()
      expect(state.pickup).toBe(true)
    })

    it('should always have pause as false for Player 2', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'Escape' }))
      const state = input.getPlayer2State()
      expect(state.pause).toBe(false)
    })
  })

  describe('getState (combined)', () => {
    beforeEach(() => {
      input.init()
    })

    it('should combine WASD and arrow keys for movement', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'KeyW' }))
      let state = input.getState()
      expect(state.up).toBe(true)

      input.clearFrameState()
      window.dispatchEvent(new KeyboardEvent('keyup', { code: 'KeyW' }))
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'ArrowUp' }))
      state = input.getState()
      expect(state.up).toBe(true)
    })

    it('should combine ShiftLeft and ShiftRight for secondary', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'ShiftLeft' }))
      let state = input.getState()
      expect(state.secondary).toBe(true)

      window.dispatchEvent(new KeyboardEvent('keyup', { code: 'ShiftLeft' }))
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'ShiftRight' }))
      state = input.getState()
      expect(state.secondary).toBe(true)
    })
  })

  describe('clearFrameState', () => {
    beforeEach(() => {
      input.init()
    })

    it('should clear pressed and released states', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'KeyW' }))
      window.dispatchEvent(new MouseEvent('mousedown', { button: 0 }))

      expect(input.isKeyPressed('KeyW')).toBe(true)
      expect(input.isMousePressed(0)).toBe(true)

      input.clearFrameState()

      expect(input.isKeyPressed('KeyW')).toBe(false)
      expect(input.isMousePressed(0)).toBe(false)
    })

    it('should not clear held state', () => {
      window.dispatchEvent(new KeyboardEvent('keydown', { code: 'KeyW' }))
      window.dispatchEvent(new MouseEvent('mousedown', { button: 0 }))

      input.clearFrameState()

      expect(input.isKeyDown('KeyW')).toBe(true)
      expect(input.isMouseDown(0)).toBe(true)
    })
  })

  describe('gamepad support', () => {
    beforeEach(() => {
      input.init()
    })

    it('should handle gamepad connection event listener registration', () => {
      // Gamepad events are registered in init() - we verify that
      // the listener was added (checked in initialization tests)
      // Full gamepad testing requires browser environment
      const state = input.getPlayer1State()
      // Without gamepad, these should be false
      expect(state.up).toBe(false)
      expect(state.fire).toBe(false)
    })

    it('should return default input state without gamepad', () => {
      const state = input.getPlayer1State()
      expect(state.up).toBe(false)
      expect(state.down).toBe(false)
      expect(state.left).toBe(false)
      expect(state.right).toBe(false)
      expect(state.fire).toBe(false)
      expect(state.secondary).toBe(false)
      expect(state.swap).toBe(false)
      expect(state.pickup).toBe(false)
      expect(state.pause).toBe(false)
    })
  })

  describe('game keys', () => {
    beforeEach(() => {
      input.init()
    })

    it('should identify all game keys', () => {
      const gameKeys = [
        'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight',
        'KeyW', 'KeyA', 'KeyS', 'KeyD',
        'KeyQ', 'KeyE',
        'Space', 'ShiftLeft', 'ShiftRight',
        'Escape', 'Numpad0', 'Digit0'
      ]

      for (const key of gameKeys) {
        const event = new KeyboardEvent('keydown', { code: key })
        const preventSpy = vi.spyOn(event, 'preventDefault')
        window.dispatchEvent(event)
        expect(preventSpy).toHaveBeenCalled()
      }
    })

    it('should not identify non-game keys', () => {
      const nonGameKeys = ['KeyZ', 'KeyX', 'Enter', 'Tab']

      for (const key of nonGameKeys) {
        const event = new KeyboardEvent('keydown', { code: key })
        const preventSpy = vi.spyOn(event, 'preventDefault')
        window.dispatchEvent(event)
        expect(preventSpy).not.toHaveBeenCalled()
      }
    })
  })
})
