export interface InputState {
  up: boolean
  down: boolean
  left: boolean
  right: boolean
  fire: boolean
  special: boolean
  pause: boolean
}

export class Input {
  private keys: Set<string> = new Set()
  private keysPressed: Set<string> = new Set() // Just pressed this frame
  private keysReleased: Set<string> = new Set() // Just released this frame

  // Gamepad support
  private gamepadIndex: number | null = null

  init(): void {
    window.addEventListener('keydown', this.onKeyDown)
    window.addEventListener('keyup', this.onKeyUp)
    window.addEventListener('gamepadconnected', this.onGamepadConnected)
    window.addEventListener('gamepaddisconnected', this.onGamepadDisconnected)
    window.addEventListener('blur', this.onBlur)
  }

  destroy(): void {
    window.removeEventListener('keydown', this.onKeyDown)
    window.removeEventListener('keyup', this.onKeyUp)
    window.removeEventListener('gamepadconnected', this.onGamepadConnected)
    window.removeEventListener('gamepaddisconnected', this.onGamepadDisconnected)
    window.removeEventListener('blur', this.onBlur)
  }

  private onKeyDown = (e: KeyboardEvent): void => {
    // Prevent default for game keys
    if (this.isGameKey(e.code)) {
      e.preventDefault()
    }

    if (!this.keys.has(e.code)) {
      this.keysPressed.add(e.code)
    }
    this.keys.add(e.code)
  }

  private onKeyUp = (e: KeyboardEvent): void => {
    this.keys.delete(e.code)
    this.keysReleased.add(e.code)
  }

  private onBlur = (): void => {
    // Clear all keys when window loses focus
    this.keys.clear()
  }

  private onGamepadConnected = (e: GamepadEvent): void => {
    console.log('Gamepad connected:', e.gamepad.id)
    this.gamepadIndex = e.gamepad.index
  }

  private onGamepadDisconnected = (e: GamepadEvent): void => {
    console.log('Gamepad disconnected:', e.gamepad.id)
    if (this.gamepadIndex === e.gamepad.index) {
      this.gamepadIndex = null
    }
  }

  private isGameKey(code: string): boolean {
    return [
      'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight',
      'KeyW', 'KeyA', 'KeyS', 'KeyD',
      'Space', 'ShiftLeft', 'ShiftRight',
      'Escape', 'Numpad0', 'Digit0'
    ].includes(code)
  }

  // Call at end of each frame
  clearFrameState(): void {
    this.keysPressed.clear()
    this.keysReleased.clear()
  }

  isKeyDown(code: string): boolean {
    return this.keys.has(code)
  }

  isKeyPressed(code: string): boolean {
    return this.keysPressed.has(code)
  }

  isKeyReleased(code: string): boolean {
    return this.keysReleased.has(code)
  }

  // Get input state for player 1 (WASD + Space)
  getPlayer1State(): InputState {
    const gamepad = this.getGamepad()

    return {
      up: this.isKeyDown('KeyW') || this.getGamepadAxis(gamepad, 1) < -0.5,
      down: this.isKeyDown('KeyS') || this.getGamepadAxis(gamepad, 1) > 0.5,
      left: this.isKeyDown('KeyA') || this.getGamepadAxis(gamepad, 0) < -0.5,
      right: this.isKeyDown('KeyD') || this.getGamepadAxis(gamepad, 0) > 0.5,
      fire: this.isKeyDown('Space') || this.getGamepadButton(gamepad, 0),
      special: this.isKeyDown('ShiftLeft') || this.getGamepadButton(gamepad, 1),
      pause: this.isKeyPressed('Escape') || this.getGamepadButton(gamepad, 9),
    }
  }

  // Get input state for player 2 (Arrows + Numpad0/0)
  getPlayer2State(): InputState {
    return {
      up: this.isKeyDown('ArrowUp'),
      down: this.isKeyDown('ArrowDown'),
      left: this.isKeyDown('ArrowLeft'),
      right: this.isKeyDown('ArrowRight'),
      fire: this.isKeyDown('Numpad0') || this.isKeyDown('Digit0'),
      special: this.isKeyDown('ShiftRight'),
      pause: false, // Only P1 can pause
    }
  }

  // Legacy: combined input (for single player or when only one set of controls needed)
  getState(): InputState {
    const gamepad = this.getGamepad()

    return {
      up: this.isKeyDown('KeyW') || this.isKeyDown('ArrowUp') || this.getGamepadAxis(gamepad, 1) < -0.5,
      down: this.isKeyDown('KeyS') || this.isKeyDown('ArrowDown') || this.getGamepadAxis(gamepad, 1) > 0.5,
      left: this.isKeyDown('KeyA') || this.isKeyDown('ArrowLeft') || this.getGamepadAxis(gamepad, 0) < -0.5,
      right: this.isKeyDown('KeyD') || this.isKeyDown('ArrowRight') || this.getGamepadAxis(gamepad, 0) > 0.5,
      fire: this.isKeyDown('Space') || this.getGamepadButton(gamepad, 0),
      special: this.isKeyDown('ShiftLeft') || this.isKeyDown('ShiftRight') || this.getGamepadButton(gamepad, 1),
      pause: this.isKeyPressed('Escape') || this.getGamepadButton(gamepad, 9),
    }
  }

  private getGamepad(): Gamepad | null {
    if (this.gamepadIndex === null) return null
    return navigator.getGamepads()[this.gamepadIndex] ?? null
  }

  private getGamepadAxis(gamepad: Gamepad | null, index: number): number {
    if (!gamepad || !gamepad.axes[index]) return 0
    const value = gamepad.axes[index]
    // Dead zone
    return Math.abs(value) < 0.15 ? 0 : value
  }

  private getGamepadButton(gamepad: Gamepad | null, index: number): boolean {
    if (!gamepad || !gamepad.buttons[index]) return false
    return gamepad.buttons[index].pressed
  }
}
