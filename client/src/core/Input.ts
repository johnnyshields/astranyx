export interface InputState {
  up: boolean
  down: boolean
  left: boolean
  right: boolean
  fire: boolean         // Primary fire (Space / Left Mouse) - base gun
  special: boolean      // Unused legacy
  secondary: boolean    // Secondary fire (Shift / Right Mouse) - equipped weapon
  swap: boolean         // Swap weapon (Q) - edge triggered
  pickup: boolean       // Manual pickup (E) - edge triggered
  pause: boolean
}

export class Input {
  private keys: Set<string> = new Set()
  private keysPressed: Set<string> = new Set() // Just pressed this frame
  private keysReleased: Set<string> = new Set() // Just released this frame

  // Mouse support
  private mouseButtons: Set<number> = new Set()
  private mouseButtonsPressed: Set<number> = new Set()

  // Gamepad support
  private gamepadIndex: number | null = null

  init(): void {
    window.addEventListener('keydown', this.onKeyDown)
    window.addEventListener('keyup', this.onKeyUp)
    window.addEventListener('mousedown', this.onMouseDown)
    window.addEventListener('mouseup', this.onMouseUp)
    window.addEventListener('contextmenu', this.onContextMenu)
    window.addEventListener('gamepadconnected', this.onGamepadConnected)
    window.addEventListener('gamepaddisconnected', this.onGamepadDisconnected)
    window.addEventListener('blur', this.onBlur)
  }

  destroy(): void {
    window.removeEventListener('keydown', this.onKeyDown)
    window.removeEventListener('keyup', this.onKeyUp)
    window.removeEventListener('mousedown', this.onMouseDown)
    window.removeEventListener('mouseup', this.onMouseUp)
    window.removeEventListener('contextmenu', this.onContextMenu)
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

  private onMouseDown = (e: MouseEvent): void => {
    if (!this.mouseButtons.has(e.button)) {
      this.mouseButtonsPressed.add(e.button)
    }
    this.mouseButtons.add(e.button)
  }

  private onMouseUp = (e: MouseEvent): void => {
    this.mouseButtons.delete(e.button)
  }

  private onContextMenu = (e: MouseEvent): void => {
    // Prevent right-click context menu during gameplay
    e.preventDefault()
  }

  private onBlur = (): void => {
    // Clear all inputs when window loses focus
    this.keys.clear()
    this.mouseButtons.clear()
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
      'KeyQ', 'KeyE',  // Weapon swap and pickup
      'Space', 'ShiftLeft', 'ShiftRight',
      'Escape', 'Numpad0', 'Digit0'
    ].includes(code)
  }

  // Call at end of each frame
  clearFrameState(): void {
    this.keysPressed.clear()
    this.keysReleased.clear()
    this.mouseButtonsPressed.clear()
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

  isMouseDown(button: number): boolean {
    return this.mouseButtons.has(button)
  }

  isMousePressed(button: number): boolean {
    return this.mouseButtonsPressed.has(button)
  }

  // Get input state for player 1 (WASD + Space + Mouse)
  getPlayer1State(): InputState {
    const gamepad = this.getGamepad()

    return {
      up: this.isKeyDown('KeyW') || this.getGamepadAxis(gamepad, 1) < -0.5,
      down: this.isKeyDown('KeyS') || this.getGamepadAxis(gamepad, 1) > 0.5,
      left: this.isKeyDown('KeyA') || this.getGamepadAxis(gamepad, 0) < -0.5,
      right: this.isKeyDown('KeyD') || this.getGamepadAxis(gamepad, 0) > 0.5,
      fire: this.isKeyDown('Space') || this.isMouseDown(0) || this.getGamepadButton(gamepad, 0),
      special: false, // Legacy, unused
      secondary: this.isKeyDown('ShiftLeft') || this.isMouseDown(2) || this.getGamepadButton(gamepad, 5), // RB
      swap: this.isKeyPressed('KeyQ') || this.isGamepadButtonPressed(gamepad, 4), // LB - edge triggered
      pickup: this.isKeyPressed('KeyE') || this.isGamepadButtonPressed(gamepad, 2), // Y/Triangle
      pause: this.isKeyPressed('Escape') || this.isGamepadButtonPressed(gamepad, 9),
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
      special: false,
      secondary: this.isKeyDown('ShiftRight'),
      swap: this.isKeyPressed('Numpad1') || this.isKeyPressed('Digit1'), // 1 key for P2 swap
      pickup: this.isKeyPressed('Numpad2') || this.isKeyPressed('Digit2'), // 2 key for P2 pickup
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
      fire: this.isKeyDown('Space') || this.isMouseDown(0) || this.getGamepadButton(gamepad, 0),
      special: false,
      secondary: this.isKeyDown('ShiftLeft') || this.isKeyDown('ShiftRight') || this.isMouseDown(2) || this.getGamepadButton(gamepad, 5),
      swap: this.isKeyPressed('KeyQ') || this.isGamepadButtonPressed(gamepad, 4),
      pickup: this.isKeyPressed('KeyE') || this.isGamepadButtonPressed(gamepad, 2),
      pause: this.isKeyPressed('Escape') || this.isGamepadButtonPressed(gamepad, 9),
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

  // For edge-triggered gamepad buttons, we need to track previous state
  // For simplicity, we treat pressed state as the current frame's pressed
  private isGamepadButtonPressed(gamepad: Gamepad | null, index: number): boolean {
    // Note: This is a simplified version - for true edge detection,
    // we'd need to track previous frame's button state
    if (!gamepad || !gamepad.buttons[index]) return false
    return gamepad.buttons[index].pressed
  }
}
