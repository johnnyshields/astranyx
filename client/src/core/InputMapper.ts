/**
 * InputState represents the abstract game inputs
 */
export interface InputState {
  up: boolean
  down: boolean
  left: boolean
  right: boolean
  fire: boolean
  special: boolean
  secondary: boolean
  swap: boolean
  pickup: boolean
  pause: boolean
}

/**
 * Raw input source that provides key and button states
 */
export interface InputSource {
  isKeyDown(code: string): boolean
  isKeyPressed(code: string): boolean
  isMouseDown(button: number): boolean
  getGamepadAxis(index: number): number
  getGamepadButton(index: number): boolean
  getGamepadButtonPressed(index: number): boolean
}

/**
 * Key bindings configuration
 */
export interface KeyBindings {
  up: string[]
  down: string[]
  left: string[]
  right: string[]
  fire: string[]
  secondary: string[]
  swap: string[]
  pickup: string[]
  pause: string[]
}

/**
 * Default bindings for Player 1 (WASD + Space + Mouse)
 */
export const PLAYER1_BINDINGS: KeyBindings = {
  up: ['KeyW'],
  down: ['KeyS'],
  left: ['KeyA'],
  right: ['KeyD'],
  fire: ['Space'],
  secondary: ['ShiftLeft'],
  swap: ['KeyQ'],
  pickup: ['KeyE'],
  pause: ['Escape'],
}

/**
 * Default bindings for Player 2 (Arrow keys)
 */
export const PLAYER2_BINDINGS: KeyBindings = {
  up: ['ArrowUp'],
  down: ['ArrowDown'],
  left: ['ArrowLeft'],
  right: ['ArrowRight'],
  fire: ['Numpad0', 'Digit0'],
  secondary: ['ShiftRight'],
  swap: ['Numpad1', 'Digit1'],
  pickup: ['Numpad2', 'Digit2'],
  pause: [],
}

/**
 * Combined bindings (for single player mode)
 */
export const COMBINED_BINDINGS: KeyBindings = {
  up: ['KeyW', 'ArrowUp'],
  down: ['KeyS', 'ArrowDown'],
  left: ['KeyA', 'ArrowLeft'],
  right: ['KeyD', 'ArrowRight'],
  fire: ['Space'],
  secondary: ['ShiftLeft', 'ShiftRight'],
  swap: ['KeyQ'],
  pickup: ['KeyE'],
  pause: ['Escape'],
}

/**
 * Gamepad mapping configuration
 */
export interface GamepadMapping {
  moveAxisX: number
  moveAxisY: number
  fireButton: number
  secondaryButton: number
  swapButton: number
  pickupButton: number
  pauseButton: number
  deadzone: number
}

/**
 * Default gamepad mapping (Xbox-style)
 */
export const DEFAULT_GAMEPAD_MAPPING: GamepadMapping = {
  moveAxisX: 0,
  moveAxisY: 1,
  fireButton: 0, // A
  secondaryButton: 5, // RB
  swapButton: 4, // LB
  pickupButton: 2, // Y
  pauseButton: 9, // Start
  deadzone: 0.15,
}

/**
 * InputMapper maps raw input sources to game InputState
 * Supports keyboard, mouse, and gamepad with configurable bindings
 */
export class InputMapper {
  private bindings: KeyBindings
  private gamepadMapping: GamepadMapping
  private useMouse: boolean
  private useGamepad: boolean

  constructor(options: {
    bindings?: KeyBindings
    gamepadMapping?: GamepadMapping
    useMouse?: boolean
    useGamepad?: boolean
  } = {}) {
    this.bindings = options.bindings ?? COMBINED_BINDINGS
    this.gamepadMapping = options.gamepadMapping ?? DEFAULT_GAMEPAD_MAPPING
    this.useMouse = options.useMouse ?? true
    this.useGamepad = options.useGamepad ?? true
  }

  /**
   * Map input source to game state
   */
  getState(source: InputSource): InputState {
    return {
      up: this.checkUp(source),
      down: this.checkDown(source),
      left: this.checkLeft(source),
      right: this.checkRight(source),
      fire: this.checkFire(source),
      special: false,
      secondary: this.checkSecondary(source),
      swap: this.checkSwap(source),
      pickup: this.checkPickup(source),
      pause: this.checkPause(source),
    }
  }

  /**
   * Check if any key in a binding is pressed (held down)
   */
  private checkKeys(source: InputSource, keys: string[]): boolean {
    return keys.some(key => source.isKeyDown(key))
  }

  /**
   * Check if any key in a binding was just pressed (edge-triggered)
   */
  private checkKeysPressed(source: InputSource, keys: string[]): boolean {
    return keys.some(key => source.isKeyPressed(key))
  }

  private checkUp(source: InputSource): boolean {
    if (this.checkKeys(source, this.bindings.up)) return true
    if (this.useGamepad) {
      const axis = source.getGamepadAxis(this.gamepadMapping.moveAxisY)
      if (axis < -this.gamepadMapping.deadzone) return true
    }
    return false
  }

  private checkDown(source: InputSource): boolean {
    if (this.checkKeys(source, this.bindings.down)) return true
    if (this.useGamepad) {
      const axis = source.getGamepadAxis(this.gamepadMapping.moveAxisY)
      if (axis > this.gamepadMapping.deadzone) return true
    }
    return false
  }

  private checkLeft(source: InputSource): boolean {
    if (this.checkKeys(source, this.bindings.left)) return true
    if (this.useGamepad) {
      const axis = source.getGamepadAxis(this.gamepadMapping.moveAxisX)
      if (axis < -this.gamepadMapping.deadzone) return true
    }
    return false
  }

  private checkRight(source: InputSource): boolean {
    if (this.checkKeys(source, this.bindings.right)) return true
    if (this.useGamepad) {
      const axis = source.getGamepadAxis(this.gamepadMapping.moveAxisX)
      if (axis > this.gamepadMapping.deadzone) return true
    }
    return false
  }

  private checkFire(source: InputSource): boolean {
    if (this.checkKeys(source, this.bindings.fire)) return true
    if (this.useMouse && source.isMouseDown(0)) return true
    if (this.useGamepad && source.getGamepadButton(this.gamepadMapping.fireButton)) return true
    return false
  }

  private checkSecondary(source: InputSource): boolean {
    if (this.checkKeys(source, this.bindings.secondary)) return true
    if (this.useMouse && source.isMouseDown(2)) return true
    if (this.useGamepad && source.getGamepadButton(this.gamepadMapping.secondaryButton)) return true
    return false
  }

  private checkSwap(source: InputSource): boolean {
    if (this.checkKeysPressed(source, this.bindings.swap)) return true
    if (this.useGamepad && source.getGamepadButtonPressed(this.gamepadMapping.swapButton)) return true
    return false
  }

  private checkPickup(source: InputSource): boolean {
    if (this.checkKeysPressed(source, this.bindings.pickup)) return true
    if (this.useGamepad && source.getGamepadButtonPressed(this.gamepadMapping.pickupButton)) return true
    return false
  }

  private checkPause(source: InputSource): boolean {
    if (this.checkKeysPressed(source, this.bindings.pause)) return true
    if (this.useGamepad && source.getGamepadButtonPressed(this.gamepadMapping.pauseButton)) return true
    return false
  }

  /**
   * Get current bindings
   */
  getBindings(): KeyBindings {
    return { ...this.bindings }
  }

  /**
   * Set new bindings
   */
  setBindings(bindings: KeyBindings): void {
    this.bindings = bindings
  }

  /**
   * Get gamepad mapping
   */
  getGamepadMapping(): GamepadMapping {
    return { ...this.gamepadMapping }
  }

  /**
   * Set gamepad mapping
   */
  setGamepadMapping(mapping: GamepadMapping): void {
    this.gamepadMapping = mapping
  }

  /**
   * Enable/disable mouse input
   */
  setUseMouse(use: boolean): void {
    this.useMouse = use
  }

  /**
   * Enable/disable gamepad input
   */
  setUseGamepad(use: boolean): void {
    this.useGamepad = use
  }

  /**
   * Create mapper for player 1
   */
  static forPlayer1(): InputMapper {
    return new InputMapper({
      bindings: PLAYER1_BINDINGS,
      useMouse: true,
      useGamepad: true,
    })
  }

  /**
   * Create mapper for player 2
   */
  static forPlayer2(): InputMapper {
    return new InputMapper({
      bindings: PLAYER2_BINDINGS,
      useMouse: false,
      useGamepad: false, // P2 doesn't use gamepad in local multiplayer
    })
  }
}

/**
 * List of keys that should have default behavior prevented
 */
export const GAME_KEYS = [
  'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight',
  'KeyW', 'KeyA', 'KeyS', 'KeyD',
  'KeyQ', 'KeyE',
  'Space', 'ShiftLeft', 'ShiftRight',
  'Escape', 'Numpad0', 'Digit0', 'Numpad1', 'Digit1', 'Numpad2', 'Digit2',
]

/**
 * Check if a key code is a game key
 */
export function isGameKey(code: string): boolean {
  return GAME_KEYS.includes(code)
}
