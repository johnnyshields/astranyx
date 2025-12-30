/**
 * Lockstep Netcode for P2P multiplayer
 *
 * How it works:
 * 1. Each player runs the same deterministic simulation
 * 2. Players exchange inputs for each frame
 * 3. Game only advances when all inputs are received
 * 4. Input delay hides network latency
 *
 * Frame timeline:
 *   Frame 0    Frame 1    Frame 2    Frame 3
 *     |          |          |          |
 *   [input]   [input]   [input]   [input]  <- local input captured
 *     |          |          |          |
 *   [send]    [send]    [send]    [send]   <- send to peers
 *     |          |          |          |
 *   [wait]    [wait]    [wait]    [wait]   <- wait for peer inputs
 *     |          |          |          |
 *   [sim]     [sim]     [sim]     [sim]    <- simulate with all inputs
 */

export interface PlayerInput {
  up: boolean
  down: boolean
  left: boolean
  right: boolean
  fire: boolean
  special: boolean
  secondary: boolean   // Secondary fire (equipped weapon)
  swap: boolean        // Swap weapon (edge-triggered)
  pickup: boolean      // Manual pickup (edge-triggered)
}

export interface FrameInput {
  frame: number
  playerId: string
  input: PlayerInput
  checksum?: number  // For desync detection
}

export interface LockstepConfig {
  inputDelay: number      // Frames of input delay (default: 3)
  maxRollbackFrames: number  // Not used in pure lockstep
  playerCount: number
  localPlayerId: string
  playerOrder: Map<string, number>  // player_id -> index
}

type InputHandler = (inputs: Map<string, PlayerInput>) => void
type DesyncHandler = (frame: number, expected: number, got: number) => void

export class LockstepNetcode {
  private config: LockstepConfig

  // Frame tracking
  private currentFrame = 0
  private confirmedFrame = -1  // Last frame where all inputs received

  // Input storage
  // frame -> player_id -> input
  private inputBuffer: Map<number, Map<string, FrameInput>> = new Map()

  // Local input queue (for input delay)
  private localInputQueue: FrameInput[] = []

  // Peers
  private peers: Map<string, RTCDataChannel> = new Map()

  // Callbacks
  private onInputsReady: InputHandler | null = null
  private onDesync: DesyncHandler | null = null

  // State
  private running = false
  private waitingForInputs = false

  constructor(config: LockstepConfig) {
    this.config = {
      inputDelay: config.inputDelay ?? 3,
      maxRollbackFrames: config.maxRollbackFrames ?? 0,
      playerCount: config.playerCount,
      localPlayerId: config.localPlayerId,
      playerOrder: config.playerOrder,
    }
  }

  start(): void {
    this.running = true
    this.currentFrame = 0
    this.confirmedFrame = -1
    this.inputBuffer.clear()
    this.localInputQueue = []
  }

  stop(): void {
    this.running = false
  }

  /**
   * Add a peer connection
   */
  addPeer(playerId: string, dataChannel: RTCDataChannel): void {
    this.peers.set(playerId, dataChannel)

    dataChannel.onmessage = (event) => {
      const data = JSON.parse(event.data as string) as FrameInput
      this.receiveInput(data)
    }
  }

  removePeer(playerId: string): void {
    this.peers.delete(playerId)
  }

  /**
   * Called each game tick with local input
   * Returns true if simulation should advance
   */
  tick(localInput: PlayerInput): boolean {
    if (!this.running) return false

    // Create input for future frame (with input delay)
    const targetFrame = this.currentFrame + this.config.inputDelay
    const frameInput: FrameInput = {
      frame: targetFrame,
      playerId: this.config.localPlayerId,
      input: localInput,
    }

    // Store locally
    this.storeInput(frameInput)

    // Send to all peers
    this.broadcastInput(frameInput)

    // Check if we can advance
    return this.tryAdvanceFrame()
  }

  /**
   * Try to advance to next frame if all inputs received
   */
  private tryAdvanceFrame(): boolean {
    const frameInputs = this.inputBuffer.get(this.currentFrame)

    if (!frameInputs) {
      this.waitingForInputs = true
      return false
    }

    // Check if we have inputs from all players
    if (frameInputs.size < this.config.playerCount) {
      this.waitingForInputs = true
      return false
    }

    this.waitingForInputs = false

    // Collect inputs in player order for determinism
    const orderedInputs = new Map<string, PlayerInput>()
    for (const [playerId] of this.config.playerOrder) {
      const input = frameInputs.get(playerId)
      if (input) {
        orderedInputs.set(playerId, input.input)
      }
    }

    // Notify game to simulate with these inputs
    this.onInputsReady?.(orderedInputs)

    // Advance frame
    this.confirmedFrame = this.currentFrame
    this.currentFrame++

    // Cleanup old inputs
    this.cleanupOldInputs()

    return true
  }

  private storeInput(frameInput: FrameInput): void {
    let frameInputs = this.inputBuffer.get(frameInput.frame)
    if (!frameInputs) {
      frameInputs = new Map()
      this.inputBuffer.set(frameInput.frame, frameInputs)
    }
    frameInputs.set(frameInput.playerId, frameInput)
  }

  private receiveInput(frameInput: FrameInput): void {
    // Ignore inputs for frames we've already processed
    if (frameInput.frame <= this.confirmedFrame) {
      return
    }

    this.storeInput(frameInput)

    // Try to advance if we were waiting
    if (this.waitingForInputs) {
      this.tryAdvanceFrame()
    }
  }

  private broadcastInput(frameInput: FrameInput): void {
    const message = JSON.stringify(frameInput)

    for (const [, channel] of this.peers) {
      if (channel.readyState === 'open') {
        channel.send(message)
      }
    }
  }

  private cleanupOldInputs(): void {
    // Keep last 60 frames for debugging, delete older
    const minFrame = this.confirmedFrame - 60

    for (const frame of this.inputBuffer.keys()) {
      if (frame < minFrame) {
        this.inputBuffer.delete(frame)
      }
    }
  }

  // Event handlers
  setInputHandler(handler: InputHandler): void {
    this.onInputsReady = handler
  }

  setDesyncHandler(handler: DesyncHandler): void {
    this.onDesync = handler
  }

  // Getters
  getCurrentFrame(): number {
    return this.currentFrame
  }

  getConfirmedFrame(): number {
    return this.confirmedFrame
  }

  isWaitingForInputs(): boolean {
    return this.waitingForInputs
  }

  getInputDelay(): number {
    return this.config.inputDelay
  }

  /**
   * Get the local player index for deterministic spawning
   */
  getLocalPlayerIndex(): number {
    return this.config.playerOrder.get(this.config.localPlayerId) ?? 0
  }
}

/**
 * Empty input for when no input is pressed
 */
export function emptyInput(): PlayerInput {
  return {
    up: false,
    down: false,
    left: false,
    right: false,
    fire: false,
    special: false,
    secondary: false,
    swap: false,
    pickup: false,
  }
}

/**
 * Compare two inputs for equality
 */
export function inputsEqual(a: PlayerInput, b: PlayerInput): boolean {
  return (
    a.up === b.up &&
    a.down === b.down &&
    a.left === b.left &&
    a.right === b.right &&
    a.fire === b.fire &&
    a.special === b.special
  )
}
