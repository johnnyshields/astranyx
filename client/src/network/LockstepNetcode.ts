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
  pause: boolean       // Pause toggle (edge-triggered)
}

/**
 * Owner-authoritative game events
 * These events are only detected by the owning player and broadcast to others
 */
export type GameEvent =
  | { type: 'damage'; playerId: string; amount: number; newShields: number; newLives: number }
  | { type: 'death'; playerId: string }
  | { type: 'respawn'; playerId: string }
  | { type: 'pickup'; playerId: string; pickupId: number }
  | { type: 'weapon_pickup'; playerId: string; dropId: number }

export interface FrameInput {
  frame: number
  playerId: string
  input: PlayerInput
  events?: GameEvent[]  // Owner-authoritative events for this frame
  checksum?: number     // For desync detection
}

export interface LockstepConfig {
  inputDelay: number      // Frames of input delay (default: 3)
  maxRollbackFrames: number  // Not used in pure lockstep
  playerCount: number
  localPlayerId: string
  playerOrder: Map<string, number>  // player_id -> index
}

type InputHandler = (inputs: Map<string, PlayerInput>, events: GameEvent[]) => void
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

    // Pre-seed frames 0 to inputDelay-1 with empty inputs for all players
    // This is needed because the first real inputs go to frame inputDelay
    const emptyInput: PlayerInput = {
      up: false,
      down: false,
      left: false,
      right: false,
      fire: false,
      special: false,
      secondary: false,
      swap: false,
      pickup: false,
      pause: false,
    }

    for (let frame = 0; frame < this.config.inputDelay; frame++) {
      const frameInputs = new Map<string, FrameInput>()
      for (const [playerId] of this.config.playerOrder) {
        frameInputs.set(playerId, {
          frame,
          playerId,
          input: emptyInput,
        })
      }
      this.inputBuffer.set(frame, frameInputs)
    }

    console.log('Lockstep: Started', {
      playerCount: this.config.playerCount,
      inputDelay: this.config.inputDelay,
      localPlayerId: this.config.localPlayerId,
      peers: Array.from(this.peers.keys()),
      preSeededFrames: this.config.inputDelay,
    })
  }

  stop(): void {
    this.running = false
  }

  /**
   * Add a peer connection
   */
  addPeer(playerId: string, dataChannel: RTCDataChannel): void {
    console.log(`Lockstep: Adding peer ${playerId}`)
    this.peers.set(playerId, dataChannel)

    dataChannel.onmessage = (event) => {
      const data = JSON.parse(event.data as string) as FrameInput
      console.log(`Lockstep: Received input from ${data.playerId} for frame ${data.frame}`)
      this.receiveInput(data)
    }
  }

  removePeer(playerId: string): void {
    this.peers.delete(playerId)
  }

  // Checksum storage for desync detection
  // frame -> player_id -> checksum
  private checksumBuffer: Map<number, Map<string, number>> = new Map()
  private lastLocalChecksum = 0

  /**
   * Called each game tick with local input
   * @param localInput - The local player's input
   * @param events - Owner-authoritative events detected this frame
   * @param checksum - Optional checksum of current game state for desync detection
   * Returns true if simulation should advance
   */
  tick(localInput: PlayerInput, events?: GameEvent[], checksum?: number): boolean {
    if (!this.running) return false

    // Store local checksum for comparison
    if (checksum !== undefined) {
      this.lastLocalChecksum = checksum
    }

    // Create input for future frame (with input delay)
    const targetFrame = this.currentFrame + this.config.inputDelay
    const frameInput: FrameInput = {
      frame: targetFrame,
      playerId: this.config.localPlayerId,
      input: localInput,
      events: events && events.length > 0 ? events : undefined,
      checksum: checksum, // Include checksum for desync detection
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
      console.log(`Lockstep: No inputs for frame ${this.currentFrame}`)
      this.waitingForInputs = true
      return false
    }

    // Check if we have inputs from all players
    if (frameInputs.size < this.config.playerCount) {
      console.log(`Lockstep: Frame ${this.currentFrame} has ${frameInputs.size}/${this.config.playerCount} inputs`)
      this.waitingForInputs = true
      return false
    }

    this.waitingForInputs = false

    // Check for desync (compare checksums from previous frame)
    // We compare checksums from inputDelay frames ago since that's when they were generated
    const checksumFrame = this.currentFrame - this.config.inputDelay
    if (checksumFrame >= 0) {
      this.checkForDesync(checksumFrame, frameInputs)
    }

    // Collect inputs and events in player order for determinism
    const orderedInputs = new Map<string, PlayerInput>()
    const allEvents: GameEvent[] = []
    for (const [playerId] of this.config.playerOrder) {
      const input = frameInputs.get(playerId)
      if (input) {
        orderedInputs.set(playerId, input.input)
        // Collect events from this player
        if (input.events) {
          allEvents.push(...input.events)
        }
      }
    }

    // Notify game to simulate with these inputs and events
    this.onInputsReady?.(orderedInputs, allEvents)

    // Advance frame
    this.confirmedFrame = this.currentFrame
    this.currentFrame++

    // Cleanup old inputs
    this.cleanupOldInputs()

    return true
  }

  /**
   * Check if any checksums mismatch, indicating a desync
   */
  private checkForDesync(frame: number, frameInputs: Map<string, FrameInput>): void {
    // Get local checksum from the input we sent for this frame
    const localInput = frameInputs.get(this.config.localPlayerId)
    if (!localInput?.checksum) return

    // Compare against all remote checksums
    for (const [playerId, input] of frameInputs) {
      if (playerId === this.config.localPlayerId) continue
      if (input.checksum === undefined) continue

      if (input.checksum !== localInput.checksum) {
        console.error(`DESYNC DETECTED at frame ${frame}!`)
        console.error(`  Local checksum: ${localInput.checksum}`)
        console.error(`  Remote (${playerId}) checksum: ${input.checksum}`)
        this.onDesync?.(frame, localInput.checksum, input.checksum)
      }
    }
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
    pause: false,
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
