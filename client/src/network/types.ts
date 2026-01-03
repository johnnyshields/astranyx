/**
 * Shared types for lockstep netcode
 *
 * These types are used across:
 * - LockstepNetcode (orchestrator)
 * - InputBuffer
 * - LocalEventQueue
 * - StateSyncManager
 * - LeaderElection
 */

// =============================================================================
// Player Input Types
// =============================================================================

/**
 * Input state for a single frame
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
    a.special === b.special &&
    a.secondary === b.secondary &&
    a.swap === b.swap &&
    a.pickup === b.pickup &&
    a.pause === b.pause
  )
}

// =============================================================================
// Game Event Types (Owner-Authoritative)
// =============================================================================

/**
 * Owner-authoritative game events
 * These events are only detected by the owning player and broadcast to others
 */
export type GameEvent =
  | DamageEvent
  | DeathEvent
  | RespawnEvent
  | PickupEvent
  | WeaponPickupEvent
  | EnemyDamageEvent

export interface DamageEvent {
  type: 'damage'
  playerId: string
  amount: number
  newShields: number
  newLives: number
}

export interface DeathEvent {
  type: 'death'
  playerId: string
}

export interface RespawnEvent {
  type: 'respawn'
  playerId: string
}

export interface PickupEvent {
  type: 'pickup'
  playerId: string
  pickupId: number
}

export interface WeaponPickupEvent {
  type: 'weapon_pickup'
  playerId: string
  dropId: number
}

export interface EnemyDamageEvent {
  type: 'enemy_damage'
  ownerId: string
  enemyId: number
  amount: number
  newHealth: number
  killed: boolean
}

/**
 * Get the owner/player ID from an event
 */
export function getEventOwnerId(event: GameEvent): string {
  return event.type === 'enemy_damage' ? event.ownerId : event.playerId
}

// =============================================================================
// Frame Input Types
// =============================================================================

/**
 * Input for a specific frame from a specific player
 */
export interface FrameInput {
  frame: number
  playerId: string
  input: PlayerInput
  events?: GameEvent[]  // Owner-authoritative events for this frame
  checksum?: number     // For desync detection
}

// =============================================================================
// Network Message Types
// =============================================================================

/**
 * State sync message sent by leader to correct desync
 */
export interface StateSyncMessage {
  type: 'state_sync'
  frame: number
  state: unknown  // SerializedState from Simulation
  checksum: number
  term: number    // Election term for authority validation
}

/**
 * Leader election messages
 */
export interface RequestVoteMessage {
  type: 'request_vote'
  term: number
  candidateId: string
  lastFrame: number  // For log comparison
}

export interface VoteResponseMessage {
  type: 'vote_response'
  term: number
  voteGranted: boolean
  voterId: string
}

export interface HeartbeatMessage {
  type: 'heartbeat'
  term: number
  leaderId: string
  frame: number
  timestamp?: number  // For RTT measurement (ms since epoch)
}

export interface HeartbeatAckMessage {
  type: 'heartbeat_ack'
  term: number
  peerId: string
  frame: number
  timestamp?: number  // Echo back the heartbeat timestamp for RTT calculation
}

/**
 * All network message types
 */
export type NetMessage =
  | FrameInput
  | StateSyncMessage
  | RequestVoteMessage
  | VoteResponseMessage
  | HeartbeatMessage
  | HeartbeatAckMessage

/**
 * Type guard for StateSyncMessage
 */
export function isStateSyncMessage(msg: NetMessage): msg is StateSyncMessage {
  return 'type' in msg && msg.type === 'state_sync'
}

/**
 * Type guard for election messages
 */
export function isElectionMessage(msg: NetMessage): msg is RequestVoteMessage | VoteResponseMessage {
  return 'type' in msg && (msg.type === 'request_vote' || msg.type === 'vote_response')
}

/**
 * Type guard for heartbeat messages
 */
export function isHeartbeatMessage(msg: NetMessage): msg is HeartbeatMessage | HeartbeatAckMessage {
  return 'type' in msg && (msg.type === 'heartbeat' || msg.type === 'heartbeat_ack')
}

/**
 * Type guard for FrameInput
 */
export function isFrameInput(msg: NetMessage): msg is FrameInput {
  return 'frame' in msg && 'playerId' in msg && 'input' in msg
}

// =============================================================================
// Configuration Types
// =============================================================================

/**
 * Configuration for lockstep netcode
 * Tick values are simulation ticks (30Hz), time values are milliseconds
 */
export interface LockstepConfig {
  inputDelayTicks: number      // Ticks of input delay (default: 2)
  playerCount: number
  localPlayerId: string
  playerOrder: Map<string, number>  // player_id -> index
  stateSyncTicks?: number      // Ticks between state syncs (default: 150 = 5 seconds)
  eventBufferTicks?: number    // Max ticks of events to buffer (default: 450 = 15 seconds)
  electionTimeoutMs?: number   // Ms before election timeout (default: 1500)
  heartbeatMs?: number         // Ms between heartbeats (default: 500)
  protocolMode?: 'binary' | 'json'  // Protocol mode (default: 'binary')
}

/**
 * Simulation tick rate (must match Engine.ts)
 * Network sync happens at this rate, not render frame rate
 */
export const SIM_TICK_RATE = 30 // ticks per second
export const SIM_TICK_MS = 1000 / SIM_TICK_RATE // 33.33ms per tick

/**
 * Default configuration values
 * Tick values are simulation ticks (30Hz), time values are milliseconds
 */
export const DEFAULT_CONFIG = {
  inputDelayTicks: 2,          // 2 ticks = 66ms at 30Hz (responsive for shooters)
  stateSyncTicks: 150,         // 5 seconds at 30Hz (150 ticks)
  eventBufferTicks: 450,       // 15 seconds at 30Hz (450 ticks)
  electionTimeoutMs: 1500,     // 1.5 seconds
  heartbeatMs: 500,            // 0.5 seconds
} as const

// =============================================================================
// Peer State Types
// =============================================================================

/**
 * Election state for a peer
 */
export type PeerState = 'follower' | 'candidate' | 'leader'

// =============================================================================
// Callback Types
// =============================================================================

/**
 * Called when inputs are ready for a frame
 */
export type InputHandler = (inputs: Map<string, PlayerInput>, events: GameEvent[]) => void

/**
 * Called when desync is detected
 */
export type DesyncHandler = (frame: number, expected: number, got: number) => void

/**
 * Called when state sync is received
 * @param state - The authoritative state from leader
 * @param frame - The frame this state is for
 * @param pendingEvents - Local events to re-apply after sync
 */
export type StateSyncHandler = (state: unknown, frame: number, pendingEvents: GameEvent[]) => void

/**
 * Called when leader changes
 */
export type LeaderChangeHandler = (newLeaderId: string, term: number) => void

/**
 * Called when a peer disconnects
 */
export type PeerDisconnectHandler = (peerId: string) => void
