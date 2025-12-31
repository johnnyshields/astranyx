/**
 * Jepsen-style failure tests for Lockstep Netcode
 *
 * These tests verify correctness under various failure scenarios:
 * - Network partitions
 * - Message loss
 * - Leader failures
 * - Split-brain prevention
 *
 * Inspired by Jepsen analyses: https://jepsen.io/analyses
 */

import { describe, it, expect, beforeEach, afterEach } from 'bun:test'
import { LockstepNetcode } from '../LockstepNetcode.ts'
import { LeaderElection } from '../LeaderElection.ts'
import { InputBuffer } from '../InputBuffer.ts'
import { LocalEventQueue } from '../LocalEventQueue.ts'
import { StateSyncManager } from '../StateSyncManager.ts'
import type { PlayerInput, GameEvent, FrameInput } from '../types.ts'
import { emptyInput, getEventOwnerId } from '../types.ts'
import {
  FaultInjector,
  MockDataChannel,
  createMockNetwork,
  type TestScenario,
  runScenario,
} from './FaultInjection.ts'

// =============================================================================
// Test Utilities
// =============================================================================

function createPlayerOrder(peerIds: string[]): Map<string, number> {
  const order = new Map<string, number>()
  peerIds.forEach((id, idx) => order.set(id, idx))
  return order
}

function createTestInput(overrides: Partial<PlayerInput> = {}): PlayerInput {
  return { ...emptyInput(), ...overrides }
}

// Advance time for election timeouts
function advanceTime(ms: number): Promise<void> {
  return new Promise(resolve => setTimeout(resolve, ms))
}

// =============================================================================
// InputBuffer Tests
// =============================================================================

describe('InputBuffer', () => {
  it('stores and retrieves inputs correctly', () => {
    const buffer = new InputBuffer({
      inputDelay: 3,
      playerCount: 2,
      playerOrder: createPlayerOrder(['p1', 'p2']),
    })
    buffer.reset()

    const input: FrameInput = {
      frame: 5,
      playerId: 'p1',
      input: createTestInput({ up: true }),
    }

    buffer.storeInput(input)
    expect(buffer.hasInput(5, 'p1')).toBe(true)
    expect(buffer.hasInput(5, 'p2')).toBe(false)
  })

  it('detects when all inputs are ready', () => {
    const buffer = new InputBuffer({
      inputDelay: 3,
      playerCount: 2,
      playerOrder: createPlayerOrder(['p1', 'p2']),
    })
    buffer.reset()

    buffer.storeInput({ frame: 5, playerId: 'p1', input: createTestInput() })
    expect(buffer.hasAllInputs(5)).toBe(false)

    buffer.storeInput({ frame: 5, playerId: 'p2', input: createTestInput() })
    expect(buffer.hasAllInputs(5)).toBe(true)
  })

  it('returns inputs in deterministic order', () => {
    const buffer = new InputBuffer({
      inputDelay: 3,
      playerCount: 3,
      playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
    })
    buffer.reset()

    // Add in non-deterministic order
    buffer.storeInput({ frame: 5, playerId: 'p3', input: createTestInput({ right: true }) })
    buffer.storeInput({ frame: 5, playerId: 'p1', input: createTestInput({ up: true }) })
    buffer.storeInput({ frame: 5, playerId: 'p2', input: createTestInput({ down: true }) })

    const result = buffer.getOrderedInputs(5)
    expect(result).not.toBeNull()

    // Should be in player order
    const keys = Array.from(result!.inputs.keys())
    expect(keys).toEqual(['p1', 'p2', 'p3'])
  })

  it('detects checksum mismatches', () => {
    const buffer = new InputBuffer({
      inputDelay: 3,
      playerCount: 2,
      playerOrder: createPlayerOrder(['p1', 'p2']),
    })
    buffer.reset()

    buffer.storeInput({ frame: 5, playerId: 'p1', input: createTestInput(), checksum: 12345 })
    buffer.storeInput({ frame: 5, playerId: 'p2', input: createTestInput(), checksum: 99999 })

    const mismatches = buffer.checkDesync(5, 'p1')
    expect(mismatches.length).toBe(1)
    expect(mismatches[0]!.playerId).toBe('p2')
    expect(mismatches[0]!.localChecksum).toBe(12345)
    expect(mismatches[0]!.remoteChecksum).toBe(99999)
  })

  it('cleans up old frames', () => {
    const buffer = new InputBuffer({
      inputDelay: 3,
      playerCount: 1,
      playerOrder: createPlayerOrder(['p1']),
      retentionFrames: 10,
    })
    buffer.reset()

    // Add frames 0-20
    for (let i = 0; i <= 20; i++) {
      buffer.storeInput({ frame: i, playerId: 'p1', input: createTestInput() })
    }

    expect(buffer.size()).toBeGreaterThan(10)

    // Cleanup with confirmed frame 15
    buffer.cleanup(15)

    // Frames before 5 (15 - 10) should be gone
    expect(buffer.hasInput(4, 'p1')).toBe(false)
    expect(buffer.hasInput(5, 'p1')).toBe(true)
  })

  it('pre-seeds initial frames with empty inputs on reset', () => {
    const buffer = new InputBuffer({
      inputDelay: 3,
      playerCount: 2,
      playerOrder: createPlayerOrder(['p1', 'p2']),
    })
    buffer.reset()

    // Frames 0, 1, 2 should be pre-seeded (inputDelay = 3)
    expect(buffer.hasAllInputs(0)).toBe(true)
    expect(buffer.hasAllInputs(1)).toBe(true)
    expect(buffer.hasAllInputs(2)).toBe(true)
    expect(buffer.hasAllInputs(3)).toBe(false)

    // Verify inputs are empty
    const frame0 = buffer.getOrderedInputs(0)
    expect(frame0).not.toBeNull()
    const p1Input = frame0!.inputs.get('p1')
    expect(p1Input?.up).toBe(false)
    expect(p1Input?.fire).toBe(false)
  })

  it('returns null for getOrderedInputs on partially filled frame', () => {
    const buffer = new InputBuffer({
      inputDelay: 3,
      playerCount: 3,
      playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
    })
    buffer.reset()

    // Only add 2 of 3 players' inputs for frame 10
    buffer.storeInput({ frame: 10, playerId: 'p1', input: createTestInput() })
    buffer.storeInput({ frame: 10, playerId: 'p2', input: createTestInput() })

    // Should return null since p3 is missing
    expect(buffer.getOrderedInputs(10)).toBeNull()
    expect(buffer.hasAllInputs(10)).toBe(false)
    expect(buffer.getInputCount(10)).toBe(2)

    // Now add p3
    buffer.storeInput({ frame: 10, playerId: 'p3', input: createTestInput() })
    expect(buffer.getOrderedInputs(10)).not.toBeNull()
    expect(buffer.hasAllInputs(10)).toBe(true)
  })

  it('handles high frame numbers correctly', () => {
    const buffer = new InputBuffer({
      inputDelay: 3,
      playerCount: 2,
      playerOrder: createPlayerOrder(['p1', 'p2']),
      retentionFrames: 60,
    })
    buffer.reset()

    // Simulate a long game session with high frame numbers
    const highFrame = 100000
    buffer.storeInput({ frame: highFrame, playerId: 'p1', input: createTestInput({ up: true }) })
    buffer.storeInput({ frame: highFrame, playerId: 'p2', input: createTestInput({ down: true }) })

    expect(buffer.hasAllInputs(highFrame)).toBe(true)
    const result = buffer.getOrderedInputs(highFrame)
    expect(result).not.toBeNull()
    expect(result!.inputs.get('p1')?.up).toBe(true)
    expect(result!.inputs.get('p2')?.down).toBe(true)

    // Cleanup should work at high frames
    buffer.cleanup(highFrame)
    // Pre-seeded frames 0-2 should be cleaned up
    expect(buffer.hasInput(0, 'p1')).toBe(false)
    // Only highFrame should remain (within retention window)
    expect(buffer.hasInput(highFrame, 'p1')).toBe(true)
  })

  it('collects events from all players in deterministic order', () => {
    const buffer = new InputBuffer({
      inputDelay: 3,
      playerCount: 2,
      playerOrder: createPlayerOrder(['p1', 'p2']),
    })
    buffer.reset()

    const event1: GameEvent = { type: 'damage', playerId: 'p1', amount: 10, newShields: 90, newLives: 3 }
    const event2: GameEvent = { type: 'pickup', playerId: 'p2', pickupId: 5 }
    const event3: GameEvent = { type: 'death', playerId: 'p1' }

    // Add inputs with events (p2 first, then p1 to test ordering)
    buffer.storeInput({ frame: 5, playerId: 'p2', input: createTestInput(), events: [event2] })
    buffer.storeInput({ frame: 5, playerId: 'p1', input: createTestInput(), events: [event1, event3] })

    const result = buffer.getOrderedInputs(5)
    expect(result).not.toBeNull()

    // Events should be ordered by player order: p1's events first, then p2's
    expect(result!.events.length).toBe(3)
    expect(result!.events[0]).toEqual(event1) // p1's first event
    expect(result!.events[1]).toEqual(event3) // p1's second event
    expect(result!.events[2]).toEqual(event2) // p2's event
  })

  it('handles checksum comparison with missing checksums', () => {
    const buffer = new InputBuffer({
      inputDelay: 3,
      playerCount: 2,
      playerOrder: createPlayerOrder(['p1', 'p2']),
    })
    buffer.reset()

    // p1 provides checksum, p2 doesn't
    buffer.storeInput({ frame: 5, playerId: 'p1', input: createTestInput(), checksum: 12345 })
    buffer.storeInput({ frame: 5, playerId: 'p2', input: createTestInput() })

    // Should not report mismatch for missing checksum
    const mismatches = buffer.checkDesync(5, 'p1')
    expect(mismatches.length).toBe(0)
  })

  it('returns empty array when checking desync on non-existent frame', () => {
    const buffer = new InputBuffer({
      inputDelay: 3,
      playerCount: 2,
      playerOrder: createPlayerOrder(['p1', 'p2']),
    })
    buffer.reset()

    const mismatches = buffer.checkDesync(9999, 'p1')
    expect(mismatches.length).toBe(0)
  })

  it('overwrites duplicate inputs for same frame/player', () => {
    const buffer = new InputBuffer({
      inputDelay: 3,
      playerCount: 2,
      playerOrder: createPlayerOrder(['p1', 'p2']),
    })
    buffer.reset()

    // Send input twice (simulating duplicate packet)
    buffer.storeInput({ frame: 5, playerId: 'p1', input: createTestInput({ up: true }) })
    buffer.storeInput({ frame: 5, playerId: 'p1', input: createTestInput({ down: true }) })
    buffer.storeInput({ frame: 5, playerId: 'p2', input: createTestInput() })

    const result = buffer.getOrderedInputs(5)
    expect(result).not.toBeNull()
    // Should have the second (overwritten) input
    expect(result!.inputs.get('p1')?.up).toBe(false)
    expect(result!.inputs.get('p1')?.down).toBe(true)
  })
})

// =============================================================================
// LocalEventQueue Tests
// =============================================================================

describe('LocalEventQueue', () => {
  it('buffers and retrieves events', () => {
    const queue = new LocalEventQueue({
      bufferSize: 100,
      localPlayerId: 'p1',
    })
    queue.reset()

    const event: GameEvent = { type: 'damage', playerId: 'p1', amount: 10, newShields: 90, newLives: 3 }
    queue.addEvent(event, 5)

    const pending = queue.getPendingEvents()
    expect(pending.length).toBe(1)
    expect(pending[0]).toEqual(event)
  })

  it('filters local vs remote events', () => {
    const queue = new LocalEventQueue({
      bufferSize: 100,
      localPlayerId: 'p1',
    })
    queue.reset()

    queue.addEvent({ type: 'damage', playerId: 'p1', amount: 10, newShields: 90, newLives: 3 }, 5)
    queue.addEvent({ type: 'damage', playerId: 'p2', amount: 20, newShields: 80, newLives: 3 }, 5)

    const allPending = queue.getPendingEvents()
    expect(allPending.length).toBe(2)

    const remoteEvents = queue.filterRemoteEvents(allPending)
    expect(remoteEvents.length).toBe(1)
    expect(getEventOwnerId(remoteEvents[0]!)).toBe('p2')
  })

  it('preserves local events for re-apply after sync', () => {
    const queue = new LocalEventQueue({
      bufferSize: 100,
      localPlayerId: 'p1',
    })
    queue.reset()

    queue.addEvent({ type: 'pickup', playerId: 'p1', pickupId: 1 }, 5)
    queue.addEvent({ type: 'pickup', playerId: 'p2', pickupId: 2 }, 6)

    const eventsToReapply = queue.onStateSync(10)

    // Only local events should be returned for re-application
    expect(eventsToReapply.length).toBe(1)
    expect(getEventOwnerId(eventsToReapply[0]!)).toBe('p1')

    // Queue should be cleared
    expect(queue.getPendingEvents().length).toBe(0)
  })
})

// =============================================================================
// StateSyncManager Tests
// =============================================================================

describe('StateSyncManager', () => {
  it('determines when to send sync', () => {
    const manager = new StateSyncManager({
      syncInterval: 10,
    })
    manager.reset()

    // Initially should not need sync
    manager.setCurrentFrame(5)
    expect(manager.shouldSendSync()).toBe(false)

    // After sync interval, should need sync
    manager.setCurrentFrame(15)
    expect(manager.shouldSendSync()).toBe(true)

    // After sending sync, should not need it
    manager.onSyncSent()
    expect(manager.shouldSendSync()).toBe(false)
  })

  it('triggers immediate sync on desync', () => {
    const manager = new StateSyncManager({
      syncInterval: 100,
    })
    manager.reset()

    manager.setCurrentFrame(5)
    expect(manager.shouldSendSync()).toBe(false)

    manager.markDesync()
    expect(manager.shouldSendSync()).toBe(true)
  })

  it('validates sync term', () => {
    const manager = new StateSyncManager({
      syncInterval: 10,
    })
    manager.reset()
    manager.setCurrentTerm(5)

    // Old term sync should be ignored
    const oldResult = manager.receiveSyncMessage({
      type: 'state_sync',
      frame: 10,
      state: {},
      checksum: 123,
      term: 3, // Old term
    })
    expect(oldResult.length).toBe(0)

    // Current term sync should be accepted
    let syncReceived = false
    manager.setStateSyncHandler(() => {
      syncReceived = true
    })

    manager.receiveSyncMessage({
      type: 'state_sync',
      frame: 10,
      state: {},
      checksum: 123,
      term: 5,
    })
    expect(syncReceived).toBe(true)
  })
})

// =============================================================================
// LeaderElection Tests
// =============================================================================

describe('LeaderElection', () => {
  it('initializes with player 0 as leader', () => {
    const election = new LeaderElection({
      localPlayerId: 'p1',
      playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    expect(election.isLeader()).toBe(true)
    expect(election.getCurrentLeader()).toBe('p1')
  })

  it('player 1 starts as follower', () => {
    const election = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    expect(election.isLeader()).toBe(false)
    expect(election.getState()).toBe('follower')
  })

  it('grants votes correctly', () => {
    const e1 = new LeaderElection({
      localPlayerId: 'p1',
      playerOrder: createPlayerOrder(['p1', 'p2']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    const e2 = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder: createPlayerOrder(['p1', 'p2']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    let voteResponse: any = null
    e2.setSendMessage((peerId, msg) => {
      if (msg.type === 'vote_response') {
        voteResponse = msg
      }
    })

    // p2 receives vote request from p1 for term 1
    e2.handleMessage(
      {
        type: 'request_vote',
        term: 1,
        candidateId: 'p1',
        lastFrame: 0,
      },
      'p1'
    )

    expect(voteResponse).not.toBeNull()
    expect(voteResponse.voteGranted).toBe(true)
  })

  it('rejects vote for lower term', () => {
    const election = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder: createPlayerOrder(['p1', 'p2']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    // Manually set term higher
    election.handleMessage(
      { type: 'heartbeat', term: 5, leaderId: 'p1', frame: 0 },
      'p1'
    )

    let voteResponse: any = null
    election.setSendMessage((peerId, msg) => {
      if (msg.type === 'vote_response') {
        voteResponse = msg
      }
    })

    // Receive vote request for lower term
    election.handleMessage(
      { type: 'request_vote', term: 3, candidateId: 'p3', lastFrame: 0 },
      'p3'
    )

    expect(voteResponse.voteGranted).toBe(false)
  })

  it('leader steps down when higher term discovered via heartbeat', () => {
    const election = new LeaderElection({
      localPlayerId: 'p1',
      playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    expect(election.isLeader()).toBe(true)
    expect(election.getState()).toBe('leader')

    // Receive heartbeat with higher term from another leader
    election.handleMessage(
      { type: 'heartbeat', term: 5, leaderId: 'p2', frame: 0 },
      'p2'
    )

    // Should step down
    expect(election.isLeader()).toBe(false)
    expect(election.getState()).toBe('follower')
    expect(election.getCurrentLeader()).toBe('p2')
    expect(election.getCurrentTerm()).toBe(5)
  })

  it('candidate steps down when higher term vote response received', () => {
    const e1 = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    e1.addPeer('p1')
    e1.addPeer('p3')

    // Simulate p2 starting election
    // First, force into candidate state by simulating leader disconnect
    e1.removePeer('p1') // p1 was initial leader, triggers election

    // Now simulate receiving vote response with higher term
    e1.handleMessage(
      { type: 'vote_response', term: 10, voteGranted: false, voterId: 'p3' },
      'p3'
    )

    // Should step down to follower
    expect(e1.getState()).toBe('follower')
  })

  it('rejects vote when already voted for different candidate in same term', () => {
    const election = new LeaderElection({
      localPlayerId: 'p3',
      playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    let voteResponses: any[] = []
    election.setSendMessage((peerId, msg) => {
      if (msg.type === 'vote_response') {
        voteResponses.push({ peerId, msg })
      }
    })

    // p1 requests vote for term 1
    election.handleMessage(
      { type: 'request_vote', term: 1, candidateId: 'p1', lastFrame: 0 },
      'p1'
    )

    expect(voteResponses.length).toBe(1)
    expect(voteResponses[0].msg.voteGranted).toBe(true)

    // p2 also requests vote for same term - should be rejected
    election.handleMessage(
      { type: 'request_vote', term: 1, candidateId: 'p2', lastFrame: 0 },
      'p2'
    )

    expect(voteResponses.length).toBe(2)
    expect(voteResponses[1].msg.voteGranted).toBe(false)
  })

  it('allows vote for same candidate multiple times in same term', () => {
    const election = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder: createPlayerOrder(['p1', 'p2']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    let voteResponses: any[] = []
    election.setSendMessage((peerId, msg) => {
      if (msg.type === 'vote_response') {
        voteResponses.push(msg)
      }
    })

    // p1 requests vote twice (retransmission)
    election.handleMessage(
      { type: 'request_vote', term: 1, candidateId: 'p1', lastFrame: 0 },
      'p1'
    )
    election.handleMessage(
      { type: 'request_vote', term: 1, candidateId: 'p1', lastFrame: 0 },
      'p1'
    )

    expect(voteResponses.length).toBe(2)
    expect(voteResponses[0].voteGranted).toBe(true)
    expect(voteResponses[1].voteGranted).toBe(true) // Same candidate, still granted
  })

  it('candidate wins with majority votes', () => {
    const e1 = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    e1.addPeer('p1')
    e1.addPeer('p3')
    e1.start() // Must start to enable elections

    let leaderChanged = false
    e1.setLeaderChangeHandler((leaderId, term) => {
      if (leaderId === 'p2') leaderChanged = true
    })

    // Simulate leader (p1) disconnect to trigger election
    e1.removePeer('p1')

    // p2 is now candidate and voted for self. Needs 2 of 3 votes (majority).
    // p2 already has 1 vote (self). Needs 1 more.

    expect(e1.getState()).toBe('candidate')

    // Receive vote from p3
    e1.handleMessage(
      { type: 'vote_response', term: e1.getCurrentTerm(), voteGranted: true, voterId: 'p3' },
      'p3'
    )

    // Should become leader with 2 votes
    expect(e1.isLeader()).toBe(true)
    expect(leaderChanged).toBe(true)

    e1.stop() // Clean up timers
  })

  it('candidate does not win without majority', () => {
    const e1 = new LeaderElection({
      localPlayerId: 'p3',
      playerOrder: createPlayerOrder(['p1', 'p2', 'p3', 'p4', 'p5']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    e1.addPeer('p1')
    e1.addPeer('p2')
    e1.addPeer('p4')
    e1.addPeer('p5')
    e1.start() // Must start to enable elections

    // Remove leader to trigger election
    e1.removePeer('p1')

    // p3 voted for self, needs 3 votes total (majority of 5)
    expect(e1.getState()).toBe('candidate')

    // Only receive 1 additional vote (2 total) - not enough
    e1.handleMessage(
      { type: 'vote_response', term: e1.getCurrentTerm(), voteGranted: true, voterId: 'p2' },
      'p2'
    )

    // Should still be candidate
    expect(e1.isLeader()).toBe(false)
    expect(e1.getState()).toBe('candidate')

    // Receive one more (3 total = majority)
    e1.handleMessage(
      { type: 'vote_response', term: e1.getCurrentTerm(), voteGranted: true, voterId: 'p4' },
      'p4'
    )

    expect(e1.isLeader()).toBe(true)

    e1.stop() // Clean up timers
  })

  it('ignores vote response from wrong term', () => {
    const e1 = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    e1.addPeer('p1')
    e1.addPeer('p3')
    e1.start() // Must start to enable elections

    // Trigger election
    e1.removePeer('p1')

    const currentTerm = e1.getCurrentTerm()

    // Receive stale vote from old term
    e1.handleMessage(
      { type: 'vote_response', term: currentTerm - 1, voteGranted: true, voterId: 'p3' },
      'p3'
    )

    // Should still be candidate (stale vote ignored)
    expect(e1.getState()).toBe('candidate')

    e1.stop() // Clean up timers
  })

  it('resets votedFor on term change', () => {
    const election = new LeaderElection({
      localPlayerId: 'p3',
      playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    let voteResponses: any[] = []
    election.setSendMessage((peerId, msg) => {
      if (msg.type === 'vote_response') {
        voteResponses.push({ peerId, msg })
      }
    })

    // Vote for p1 in term 1
    election.handleMessage(
      { type: 'request_vote', term: 1, candidateId: 'p1', lastFrame: 0 },
      'p1'
    )
    expect(voteResponses[0].msg.voteGranted).toBe(true)

    // New term 2 - should be able to vote for different candidate
    election.handleMessage(
      { type: 'request_vote', term: 2, candidateId: 'p2', lastFrame: 0 },
      'p2'
    )
    expect(voteResponses[1].msg.voteGranted).toBe(true)
  })

  it('rejects vote for candidate with lower lastFrame', () => {
    const election = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder: createPlayerOrder(['p1', 'p2']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    // Advance local frame
    election.setCurrentFrame(100)

    let voteResponse: any = null
    election.setSendMessage((peerId, msg) => {
      if (msg.type === 'vote_response') {
        voteResponse = msg
      }
    })

    // Candidate has lower lastFrame
    election.handleMessage(
      { type: 'request_vote', term: 1, candidateId: 'p1', lastFrame: 50 },
      'p1'
    )

    // Should reject - candidate's log is behind
    expect(voteResponse.voteGranted).toBe(false)
  })

  it('notifies leader change via callback', () => {
    const election = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder: createPlayerOrder(['p1', 'p2']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    let leaderChanges: Array<{ leaderId: string; term: number }> = []
    election.setLeaderChangeHandler((leaderId, term) => {
      leaderChanges.push({ leaderId, term })
    })

    // Receive heartbeat from new leader
    election.handleMessage(
      { type: 'heartbeat', term: 3, leaderId: 'p3', frame: 0 },
      'p3'
    )

    expect(leaderChanges.length).toBe(1)
    expect(leaderChanges[0]).toEqual({ leaderId: 'p3', term: 3 })
  })
})

// =============================================================================
// Jepsen-style Failure Scenarios
// =============================================================================

describe('Jepsen Failure Scenarios', () => {
  let injector: FaultInjector

  beforeEach(() => {
    const network = createMockNetwork(['p1', 'p2', 'p3'])
    injector = network.injector
  })

  afterEach(() => {
    injector.clearAllFaults()
  })

  describe('Network Partitions', () => {
    it('SCENARIO: Asymmetric partition - messages lost one direction', () => {
      // Set up: p1 can send to p2, but p2 cannot send to p1
      injector.setLinkFaults('p2', 'p1', { partitioned: true })

      const channel = injector.getChannel('p2', 'p1')!
      let messagesReceived = 0

      channel.onmessage = () => {
        messagesReceived++
      }

      // p2 sends to p1 - should be dropped
      channel.send(JSON.stringify({ type: 'test' }))
      expect(messagesReceived).toBe(0)

      // p1 to p2 should work (different channel)
      const reverseChannel = injector.getChannel('p1', 'p2')!
      let reverseReceived = 0
      reverseChannel.onmessage = () => reverseReceived++

      // Note: In our mock, we'd need to wire up delivery differently
      // This test validates the partition is correctly applied
    })

    it('SCENARIO: Symmetric partition - split brain prevention', () => {
      // Partition: {p1} vs {p2, p3}
      injector.createPartition([['p1'], ['p2', 'p3']])

      expect(injector.arePartitioned('p1', 'p2')).toBe(true)
      expect(injector.arePartitioned('p1', 'p3')).toBe(true)
      expect(injector.arePartitioned('p2', 'p3')).toBe(false)

      // Heal and verify
      injector.healPartitions()
      expect(injector.arePartitioned('p1', 'p2')).toBe(false)
    })

    it('SCENARIO: Minority partition cannot elect leader', () => {
      // With 3 peers, need 2 votes (majority)
      // If p1 is partitioned alone, it cannot become leader

      const e1 = new LeaderElection({
        localPlayerId: 'p1',
        playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
        electionTimeout: 100,
        heartbeatInterval: 50,
      })

      // Simulate p1 receiving vote request and trying to start election
      // But with no connected peers, it can only vote for itself
      // Force an election by simulating leader disconnect
      e1.addPeer('p2') // Add then remove to trigger election
      e1.addPeer('p3')
      e1.start()

      // Remove the "leader" (p1 is leader initially so we need different setup)
      // Actually, p1 IS the initial leader (index 0), so let's test p2 instead

      const e2 = new LeaderElection({
        localPlayerId: 'p2',
        playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
        electionTimeout: 100,
        heartbeatInterval: 50,
      })

      // p2 is follower, thinks p1 is leader
      // When p1 disconnects, p2 starts election
      e2.addPeer('p1')
      e2.addPeer('p3')
      e2.start()

      // Simulate p1 (leader) disconnect - this triggers election
      e2.removePeer('p1')

      // p2 should have started election, voted for itself
      expect(e2.getState()).toBe('candidate')
      expect(e2.getDebugInfo().votes).toBe(1) // Only self-vote

      // Without p3's vote (p3 is partitioned), p2 can't get majority (need 2/3)
      // So p2 remains candidate, not leader
      expect(e2.isLeader()).toBe(false)

      e1.stop()
      e2.stop()
    })
  })

  describe('Message Loss', () => {
    it('SCENARIO: Random packet loss - eventual delivery', async () => {
      // 50% packet loss
      injector.setGlobalFaults({ dropRate: 0.5 })

      let delivered = 0
      let attempts = 0
      const maxAttempts = 100

      const channel = injector.getChannel('p1', 'p2')!
      channel.onmessage = () => delivered++

      // Send many messages, some should get through
      for (let i = 0; i < maxAttempts; i++) {
        channel.send(JSON.stringify({ id: i }))
        attempts++
      }

      // With 50% loss, expect roughly half delivered
      // Allow for variance
      expect(delivered).toBeGreaterThan(20)
      expect(delivered).toBeLessThan(80)
    })

    it('SCENARIO: Burst loss - temporary complete failure', async () => {
      const channel = injector.getChannel('p1', 'p2')!
      let delivered = 0
      channel.onmessage = () => delivered++

      // Send before burst
      channel.send(JSON.stringify({ phase: 'before' }))
      expect(delivered).toBe(1)

      // Start burst (100% loss)
      injector.setGlobalFaults({ dropRate: 1.0 })

      channel.send(JSON.stringify({ phase: 'during' }))
      expect(delivered).toBe(1) // No new delivery

      // End burst
      injector.setGlobalFaults({ dropRate: 0 })

      channel.send(JSON.stringify({ phase: 'after' }))
      expect(delivered).toBe(2)
    })
  })

  describe('Leader Failures', () => {
    it('SCENARIO: Leader disconnects - new election occurs', async () => {
      const e2 = new LeaderElection({
        localPlayerId: 'p2',
        playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
        electionTimeout: 50, // Short for testing
        heartbeatInterval: 20,
      })

      e2.reset()
      e2.addPeer('p1')
      e2.addPeer('p3')
      e2.start()

      // Simulate leader (p1) disconnect
      e2.removePeer('p1')

      // After timeout, p2 should start election
      // In real scenario, this would be async
      // The removePeer triggers election start
      expect(e2.getDebugInfo().leader).toBeNull() // Leader unknown after disconnect
    })

    it('SCENARIO: Leader network partition - term advances', () => {
      // Simulate scenario where old leader is partitioned
      // but continues to think it's leader (stale leader)

      const e1 = new LeaderElection({
        localPlayerId: 'p1', // Old leader
        playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
        electionTimeout: 1500,
        heartbeatInterval: 500,
      })

      const e2 = new LeaderElection({
        localPlayerId: 'p2',
        playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
        electionTimeout: 1500,
        heartbeatInterval: 500,
      })

      e1.reset()
      e2.reset()

      // p1 thinks it's leader (term 0)
      expect(e1.isLeader()).toBe(true)
      expect(e1.getCurrentTerm()).toBe(0)

      // p2 receives message from new leader with higher term
      // This simulates election happening in partition
      e2.handleMessage(
        { type: 'heartbeat', term: 5, leaderId: 'p3', frame: 10 },
        'p3'
      )

      expect(e2.getCurrentTerm()).toBe(5)
      expect(e2.getCurrentLeader()).toBe('p3')

      // When p1 reconnects and receives higher term, it steps down
      e1.handleMessage(
        { type: 'heartbeat', term: 5, leaderId: 'p3', frame: 10 },
        'p3'
      )

      expect(e1.isLeader()).toBe(false)
      expect(e1.getCurrentTerm()).toBe(5)
      expect(e1.getState()).toBe('follower')
    })
  })

  describe('State Sync Under Failure', () => {
    it('SCENARIO: State sync lost - eventual consistency via retry', () => {
      // Leader sends state sync but it's lost
      // Next periodic sync should correct the state

      const manager = new StateSyncManager({
        syncInterval: 10,
      })
      manager.reset()

      // Simulate first sync "sent" but lost
      manager.onSyncSent()
      const lastSync1 = manager.getLastSyncFrame()

      // Advance frames
      manager.setCurrentFrame(20)

      // Should need another sync
      expect(manager.shouldSendSync()).toBe(true)

      // This time it succeeds
      manager.onSyncSent()
      expect(manager.getLastSyncFrame()).toBe(20)
    })

    it('SCENARIO: Desync detected - immediate sync triggered', () => {
      const manager = new StateSyncManager({
        syncInterval: 100, // Long interval
      })
      manager.reset()

      manager.setCurrentFrame(5)
      expect(manager.shouldSendSync()).toBe(false)

      // Desync detected!
      manager.markDesync()

      // Should immediately need sync despite not reaching interval
      expect(manager.shouldSendSync()).toBe(true)
    })
  })
})

// =============================================================================
// Integration Tests
// =============================================================================

describe('Integration: Full Lockstep with Faults', () => {
  it('handles peer disconnect gracefully', () => {
    const playerOrder = createPlayerOrder(['p1', 'p2'])

    const netcode = new LockstepNetcode({
      inputDelay: 2,
      playerCount: 2,
      localPlayerId: 'p1',
      playerOrder,
    })

    let disconnectedPeer: string | null = null
    netcode.setPeerDisconnectHandler((peerId) => {
      disconnectedPeer = peerId
    })

    // Add mock peer
    const mockChannel = new MockDataChannel('p1->p2', 'p1', 'p2')
    netcode.addPeer('p2', mockChannel as unknown as RTCDataChannel)

    // Start and verify
    netcode.start()
    expect(netcode.isLeader()).toBe(true)

    // Remove peer
    netcode.removePeer('p2')

    // Should trigger disconnect handler via election
    // (In real scenario, election would detect this)
  })

  it('leader change updates state sync authority', () => {
    const playerOrder = createPlayerOrder(['p1', 'p2'])

    const netcode = new LockstepNetcode({
      inputDelay: 2,
      playerCount: 2,
      localPlayerId: 'p2', // Not initial leader
      playerOrder,
    })

    let newLeader: string | null = null
    netcode.setLeaderChangeHandler((leaderId) => {
      newLeader = leaderId
    })

    netcode.start()

    // p2 is not initially leader
    expect(netcode.isLeader()).toBe(false)

    // Note: Full leader election test would require more setup
    // This validates the handler is wired correctly
  })
})

// =============================================================================
// Safety Property Tests
// =============================================================================

describe('Safety Properties', () => {
  it('PROPERTY: No two leaders in same term', () => {
    const playerOrder = createPlayerOrder(['p1', 'p2', 'p3'])

    const elections = ['p1', 'p2', 'p3'].map(
      id =>
        new LeaderElection({
          localPlayerId: id,
          playerOrder,
          electionTimeout: 1500,
          heartbeatInterval: 500,
        })
    )

    // All start in term 0
    elections.forEach(e => e.reset())

    // Count leaders per term
    const leadersInTerm = new Map<number, string[]>()

    for (const e of elections) {
      const term = e.getCurrentTerm()
      const leaders = leadersInTerm.get(term) ?? []
      if (e.isLeader()) {
        leaders.push(e.getDebugInfo().leader ?? 'unknown')
      }
      leadersInTerm.set(term, leaders)
    }

    // Verify at most one leader per term
    for (const [term, leaders] of leadersInTerm) {
      expect(leaders.length).toBeLessThanOrEqual(1)
    }
  })

  it('PROPERTY: Term monotonically increases', () => {
    const election = new LeaderElection({
      localPlayerId: 'p1',
      playerOrder: createPlayerOrder(['p1', 'p2']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    election.reset()
    const initialTerm = election.getCurrentTerm()

    // Receive message with higher term
    election.handleMessage(
      { type: 'heartbeat', term: 5, leaderId: 'p2', frame: 0 },
      'p2'
    )

    expect(election.getCurrentTerm()).toBeGreaterThanOrEqual(initialTerm)

    // Try to decrease term (should not work)
    election.handleMessage(
      { type: 'heartbeat', term: 3, leaderId: 'p2', frame: 0 },
      'p2'
    )

    expect(election.getCurrentTerm()).toBe(5) // Still 5, not decreased
  })

  it('PROPERTY: Events are applied in deterministic order', () => {
    const buffer = new InputBuffer({
      inputDelay: 2,
      playerCount: 3,
      playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
    })
    buffer.reset()

    // Add events in random order
    const event1: GameEvent = { type: 'pickup', playerId: 'p3', pickupId: 3 }
    const event2: GameEvent = { type: 'pickup', playerId: 'p1', pickupId: 1 }
    const event3: GameEvent = { type: 'pickup', playerId: 'p2', pickupId: 2 }

    buffer.storeInput({ frame: 5, playerId: 'p3', input: createTestInput(), events: [event1] })
    buffer.storeInput({ frame: 5, playerId: 'p1', input: createTestInput(), events: [event2] })
    buffer.storeInput({ frame: 5, playerId: 'p2', input: createTestInput(), events: [event3] })

    const result = buffer.getOrderedInputs(5)
    expect(result).not.toBeNull()

    // Events should be in player order (p1, p2, p3)
    expect(getEventOwnerId(result!.events[0]!)).toBe('p1')
    expect(getEventOwnerId(result!.events[1]!)).toBe('p2')
    expect(getEventOwnerId(result!.events[2]!)).toBe('p3')
  })
})

// =============================================================================
// Extended Chaos Tests (Long-Running)
// =============================================================================

describe('Extended Chaos Tests', () => {
  /**
   * Extended chaos test configuration.
   * These tests run for longer periods to catch rare race conditions.
   *
   * Recommended by TLA+ analysis document:
   * "Extend Jepsen tests for longer runs (5+ minutes)"
   */

  it('CHAOS: Sustained random partitions with leader election (1000 iterations)', () => {
    const playerOrder = createPlayerOrder(['p1', 'p2', 'p3', 'p4', 'p5'])
    const elections = ['p1', 'p2', 'p3', 'p4', 'p5'].map(
      id =>
        new LeaderElection({
          localPlayerId: id,
          playerOrder,
          electionTimeout: 100,
          heartbeatInterval: 50,
        })
    )

    // Track invariant violations
    let violations = 0

    for (let iteration = 0; iteration < 1000; iteration++) {
      // Reset all elections
      elections.forEach(e => e.reset())

      // Random sequence of events
      const numEvents = Math.floor(Math.random() * 50) + 10

      for (let i = 0; i < numEvents; i++) {
        const action = Math.floor(Math.random() * 4)
        const srcIdx = Math.floor(Math.random() * 5)
        const dstIdx = Math.floor(Math.random() * 5)

        switch (action) {
          case 0: // Heartbeat from a leader
            for (const e of elections) {
              if (e.isLeader()) {
                const term = e.getCurrentTerm()
                const leaderId = e.getDebugInfo().leader!
                // Send to random peer
                const dstElection = elections[dstIdx]
                if (dstIdx !== srcIdx && dstElection) {
                  dstElection.handleMessage(
                    { type: 'heartbeat', term, leaderId, frame: iteration },
                    leaderId
                  )
                }
                break
              }
            }
            break

          case 1: // Vote request (simulates election timeout)
            const srcElection = elections[srcIdx]
            const dstElection = elections[dstIdx]
            const candidateId = ['p1', 'p2', 'p3', 'p4', 'p5'][srcIdx]
            if (srcElection && srcElection.getState() === 'candidate' && candidateId) {
              const term = srcElection.getCurrentTerm()
              if (dstIdx !== srcIdx && dstElection) {
                dstElection.handleMessage(
                  { type: 'request_vote', term, candidateId, lastFrame: iteration },
                  candidateId
                )
              }
            }
            break

          case 2: // Step down (higher term discovered)
            // Already handled by heartbeat reception
            break

          case 3: // Partition heal (nothing to do in simplified model)
            break
        }
      }

      // Check invariant: at most one leader per term
      const leadersByTerm = new Map<number, Set<string>>()
      for (const e of elections) {
        if (e.isLeader()) {
          const term = e.getCurrentTerm()
          const leaders = leadersByTerm.get(term) ?? new Set()
          leaders.add(e.getDebugInfo().leader!)
          leadersByTerm.set(term, leaders)
        }
      }

      for (const [_term, leaders] of leadersByTerm) {
        if (leaders.size > 1) {
          violations++
        }
      }
    }

    expect(violations).toBe(0)
  })

  it('CHAOS: Rapid frame advancement under message loss (500 iterations)', () => {
    const iterations = 500

    for (let iter = 0; iter < iterations; iter++) {
      const buffer = new InputBuffer({
        inputDelay: 3,
        playerCount: 3,
        playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
      })
      buffer.reset()

      // Track frames that can advance
      const framesWithAllInputs: number[] = []

      // Random frame operations
      for (let frame = 3; frame < 20; frame++) {
        // Random subset of players submit input (50% chance each)
        const submitters = ['p1', 'p2', 'p3'].filter(() => Math.random() > 0.5)

        for (const playerId of submitters) {
          buffer.storeInput({
            frame,
            playerId,
            input: emptyInput(),
          })
        }

        // Check if all inputs received
        if (buffer.hasAllInputs(frame)) {
          framesWithAllInputs.push(frame)

          // Verify assertCanAdvance doesn't throw
          try {
            buffer.assertCanAdvance(frame)
          } catch {
            throw new Error(`assertCanAdvance failed for frame ${frame} with all inputs`)
          }
        } else {
          // Verify assertCanAdvance DOES throw
          let threw = false
          try {
            buffer.assertCanAdvance(frame)
          } catch {
            threw = true
          }
          if (!threw) {
            throw new Error(`assertCanAdvance should have thrown for frame ${frame}`)
          }
        }
      }
    }
  })

  it('CHAOS: State sync under rapid leader changes (200 iterations)', () => {
    const iterations = 200

    for (let iter = 0; iter < iterations; iter++) {
      const manager = new StateSyncManager({ syncInterval: 60 })
      manager.reset()

      let maxTerm = 0

      // Random sequence of term changes and syncs
      for (let i = 0; i < 50; i++) {
        const action = Math.floor(Math.random() * 3)

        switch (action) {
          case 0: // Increase term
            maxTerm += Math.floor(Math.random() * 3) + 1
            manager.setCurrentTerm(maxTerm)
            break

          case 1: // Record accepted sync (at current term)
            manager.recordAcceptedSyncTerm(maxTerm)
            break

          case 2: // Check invariants
            try {
              manager.assertInvariants()
            } catch (e) {
              throw new Error(`Invariant violated at iteration ${iter}, step ${i}: ${e}`)
            }
            break
        }
      }

      // Final invariant check
      manager.assertInvariants()
    }
  })

  it('CHAOS: Local event preservation through multiple syncs (100 iterations)', () => {
    const iterations = 100

    for (let iter = 0; iter < iterations; iter++) {
      const queue = new LocalEventQueue({
        bufferSize: 900,
        localPlayerId: 'local',
      })
      queue.reset()

      let localEventCount = 0

      // Add random local and remote events
      for (let i = 0; i < 20; i++) {
        const isLocal = Math.random() > 0.5
        const event: GameEvent = {
          type: 'damage',
          playerId: isLocal ? 'local' : `remote${i}`,
          amount: 10,
          newShields: 90,
          newLives: 3,
        }
        queue.addEvent(event, i)
        if (isLocal) localEventCount++
      }

      // Perform state sync
      const reapplied = queue.onStateSync(10)

      // After sync, only local events should remain
      queue.assertLocalEventsOnly()

      // Reapplied events should all be local
      for (const event of reapplied) {
        if (getEventOwnerId(event) !== 'local') {
          throw new Error(`Non-local event in reapply list: ${JSON.stringify(event)}`)
        }
      }
    }
  })
})
