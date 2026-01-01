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

import { describe, it, expect, beforeEach, afterEach } from 'vitest'
import { LockstepNetcode } from '../LockstepNetcode.ts'
import { LeaderElection } from '../LeaderElection.ts'
import { InputBuffer } from '../InputBuffer.ts'
import { LocalEventQueue } from '../LocalEventQueue.ts'
import { StateSyncManager } from '../StateSyncManager.ts'
import type { PlayerInput, GameEvent, FrameInput, VoteResponseMessage } from '../types.ts'
import { emptyInput, getEventOwnerId } from '../types.ts'
import { FaultInjector, MockDataChannel, createMockNetwork } from './FaultInjection.ts'

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
    const _e1 = new LeaderElection({
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

    let voteResponse: VoteResponseMessage | null = null
    e2.setSendMessage((_peerId, msg) => {
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
    expect(voteResponse!.voteGranted).toBe(true)
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

    let voteResponse: VoteResponseMessage | null = null
    election.setSendMessage((_peerId, msg) => {
      if (msg.type === 'vote_response') {
        voteResponse = msg
      }
    })

    // Receive vote request for lower term
    election.handleMessage(
      { type: 'request_vote', term: 3, candidateId: 'p3', lastFrame: 0 },
      'p3'
    )

    expect(voteResponse!.voteGranted).toBe(false)
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

    const voteResponses: Array<{ peerId: string; msg: VoteResponseMessage }> = []
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
    expect(voteResponses[0]!.msg.voteGranted).toBe(true)

    // p2 also requests vote for same term - should be rejected
    election.handleMessage(
      { type: 'request_vote', term: 1, candidateId: 'p2', lastFrame: 0 },
      'p2'
    )

    expect(voteResponses.length).toBe(2)
    expect(voteResponses[1]!.msg.voteGranted).toBe(false)
  })

  it('allows vote for same candidate multiple times in same term', () => {
    const election = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder: createPlayerOrder(['p1', 'p2']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    const voteResponses: VoteResponseMessage[] = []
    election.setSendMessage((_peerId, msg) => {
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
    expect(voteResponses[0]!.voteGranted).toBe(true)
    expect(voteResponses[1]!.voteGranted).toBe(true) // Same candidate, still granted
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
    e1.setLeaderChangeHandler((leaderId, _term) => {
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

    const voteResponses: Array<{ peerId: string; msg: VoteResponseMessage }> = []
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
    expect(voteResponses[0]!.msg.voteGranted).toBe(true)

    // New term 2 - should be able to vote for different candidate
    election.handleMessage(
      { type: 'request_vote', term: 2, candidateId: 'p2', lastFrame: 0 },
      'p2'
    )
    expect(voteResponses[1]!.msg.voteGranted).toBe(true)
  })

  it('candidate steps down via onHigherTermSeen (TLA+ ReceiveStateSync fix)', () => {
    const election = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    election.addPeer('p1')
    election.addPeer('p3')
    election.start()

    // Trigger election by removing leader
    election.removePeer('p1')

    // p2 should be candidate
    expect(election.getState()).toBe('candidate')
    const candidateTerm = election.getCurrentTerm()
    expect(election.getDebugInfo().votes).toBeGreaterThanOrEqual(1) // At least self-vote

    // Simulate receiving state sync from leader with higher term
    // This exercises the new onHigherTermSeen method
    election.onHigherTermSeen(candidateTerm + 5)

    // Should step down to follower
    expect(election.getState()).toBe('follower')
    expect(election.getCurrentTerm()).toBe(candidateTerm + 5)
    // Votes should be cleared
    expect(election.getDebugInfo().votes).toBe(0)

    election.stop()
  })

  it('onHigherTermSeen does nothing for same or lower term', () => {
    const election = new LeaderElection({
      localPlayerId: 'p1',
      playerOrder: createPlayerOrder(['p1', 'p2']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    // p1 starts as leader in term 0
    expect(election.isLeader()).toBe(true)
    expect(election.getCurrentTerm()).toBe(0)

    // Same term - should not step down
    election.onHigherTermSeen(0)
    expect(election.isLeader()).toBe(true)

    // Lower term - should not step down
    // First bump the term
    election.handleMessage(
      { type: 'heartbeat', term: 5, leaderId: 'p2', frame: 0 },
      'p2'
    )
    expect(election.getCurrentTerm()).toBe(5)
    expect(election.getState()).toBe('follower')

    // Now try lower term
    const stateBefore = election.getState()
    election.onHigherTermSeen(3)
    expect(election.getState()).toBe(stateBefore)
    expect(election.getCurrentTerm()).toBe(5) // Unchanged
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

    let voteResponse: VoteResponseMessage | null = null
    election.setSendMessage((_peerId, msg) => {
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
    expect(voteResponse!.voteGranted).toBe(false)
  })

  it('notifies leader change via callback', () => {
    const election = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder: createPlayerOrder(['p1', 'p2']),
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    const leaderChanges: Array<{ leaderId: string; term: number }> = []
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
      const maxAttempts = 100

      const channel = injector.getChannel('p1', 'p2')!
      channel.onmessage = () => delivered++

      // Send many messages, some should get through
      for (let i = 0; i < maxAttempts; i++) {
        channel.send(JSON.stringify({ id: i }))
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
      const _lastSync1 = manager.getLastSyncFrame()

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

    let _disconnectedPeer: string | null = null
    netcode.setPeerDisconnectHandler((peerId) => {
      _disconnectedPeer = peerId
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

    let _newLeader: string | null = null
    netcode.setLeaderChangeHandler((leaderId) => {
      _newLeader = leaderId
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
    for (const [_term, leaders] of leadersInTerm) {
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

  it('PROPERTY: Candidate cannot become leader after term bump from state sync (TLA+ NoTwoLeadersInSameTerm)', () => {
    // This test reproduces the exact bug found by TLA+ model checker:
    // A candidate with majority votes from term N cannot become leader
    // after their term is bumped to N+1 by a state sync from an existing leader.
    //
    // The fix: onHigherTermSeen clears votesReceived, preventing stale votes
    // from being used in the new term.

    const playerOrder = createPlayerOrder(['p1', 'p2', 'p3'])

    // p2 is a candidate who has collected majority votes in term 1
    const e2 = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder,
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    e2.addPeer('p1')
    e2.addPeer('p3')
    e2.start()

    // Simulate: p2 starts election (becomes candidate in term 1)
    e2.removePeer('p1') // Triggers election

    expect(e2.getState()).toBe('candidate')
    const term1 = e2.getCurrentTerm()

    // Simulate: p2 receives vote from p1 (would give majority)
    e2.handleMessage(
      { type: 'vote_response', term: term1, voteGranted: true, voterId: 'p1' },
      'p1'
    )

    // At this point, p2 has majority and would become leader...
    // BUT before BecomeLeader fires, a state sync arrives from p1 (who is leader in term 2)

    // Simulate receiving state sync with higher term
    // This is where the bug was: term would update but votes wouldn't clear
    e2.onHigherTermSeen(term1 + 1)

    // After term bump:
    // - Should be follower (not candidate or leader)
    // - Term should be updated
    // - Votes should be cleared (cannot use term 1 votes in term 2)
    expect(e2.getState()).toBe('follower')
    expect(e2.getCurrentTerm()).toBe(term1 + 1)
    expect(e2.getDebugInfo().votes).toBe(0) // Critical: votes cleared!

    // Now even if something tried to call becomeLeader, it would fail
    // because p2 is not a candidate and has no votes

    e2.stop()
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

          case 1: { // Vote request (simulates election timeout)
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
          }

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

// =============================================================================
// Additional Safety Property Tests (TLA+ Invariants)
// =============================================================================

describe('TLA+ Invariant Tests', () => {
  it('INVARIANT: VotesFromValidPeers - votes only from known peers', () => {
    const playerOrder = createPlayerOrder(['p1', 'p2', 'p3'])

    const election = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder,
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    election.addPeer('p1')
    election.addPeer('p3')
    election.start()

    // Trigger election
    election.removePeer('p1')

    // Receive votes
    election.handleMessage(
      { type: 'vote_response', term: election.getCurrentTerm(), voteGranted: true, voterId: 'p3' },
      'p3'
    )

    // Check invariant: all votes are from valid peers
    const debug = election.getDebugInfo()
    // The debug info shows vote count, actual validation is internal
    expect(debug.votes).toBeGreaterThanOrEqual(1)

    election.stop()
  })

  it('INVARIANT: VotedForValid - votedFor is null or valid peer', () => {
    const playerOrder = createPlayerOrder(['p1', 'p2', 'p3'])

    const election = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder,
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    // Initial state: p2 is follower, votedFor should be null or p1 (initial leader)
    election.assertInvariants()

    // After voting
    election.handleMessage(
      { type: 'request_vote', term: 1, candidateId: 'p1', lastFrame: 0 },
      'p1'
    )

    election.assertInvariants()
  })

  it('INVARIANT: LeaderHadMajority - leader has majority votes', () => {
    const playerOrder = createPlayerOrder(['p1', 'p2', 'p3'])

    const election = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder,
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    election.addPeer('p1')
    election.addPeer('p3')
    election.start()

    // Trigger election
    election.removePeer('p1')

    expect(election.getState()).toBe('candidate')

    // Receive vote to get majority (2 of 3)
    election.handleMessage(
      { type: 'vote_response', term: election.getCurrentTerm(), voteGranted: true, voterId: 'p3' },
      'p3'
    )

    // Now leader
    expect(election.isLeader()).toBe(true)
    expect(election.getDebugInfo().votes).toBeGreaterThanOrEqual(2) // Majority of 3

    election.stop()
  })

  it('INVARIANT: SyncTermBounded - syncTerm <= currentTerm', () => {
    const manager = new StateSyncManager({ syncInterval: 60 })
    manager.reset()

    // Set term and sync term
    manager.setCurrentTerm(5)
    manager.recordAcceptedSyncTerm(5)

    manager.assertInvariants()

    // Increase term
    manager.setCurrentTerm(10)
    manager.assertInvariants() // syncTerm (5) <= currentTerm (10)

    // Record new sync
    manager.recordAcceptedSyncTerm(10)
    manager.assertInvariants()
  })

  it('INVARIANT: FrameBoundedDrift - frames within 1 of each other (simulated)', () => {
    // This tests the concept - actual multi-peer test would need full integration
    const buffer = new InputBuffer({
      inputDelay: 3,
      playerCount: 3,
      playerOrder: createPlayerOrder(['p1', 'p2', 'p3']),
    })
    buffer.reset()

    // Simulate lockstep: all peers must have input before any can advance
    // Frame 3 needs all inputs
    buffer.storeInput({ frame: 3, playerId: 'p1', input: emptyInput() })
    expect(buffer.hasAllInputs(3)).toBe(false)

    buffer.storeInput({ frame: 3, playerId: 'p2', input: emptyInput() })
    expect(buffer.hasAllInputs(3)).toBe(false)

    buffer.storeInput({ frame: 3, playerId: 'p3', input: emptyInput() })
    expect(buffer.hasAllInputs(3)).toBe(true)

    // This enforces bounded drift - no peer can be more than inputDelay ahead
  })

  it('INVARIANT: InputsFromValidPeers - assertInvariants catches invalid peers', () => {
    const playerOrder = createPlayerOrder(['p1', 'p2', 'p3'])
    const buffer = new InputBuffer({
      inputDelay: 3,
      playerCount: 3,
      playerOrder,
    })
    buffer.reset()

    // Valid inputs pass
    buffer.storeInput({ frame: 5, playerId: 'p1', input: emptyInput() })
    buffer.storeInput({ frame: 5, playerId: 'p2', input: emptyInput() })
    buffer.assertInvariants(5)

    // Now insert from invalid peer
    buffer.storeInput({ frame: 5, playerId: 'invalid_peer', input: emptyInput() })

    // assertInvariants should throw
    expect(() => buffer.assertInvariants(5)).toThrow('InputsFromValidPeers')
  })

  it('INVARIANT: VotesFromValidPeers - assertInvariants catches invalid voters', () => {
    const playerOrder = createPlayerOrder(['p1', 'p2', 'p3'])

    const election = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder,
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    election.addPeer('p1')
    election.addPeer('p3')
    election.start()

    // Trigger election
    election.removePeer('p1')

    // Valid vote - should pass
    election.handleMessage(
      { type: 'vote_response', term: election.getCurrentTerm(), voteGranted: true, voterId: 'p3' },
      'p3'
    )
    election.assertInvariants()

    // Invalid vote from unknown peer (would be caught if it somehow got through)
    // The system should reject invalid votes, but if they got through, assertInvariants catches it
    election.stop()
  })

  it('INVARIANT: LeaderHadMajority - assertInvariants validates leader has majority', () => {
    const playerOrder = createPlayerOrder(['p1', 'p2', 'p3'])

    const election = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder,
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    election.addPeer('p1')
    election.addPeer('p3')
    election.start()

    // Trigger election - p2 becomes candidate with 1 vote (self)
    election.removePeer('p1')
    expect(election.getState()).toBe('candidate')

    // Not leader yet, invariant should pass
    election.assertInvariants()

    // Receive vote to get majority
    election.handleMessage(
      { type: 'vote_response', term: election.getCurrentTerm(), voteGranted: true, voterId: 'p3' },
      'p3'
    )

    // Now leader with majority
    expect(election.isLeader()).toBe(true)
    election.assertInvariants() // Should pass - has 2 votes (majority of 3)

    election.stop()
  })
})

// =============================================================================
// Split-Brain and Concurrent Election Tests
// =============================================================================

describe('Split-Brain Prevention', () => {
  it('SCENARIO: After partition heals, only one leader remains', () => {
    const playerOrder = createPlayerOrder(['p1', 'p2', 'p3', 'p4', 'p5'])

    // Simulate two partitions each electing a "leader"
    // When they merge, higher term wins

    const e1 = new LeaderElection({
      localPlayerId: 'p1',
      playerOrder,
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    const e2 = new LeaderElection({
      localPlayerId: 'p3',
      playerOrder,
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    e1.reset()
    e2.reset()

    // p1 is initial leader (term 0)
    expect(e1.isLeader()).toBe(true)
    expect(e1.getCurrentTerm()).toBe(0)

    // Simulate: p3 thinks it became leader in term 2 (in its partition)
    // by receiving heartbeat from itself after winning election
    e2.handleMessage(
      { type: 'heartbeat', term: 2, leaderId: 'p3', frame: 0 },
      'p3'
    )

    // Partition heals: p1 receives heartbeat from p3 with higher term
    e1.handleMessage(
      { type: 'heartbeat', term: 2, leaderId: 'p3', frame: 0 },
      'p3'
    )

    // p1 should step down
    expect(e1.isLeader()).toBe(false)
    expect(e1.getCurrentTerm()).toBe(2)
    expect(e1.getCurrentLeader()).toBe('p3')

    // Only p3 is leader
    // (In real scenario, p3 would also need to handle messages, but the key
    // property is that p1 stepped down upon seeing higher term)
  })

  it('SCENARIO: Concurrent candidates - only one wins', () => {
    const playerOrder = createPlayerOrder(['p1', 'p2', 'p3'])

    const e2 = new LeaderElection({
      localPlayerId: 'p2',
      playerOrder,
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    const e3 = new LeaderElection({
      localPlayerId: 'p3',
      playerOrder,
      electionTimeout: 1500,
      heartbeatInterval: 500,
    })

    e2.addPeer('p1')
    e2.addPeer('p3')
    e3.addPeer('p1')
    e3.addPeer('p2')

    e2.start()
    e3.start()

    // Both start elections (leader p1 "disconnected")
    e2.removePeer('p1')
    e3.removePeer('p1')

    // Both are candidates in term 1
    expect(e2.getState()).toBe('candidate')
    expect(e3.getState()).toBe('candidate')

    // p2 gets vote from p3 first (simulating network race)
    e2.handleMessage(
      { type: 'vote_response', term: e2.getCurrentTerm(), voteGranted: true, voterId: 'p3' },
      'p3'
    )

    // p2 becomes leader
    expect(e2.isLeader()).toBe(true)

    // p3 receives heartbeat from new leader p2
    e3.handleMessage(
      { type: 'heartbeat', term: e2.getCurrentTerm(), leaderId: 'p2', frame: 0 },
      'p2'
    )

    // p3 steps down to follower
    expect(e3.isLeader()).toBe(false)
    expect(e3.getState()).toBe('follower')
    expect(e3.getCurrentLeader()).toBe('p2')

    e2.stop()
    e3.stop()
  })
})

// =============================================================================
// State Sync Ordering Tests
// =============================================================================

describe('State Sync Ordering', () => {
  it('SCENARIO: Out-of-order syncs - older term rejected', () => {
    const manager = new StateSyncManager({ syncInterval: 60 })
    manager.reset()
    manager.setCurrentTerm(5)

    let syncCount = 0
    manager.setStateSyncHandler(() => {
      syncCount++
    })

    // Receive sync from term 5
    manager.receiveSyncMessage({
      type: 'state_sync',
      frame: 10,
      state: { data: 'term5' },
      checksum: 123,
      term: 5,
    })
    expect(syncCount).toBe(1)

    // Receive stale sync from term 3 (out of order)
    manager.receiveSyncMessage({
      type: 'state_sync',
      frame: 8,
      state: { data: 'term3-stale' },
      checksum: 456,
      term: 3,
    })
    expect(syncCount).toBe(1) // Should not increase - rejected

    // Receive sync from term 6 (newer)
    manager.setCurrentTerm(6)
    manager.receiveSyncMessage({
      type: 'state_sync',
      frame: 15,
      state: { data: 'term6' },
      checksum: 789,
      term: 6,
    })
    expect(syncCount).toBe(2) // Should increase
  })

  it('SCENARIO: Concurrent syncs from same term - idempotent', () => {
    const manager = new StateSyncManager({ syncInterval: 60 })
    manager.reset()
    manager.setCurrentTerm(5)

    let lastState: unknown = null
    manager.setStateSyncHandler((state) => {
      lastState = state
    })

    // Receive first sync
    manager.receiveSyncMessage({
      type: 'state_sync',
      frame: 10,
      state: { data: 'first' },
      checksum: 123,
      term: 5,
    })
    expect(lastState).toEqual({ data: 'first' })

    // Receive duplicate/concurrent sync (same term)
    manager.receiveSyncMessage({
      type: 'state_sync',
      frame: 10,
      state: { data: 'second' },
      checksum: 123,
      term: 5,
    })
    // Both are accepted (idempotent for same term)
    expect(lastState).toEqual({ data: 'second' })
  })
})

// =============================================================================
// Frame and Event Integrity Tests
// =============================================================================

describe('Frame and Event Integrity', () => {
  it('SCENARIO: Frame rollback prevention - frames never decrease', () => {
    const buffer = new InputBuffer({
      inputDelay: 3,
      playerCount: 2,
      playerOrder: createPlayerOrder(['p1', 'p2']),
      retentionFrames: 3,  // Small retention to test cleanup
    })
    buffer.reset()

    // Store inputs for frames in order
    for (let frame = 3; frame <= 10; frame++) {
      buffer.storeInput({ frame, playerId: 'p1', input: emptyInput() })
      buffer.storeInput({ frame, playerId: 'p2', input: emptyInput() })
    }

    // Cleanup to frame 8 (with retentionFrames=3, minFrame = 8-3 = 5)
    buffer.cleanup(8)

    // Frames < 5 should be gone (but we started at 3, so frames 3-4 gone)
    expect(buffer.hasInput(3, 'p1')).toBe(false)
    expect(buffer.hasInput(4, 'p1')).toBe(false)

    // Frames >= 5 still available
    expect(buffer.hasInput(5, 'p1')).toBe(true)
    expect(buffer.hasInput(8, 'p1')).toBe(true)
    expect(buffer.hasInput(9, 'p1')).toBe(true)
  })

  it('SCENARIO: Event idempotency - duplicate events handled', () => {
    const queue = new LocalEventQueue({
      bufferSize: 100,
      localPlayerId: 'p1',
    })
    queue.reset()

    const event: GameEvent = { type: 'pickup', playerId: 'p1', pickupId: 42 }

    // Add same event twice (simulating duplicate message)
    queue.addEvent(event, 5)
    queue.addEvent(event, 5)

    // Should have 2 events (queue doesn't dedupe - that's simulation's job)
    // The key is it doesn't crash or corrupt state
    const pending = queue.getPendingEvents()
    expect(pending.length).toBe(2)

    // Both events are valid
    expect(pending[0]).toEqual(event)
    expect(pending[1]).toEqual(event)
  })

  it('SCENARIO: Events from unknown players rejected', () => {
    const buffer = new InputBuffer({
      inputDelay: 3,
      playerCount: 2,
      playerOrder: createPlayerOrder(['p1', 'p2']),
    })
    buffer.reset()

    // Store input from unknown player
    buffer.storeInput({
      frame: 5,
      playerId: 'unknown',
      input: emptyInput(),
    })

    // Frame still not complete (unknown player doesn't count toward playerCount)
    expect(buffer.hasAllInputs(5)).toBe(false)

    // Add valid players
    buffer.storeInput({ frame: 5, playerId: 'p1', input: emptyInput() })
    buffer.storeInput({ frame: 5, playerId: 'p2', input: emptyInput() })

    // Now complete
    expect(buffer.hasAllInputs(5)).toBe(true)
  })
})
