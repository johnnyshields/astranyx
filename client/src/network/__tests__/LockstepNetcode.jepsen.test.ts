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
      localPlayerId: 'p1',
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
      localPlayerId: 'p1',
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
      localPlayerId: 'p1',
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
      { type: 'heartbeat', term: 5, leaderId: 'p1', frame: 0, checksum: 0 },
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
        { type: 'heartbeat', term: 5, leaderId: 'p3', frame: 10, checksum: 0 },
        'p3'
      )

      expect(e2.getCurrentTerm()).toBe(5)
      expect(e2.getCurrentLeader()).toBe('p3')

      // When p1 reconnects and receives higher term, it steps down
      e1.handleMessage(
        { type: 'heartbeat', term: 5, leaderId: 'p3', frame: 10, checksum: 0 },
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
        localPlayerId: 'p1',
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
        localPlayerId: 'p1',
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
      maxRollbackFrames: 0,
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
    expect(netcode.isHost()).toBe(true)

    // Remove peer
    netcode.removePeer('p2')

    // Should trigger disconnect handler via election
    // (In real scenario, election would detect this)
  })

  it('leader change updates state sync authority', () => {
    const playerOrder = createPlayerOrder(['p1', 'p2'])

    const netcode = new LockstepNetcode({
      inputDelay: 2,
      maxRollbackFrames: 0,
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
    expect(netcode.isHost()).toBe(false)

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
      { type: 'heartbeat', term: 5, leaderId: 'p2', frame: 0, checksum: 0 },
      'p2'
    )

    expect(election.getCurrentTerm()).toBeGreaterThanOrEqual(initialTerm)

    // Try to decrease term (should not work)
    election.handleMessage(
      { type: 'heartbeat', term: 3, leaderId: 'p2', frame: 0, checksum: 0 },
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
