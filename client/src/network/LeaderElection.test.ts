import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest'
import { LeaderElection, type LeaderElectionConfig } from './LeaderElection'
import type {
  HeartbeatMessage,
  HeartbeatAckMessage,
  VoteResponseMessage,
} from './types'

function createConfig(overrides?: Partial<LeaderElectionConfig>): LeaderElectionConfig {
  return {
    localPlayerId: 'player1',
    playerOrder: new Map([
      ['player1', 0],
      ['player2', 1],
      ['player3', 2],
    ]),
    electionTimeoutMs: 1500,
    heartbeatMs: 500,
    ...overrides,
  }
}

describe('LeaderElection', () => {
  let election: LeaderElection
  let sendMessageMock: ReturnType<typeof vi.fn>

  beforeEach(() => {
    vi.useFakeTimers()
    sendMessageMock = vi.fn()
    election = new LeaderElection(createConfig())
    election.setSendMessage(sendMessageMock as unknown as (peerId: string, message: unknown) => void)
  })

  afterEach(() => {
    election.stop()
    vi.useRealTimers()
  })

  describe('constructor', () => {
    it('should initialize with player 0 as leader', () => {
      const config = createConfig({ localPlayerId: 'player1' })
      const e = new LeaderElection(config)
      expect(e.getCurrentLeader()).toBe('player1')
      expect(e.isLeader()).toBe(true)
    })

    it('should not be leader if not player 0', () => {
      const config = createConfig({ localPlayerId: 'player2' })
      const e = new LeaderElection(config)
      expect(e.getCurrentLeader()).toBe('player1')
      expect(e.isLeader()).toBe(false)
    })

    it('should start at term 0', () => {
      expect(election.getCurrentTerm()).toBe(0)
    })
  })

  describe('peer management', () => {
    it('should add peers', () => {
      election.addPeer('player2')
      expect(election.getConnectedPeerCount()).toBe(1)

      election.addPeer('player3')
      expect(election.getConnectedPeerCount()).toBe(2)
    })

    it('should remove peers', () => {
      election.addPeer('player2')
      election.addPeer('player3')
      election.removePeer('player2')

      expect(election.getConnectedPeerCount()).toBe(1)
    })

    it('should start election when leader disconnects', () => {
      const config = createConfig({ localPlayerId: 'player2' })
      const e = new LeaderElection(config)
      e.setSendMessage(sendMessageMock as unknown as (peerId: string, message: unknown) => void)
      e.start()

      e.addPeer('player1') // Leader
      e.addPeer('player3')

      // Leader disconnects
      e.removePeer('player1')

      // Should have incremented term and sent RequestVote
      expect(e.getCurrentTerm()).toBe(1)
      e.stop()
    })
  })

  describe('heartbeat', () => {
    it('should send heartbeats when leader', () => {
      election.addPeer('player2')
      election.start()

      // Initial heartbeat should be sent immediately
      expect(sendMessageMock).toHaveBeenCalled()
      const call = sendMessageMock.mock.calls[0]!
      expect(call[1].type).toBe('heartbeat')
    })

    it('should include timestamp in heartbeat', () => {
      election.addPeer('player2')
      election.start()

      const heartbeat = sendMessageMock.mock.calls[0]![1] as HeartbeatMessage
      expect(heartbeat.timestamp).toBeDefined()
      expect(typeof heartbeat.timestamp).toBe('number')
    })

    it('should send heartbeats periodically', () => {
      election.addPeer('player2')
      election.start()

      sendMessageMock.mockClear()
      vi.advanceTimersByTime(500) // Heartbeat interval

      expect(sendMessageMock).toHaveBeenCalled()
    })
  })

  describe('heartbeat acknowledgment', () => {
    it('should send ack with echoed timestamp', () => {
      // Create follower
      const config = createConfig({ localPlayerId: 'player2' })
      const follower = new LeaderElection(config)
      const followerSend = vi.fn()
      follower.setSendMessage(followerSend)
      follower.addPeer('player1')
      follower.start()

      // Receive heartbeat with timestamp
      const heartbeat: HeartbeatMessage = {
        type: 'heartbeat',
        term: 0,
        leaderId: 'player1',
        frame: 100,
        timestamp: 1700000000000,
      }

      follower.handleMessage(heartbeat, 'player1')

      // Should have sent ack with same timestamp
      expect(followerSend).toHaveBeenCalled()
      const ack = followerSend.mock.calls[0]![1] as HeartbeatAckMessage
      expect(ack.type).toBe('heartbeat_ack')
      expect(ack.timestamp).toBe(1700000000000)

      follower.stop()
    })
  })

  describe('RTT measurement', () => {
    it('should calculate RTT from heartbeat/ack', () => {
      election.addPeer('player2')
      election.start()

      // Get the timestamp from sent heartbeat
      const heartbeat = sendMessageMock.mock.calls[0]![1] as HeartbeatMessage
      const sentTimestamp = heartbeat.timestamp!

      // Simulate receiving ack 50ms later
      vi.advanceTimersByTime(50)

      const ack: HeartbeatAckMessage = {
        type: 'heartbeat_ack',
        term: 0,
        peerId: 'player2',
        frame: 0,
        timestamp: sentTimestamp,
      }

      election.handleMessage(ack, 'player2')

      // RTT should be ~50ms
      const rtt = election.getPeerRtt('player2')
      expect(rtt).toBeGreaterThanOrEqual(50)
    })

    it('should track RTT for multiple peers', () => {
      election.addPeer('player2')
      election.addPeer('player3')
      election.start()

      const heartbeat = sendMessageMock.mock.calls[0]![1] as HeartbeatMessage

      // Ack from player2 after 30ms
      vi.advanceTimersByTime(30)
      election.handleMessage({
        type: 'heartbeat_ack',
        term: 0,
        peerId: 'player2',
        frame: 0,
        timestamp: heartbeat.timestamp,
      }, 'player2')

      // Ack from player3 after another 40ms (70ms total)
      vi.advanceTimersByTime(40)
      election.handleMessage({
        type: 'heartbeat_ack',
        term: 0,
        peerId: 'player3',
        frame: 0,
        timestamp: heartbeat.timestamp,
      }, 'player3')

      const rtt2 = election.getPeerRtt('player2')
      const rtt3 = election.getPeerRtt('player3')

      expect(rtt2).toBeGreaterThanOrEqual(30)
      expect(rtt3).toBeGreaterThan(rtt2)
    })

    it('should average multiple RTT samples', () => {
      election.addPeer('player2')
      election.start()

      // Simulate multiple heartbeat/ack cycles
      for (let i = 0; i < 5; i++) {
        sendMessageMock.mockClear()
        vi.advanceTimersByTime(500) // Trigger new heartbeat

        const heartbeat = sendMessageMock.mock.calls.find(
          c => c[1].type === 'heartbeat'
        )?.[1] as HeartbeatMessage

        if (heartbeat) {
          vi.advanceTimersByTime(50 + i * 10) // Varying RTT

          election.handleMessage({
            type: 'heartbeat_ack',
            term: 0,
            peerId: 'player2',
            frame: 0,
            timestamp: heartbeat.timestamp,
          }, 'player2')
        }
      }

      const rtt = election.getPeerRtt('player2')
      expect(rtt).toBeGreaterThan(0)
    })

    it('should return 0 for unknown peer', () => {
      expect(election.getPeerRtt('unknown')).toBe(0)
    })

    it('should get max RTT across all peers', () => {
      election.addPeer('player2')
      election.addPeer('player3')
      election.start()

      const heartbeat = sendMessageMock.mock.calls[0]![1] as HeartbeatMessage

      // Different RTTs for different peers
      vi.advanceTimersByTime(30)
      election.handleMessage({
        type: 'heartbeat_ack',
        term: 0,
        peerId: 'player2',
        frame: 0,
        timestamp: heartbeat.timestamp,
      }, 'player2')

      vi.advanceTimersByTime(70) // 100ms total
      election.handleMessage({
        type: 'heartbeat_ack',
        term: 0,
        peerId: 'player3',
        frame: 0,
        timestamp: heartbeat.timestamp,
      }, 'player3')

      const maxRtt = election.getMaxRtt()
      expect(maxRtt).toBeGreaterThanOrEqual(100)
    })

    it('should get all RTT samples', () => {
      election.addPeer('player2')
      election.start()

      const heartbeat = sendMessageMock.mock.calls[0]![1] as HeartbeatMessage

      vi.advanceTimersByTime(50)
      election.handleMessage({
        type: 'heartbeat_ack',
        term: 0,
        peerId: 'player2',
        frame: 0,
        timestamp: heartbeat.timestamp,
      }, 'player2')

      const allSamples = election.getAllRttSamples()
      expect(allSamples.has('player2')).toBe(true)
      expect(allSamples.get('player2')!.length).toBeGreaterThan(0)
    })

    it('should call RTT update handler', () => {
      const rttHandler = vi.fn()
      election.setRttUpdateHandler(rttHandler)
      election.addPeer('player2')
      election.start()

      const heartbeat = sendMessageMock.mock.calls[0]![1] as HeartbeatMessage

      vi.advanceTimersByTime(50)
      election.handleMessage({
        type: 'heartbeat_ack',
        term: 0,
        peerId: 'player2',
        frame: 0,
        timestamp: heartbeat.timestamp,
      }, 'player2')

      expect(rttHandler).toHaveBeenCalled()
      expect(rttHandler).toHaveBeenCalledWith('player2', expect.any(Number))
    })

    it('should clear RTT data on reset', () => {
      election.addPeer('player2')
      election.start()

      const heartbeat = sendMessageMock.mock.calls[0]![1] as HeartbeatMessage

      vi.advanceTimersByTime(50)
      election.handleMessage({
        type: 'heartbeat_ack',
        term: 0,
        peerId: 'player2',
        frame: 0,
        timestamp: heartbeat.timestamp,
      }, 'player2')

      expect(election.getPeerRtt('player2')).toBeGreaterThan(0)

      election.reset()

      expect(election.getPeerRtt('player2')).toBe(0)
    })
  })

  describe('election process', () => {
    it('should start election on timeout', () => {
      const config = createConfig({ localPlayerId: 'player2' })
      const follower = new LeaderElection(config)
      follower.setSendMessage(sendMessageMock as unknown as (peerId: string, message: unknown) => void)
      follower.addPeer('player1')
      follower.addPeer('player3')
      follower.start()

      sendMessageMock.mockClear()

      // Advance past election timeout
      vi.advanceTimersByTime(2500)

      // Should have sent RequestVote
      const votes = sendMessageMock.mock.calls.filter(
        c => c[1].type === 'request_vote'
      )
      expect(votes.length).toBeGreaterThan(0)

      follower.stop()
    })

    it('should become leader with majority votes', () => {
      const config = createConfig({ localPlayerId: 'player2' })
      const candidate = new LeaderElection(config)
      const leaderHandler = vi.fn()
      candidate.setSendMessage(sendMessageMock as unknown as (peerId: string, message: unknown) => void)
      candidate.setLeaderChangeHandler(leaderHandler)
      candidate.addPeer('player1')
      candidate.addPeer('player3')
      candidate.start()

      // Trigger election
      vi.advanceTimersByTime(2500)

      // Grant vote from player3
      const voteResponse: VoteResponseMessage = {
        type: 'vote_response',
        term: 1,
        voteGranted: true,
        voterId: 'player3',
      }
      candidate.handleMessage(voteResponse, 'player3')

      // Should now be leader (self vote + player3 = 2/3 majority)
      expect(candidate.isLeader()).toBe(true)
      expect(leaderHandler).toHaveBeenCalledWith('player2', 1)

      candidate.stop()
    })
  })

  describe('debug info', () => {
    it('should return debug info', () => {
      election.addPeer('player2')

      const info = election.getDebugInfo()

      expect(info.state).toBeDefined()
      expect(info.term).toBeDefined()
      expect(info.leader).toBeDefined()
      expect(info.votedFor).toBeDefined()
      expect(info.votes).toBeDefined()
      expect(info.connectedPeers).toBe(1)
    })
  })

  describe('invariant assertions', () => {
    it('should pass invariant checks in valid state', () => {
      election.start()
      expect(() => election.assertInvariants()).not.toThrow()
    })
  })
})
