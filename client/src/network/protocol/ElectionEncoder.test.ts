import { describe, it, expect } from 'vitest'
import {
  encodeRequestVote,
  decodeRequestVote,
  encodeVoteResponse,
  decodeVoteResponse,
  encodeHeartbeat,
  decodeHeartbeat,
  encodeHeartbeatAck,
  decodeHeartbeatAck,
  REQUEST_VOTE_SIZE,
  VOTE_RESPONSE_SIZE,
  HEARTBEAT_SIZE,
  HEARTBEAT_SIZE_WITH_TIMESTAMP,
  HEARTBEAT_ACK_SIZE,
  HEARTBEAT_ACK_SIZE_WITH_TIMESTAMP,
} from './ElectionEncoder'
import type {
  RequestVoteMessage,
  VoteResponseMessage,
  HeartbeatMessage,
  HeartbeatAckMessage,
} from '../types'

function createPlayerOrder(): Map<string, number> {
  return new Map([
    ['player1', 0],
    ['player2', 1],
    ['player3', 2],
    ['player4', 3],
  ])
}

const playerIdByIndex = ['player1', 'player2', 'player3', 'player4']

describe('ElectionEncoder', () => {
  describe('Size constants', () => {
    it('should have correct base sizes', () => {
      expect(REQUEST_VOTE_SIZE).toBe(8)
      expect(VOTE_RESPONSE_SIZE).toBe(5)
      expect(HEARTBEAT_SIZE).toBe(8)
      expect(HEARTBEAT_ACK_SIZE).toBe(8)
    })

    it('should have correct sizes with timestamp', () => {
      expect(HEARTBEAT_SIZE_WITH_TIMESTAMP).toBe(14)
      expect(HEARTBEAT_ACK_SIZE_WITH_TIMESTAMP).toBe(14)
    })
  })

  describe('RequestVote encoding', () => {
    const playerOrder = createPlayerOrder()

    it('should encode and decode basic RequestVote', () => {
      const message: RequestVoteMessage = {
        type: 'request_vote',
        term: 5,
        candidateId: 'player2',
        lastFrame: 1000,
      }

      const buffer = encodeRequestVote(message, playerOrder)
      expect(buffer.byteLength).toBe(REQUEST_VOTE_SIZE)

      const decoded = decodeRequestVote(buffer, playerIdByIndex)
      expect(decoded.type).toBe('request_vote')
      expect(decoded.term).toBe(5)
      expect(decoded.candidateId).toBe('player2')
      expect(decoded.lastFrame).toBe(1000)
    })

    it('should handle term 0', () => {
      const message: RequestVoteMessage = {
        type: 'request_vote',
        term: 0,
        candidateId: 'player1',
        lastFrame: 0,
      }

      const buffer = encodeRequestVote(message, playerOrder)
      const decoded = decodeRequestVote(buffer, playerIdByIndex)

      expect(decoded.term).toBe(0)
      expect(decoded.lastFrame).toBe(0)
    })

    it('should handle large term values', () => {
      const message: RequestVoteMessage = {
        type: 'request_vote',
        term: 0xFFFFFFFF, // Max 32-bit
        candidateId: 'player1',
        lastFrame: 100,
      }

      const buffer = encodeRequestVote(message, playerOrder)
      const decoded = decodeRequestVote(buffer, playerIdByIndex)

      expect(decoded.term).toBe(0xFFFFFFFF)
    })

    it('should handle max frame value (16-bit)', () => {
      const message: RequestVoteMessage = {
        type: 'request_vote',
        term: 1,
        candidateId: 'player1',
        lastFrame: 65535,
      }

      const buffer = encodeRequestVote(message, playerOrder)
      const decoded = decodeRequestVote(buffer, playerIdByIndex)

      expect(decoded.lastFrame).toBe(65535)
    })

    it('should handle unknown candidate gracefully', () => {
      const message: RequestVoteMessage = {
        type: 'request_vote',
        term: 1,
        candidateId: 'unknown',
        lastFrame: 100,
      }

      const buffer = encodeRequestVote(message, playerOrder)
      const decoded = decodeRequestVote(buffer, playerIdByIndex)

      // Unknown defaults to index 0
      expect(decoded.candidateId).toBe('player1')
    })

    it('should handle undefined lastFrame', () => {
      const message: RequestVoteMessage = {
        type: 'request_vote',
        term: 1,
        candidateId: 'player1',
        lastFrame: undefined as unknown as number,
      }

      const buffer = encodeRequestVote(message, playerOrder)
      const decoded = decodeRequestVote(buffer, playerIdByIndex)

      expect(decoded.lastFrame).toBe(0)
    })
  })

  describe('VoteResponse encoding', () => {
    const playerOrder = createPlayerOrder()

    it('should encode and decode vote granted', () => {
      const message: VoteResponseMessage = {
        type: 'vote_response',
        term: 3,
        voteGranted: true,
        voterId: 'player3',
      }

      const buffer = encodeVoteResponse(message, playerOrder)
      expect(buffer.byteLength).toBe(VOTE_RESPONSE_SIZE)

      const decoded = decodeVoteResponse(buffer, playerIdByIndex)
      expect(decoded.type).toBe('vote_response')
      expect(decoded.term).toBe(3)
      expect(decoded.voteGranted).toBe(true)
      expect(decoded.voterId).toBe('player3')
    })

    it('should encode and decode vote denied', () => {
      const message: VoteResponseMessage = {
        type: 'vote_response',
        term: 7,
        voteGranted: false,
        voterId: 'player1',
      }

      const buffer = encodeVoteResponse(message, playerOrder)
      const decoded = decodeVoteResponse(buffer, playerIdByIndex)

      expect(decoded.voteGranted).toBe(false)
    })

    it('should handle 24-bit term', () => {
      const message: VoteResponseMessage = {
        type: 'vote_response',
        term: 0xFFFFFF, // Max 24-bit
        voteGranted: true,
        voterId: 'player1',
      }

      const buffer = encodeVoteResponse(message, playerOrder)
      const decoded = decodeVoteResponse(buffer, playerIdByIndex)

      expect(decoded.term).toBe(0xFFFFFF)
    })

    it('should truncate term to 24 bits', () => {
      const message: VoteResponseMessage = {
        type: 'vote_response',
        term: 0x1FFFFFF, // More than 24 bits
        voteGranted: true,
        voterId: 'player1',
      }

      const buffer = encodeVoteResponse(message, playerOrder)
      const decoded = decodeVoteResponse(buffer, playerIdByIndex)

      expect(decoded.term).toBe(0xFFFFFF) // Truncated
    })

    it('should encode voter index in high bits of flags', () => {
      // Test different voter indices
      for (let i = 0; i < 4; i++) {
        const message: VoteResponseMessage = {
          type: 'vote_response',
          term: 1,
          voteGranted: false,
          voterId: playerIdByIndex[i]!,
        }

        const buffer = encodeVoteResponse(message, playerOrder)
        const decoded = decodeVoteResponse(buffer, playerIdByIndex)

        expect(decoded.voterId).toBe(playerIdByIndex[i])
      }
    })
  })

  describe('Heartbeat encoding', () => {
    const playerOrder = createPlayerOrder()

    it('should encode and decode basic Heartbeat without timestamp', () => {
      const message: HeartbeatMessage = {
        type: 'heartbeat',
        term: 10,
        leaderId: 'player1',
        frame: 5000,
      }

      const buffer = encodeHeartbeat(message, playerOrder)
      expect(buffer.byteLength).toBe(HEARTBEAT_SIZE)

      const decoded = decodeHeartbeat(buffer, playerIdByIndex)
      expect(decoded.type).toBe('heartbeat')
      expect(decoded.term).toBe(10)
      expect(decoded.leaderId).toBe('player1')
      expect(decoded.frame).toBe(5000)
      expect(decoded.timestamp).toBeUndefined()
    })

    it('should encode and decode Heartbeat with timestamp', () => {
      const now = Date.now()
      const message: HeartbeatMessage = {
        type: 'heartbeat',
        term: 15,
        leaderId: 'player2',
        frame: 3000,
        timestamp: now,
      }

      const buffer = encodeHeartbeat(message, playerOrder)
      expect(buffer.byteLength).toBe(HEARTBEAT_SIZE_WITH_TIMESTAMP)

      const decoded = decodeHeartbeat(buffer, playerIdByIndex)
      expect(decoded.term).toBe(15)
      expect(decoded.leaderId).toBe('player2')
      expect(decoded.frame).toBe(3000)
      expect(decoded.timestamp).toBe(now)
    })

    it('should handle large timestamps', () => {
      // Test with a timestamp in the year 3000
      const futureTimestamp = 32503680000000 // ~year 3000
      const message: HeartbeatMessage = {
        type: 'heartbeat',
        term: 1,
        leaderId: 'player1',
        frame: 100,
        timestamp: futureTimestamp,
      }

      const buffer = encodeHeartbeat(message, playerOrder)
      const decoded = decodeHeartbeat(buffer, playerIdByIndex)

      expect(decoded.timestamp).toBe(futureTimestamp)
    })

    it('should handle frame wrapping (16-bit)', () => {
      const message: HeartbeatMessage = {
        type: 'heartbeat',
        term: 1,
        leaderId: 'player1',
        frame: 70000, // > 65535
      }

      const buffer = encodeHeartbeat(message, playerOrder)
      const decoded = decodeHeartbeat(buffer, playerIdByIndex)

      expect(decoded.frame).toBe(70000 & 0xFFFF) // Wrapped
    })

    it('should round-trip all leader indices', () => {
      for (let i = 0; i < playerIdByIndex.length; i++) {
        const message: HeartbeatMessage = {
          type: 'heartbeat',
          term: i,
          leaderId: playerIdByIndex[i]!,
          frame: i * 100,
        }

        const buffer = encodeHeartbeat(message, playerOrder)
        const decoded = decodeHeartbeat(buffer, playerIdByIndex)

        expect(decoded.leaderId).toBe(playerIdByIndex[i])
      }
    })
  })

  describe('HeartbeatAck encoding', () => {
    const playerOrder = createPlayerOrder()

    it('should encode and decode basic HeartbeatAck without timestamp', () => {
      const message: HeartbeatAckMessage = {
        type: 'heartbeat_ack',
        term: 20,
        peerId: 'player3',
        frame: 4500,
      }

      const buffer = encodeHeartbeatAck(message, playerOrder)
      expect(buffer.byteLength).toBe(HEARTBEAT_ACK_SIZE)

      const decoded = decodeHeartbeatAck(buffer, playerIdByIndex)
      expect(decoded.type).toBe('heartbeat_ack')
      expect(decoded.term).toBe(20)
      expect(decoded.peerId).toBe('player3')
      expect(decoded.frame).toBe(4500)
      expect(decoded.timestamp).toBeUndefined()
    })

    it('should encode and decode HeartbeatAck with timestamp', () => {
      const timestamp = 1700000000000
      const message: HeartbeatAckMessage = {
        type: 'heartbeat_ack',
        term: 25,
        peerId: 'player4',
        frame: 6000,
        timestamp,
      }

      const buffer = encodeHeartbeatAck(message, playerOrder)
      expect(buffer.byteLength).toBe(HEARTBEAT_ACK_SIZE_WITH_TIMESTAMP)

      const decoded = decodeHeartbeatAck(buffer, playerIdByIndex)
      expect(decoded.term).toBe(25)
      expect(decoded.peerId).toBe('player4')
      expect(decoded.frame).toBe(6000)
      expect(decoded.timestamp).toBe(timestamp)
    })

    it('should echo back timestamp for RTT calculation', () => {
      // Simulate leader sending heartbeat with timestamp
      const sentTimestamp = Date.now()
      const heartbeat: HeartbeatMessage = {
        type: 'heartbeat',
        term: 1,
        leaderId: 'player1',
        frame: 100,
        timestamp: sentTimestamp,
      }

      // Follower echoes back the timestamp in ack
      const ack: HeartbeatAckMessage = {
        type: 'heartbeat_ack',
        term: 1,
        peerId: 'player2',
        frame: 100,
        timestamp: heartbeat.timestamp,
      }

      const buffer = encodeHeartbeatAck(ack, playerOrder)
      const decoded = decodeHeartbeatAck(buffer, playerIdByIndex)

      expect(decoded.timestamp).toBe(sentTimestamp)
    })

    it('should round-trip all peer indices', () => {
      for (let i = 0; i < playerIdByIndex.length; i++) {
        const message: HeartbeatAckMessage = {
          type: 'heartbeat_ack',
          term: i,
          peerId: playerIdByIndex[i]!,
          frame: i * 100,
        }

        const buffer = encodeHeartbeatAck(message, playerOrder)
        const decoded = decodeHeartbeatAck(buffer, playerIdByIndex)

        expect(decoded.peerId).toBe(playerIdByIndex[i])
      }
    })
  })

  describe('Edge cases', () => {
    const playerOrder = createPlayerOrder()

    it('should handle missing player in decode by creating fallback ID', () => {
      const message: HeartbeatMessage = {
        type: 'heartbeat',
        term: 1,
        leaderId: 'player4', // Index 3
        frame: 100,
      }

      const buffer = encodeHeartbeat(message, playerOrder)
      // Decode with shorter player list
      const decoded = decodeHeartbeat(buffer, ['player1', 'player2'])

      expect(decoded.leaderId).toBe('player_3') // Fallback format
    })

    it('should handle timestamp of 0', () => {
      const message: HeartbeatMessage = {
        type: 'heartbeat',
        term: 1,
        leaderId: 'player1',
        frame: 100,
        timestamp: 0,
      }

      const buffer = encodeHeartbeat(message, playerOrder)
      // Timestamp 0 is falsy but should still be encoded
      expect(buffer.byteLength).toBe(HEARTBEAT_SIZE_WITH_TIMESTAMP)

      const decoded = decodeHeartbeat(buffer, playerIdByIndex)
      expect(decoded.timestamp).toBe(0)
    })
  })
})
