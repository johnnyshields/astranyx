import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest'
import { P2PManager, type PeerConnection } from './P2PManager'
import type { Channel } from 'phoenix'

// Mock RTCPeerConnection
class MockRTCPeerConnection {
  connectionState: RTCPeerConnectionState = 'new'
  onicecandidate: ((event: RTCPeerConnectionIceEvent) => void) | null = null
  onconnectionstatechange: (() => void) | null = null
  ondatachannel: ((event: RTCDataChannelEvent) => void) | null = null

  private remoteDescription: RTCSessionDescription | null = null
  private localDescription: RTCSessionDescription | null = null

  createDataChannel(label: string, options?: RTCDataChannelInit): RTCDataChannel {
    return new MockRTCDataChannel(label) as unknown as RTCDataChannel
  }

  async createOffer(): Promise<RTCSessionDescriptionInit> {
    return { type: 'offer', sdp: 'mock-offer-sdp' }
  }

  async createAnswer(): Promise<RTCSessionDescriptionInit> {
    return { type: 'answer', sdp: 'mock-answer-sdp' }
  }

  async setLocalDescription(desc: RTCSessionDescriptionInit): Promise<void> {
    this.localDescription = new RTCSessionDescription(desc)
  }

  async setRemoteDescription(desc: RTCSessionDescription): Promise<void> {
    this.remoteDescription = desc
  }

  async addIceCandidate(candidate: RTCIceCandidate): Promise<void> {
    // Mock implementation
  }

  close(): void {
    this.connectionState = 'closed'
  }
}

class MockRTCDataChannel {
  label: string
  binaryType: BinaryType = 'arraybuffer'
  readyState: RTCDataChannelState = 'connecting'
  onopen: (() => void) | null = null
  onclose: (() => void) | null = null
  onerror: ((error: Event) => void) | null = null
  onmessage: ((event: MessageEvent) => void) | null = null

  constructor(label: string) {
    this.label = label
  }

  close(): void {
    this.readyState = 'closed'
  }

  send(data: string | ArrayBuffer | Blob | ArrayBufferView): void {
    // Mock implementation
  }
}

// Mock global RTCPeerConnection
vi.stubGlobal('RTCPeerConnection', MockRTCPeerConnection)
vi.stubGlobal('RTCSessionDescription', class {
  type: RTCSdpType
  sdp: string
  constructor(init: RTCSessionDescriptionInit) {
    this.type = init.type!
    this.sdp = init.sdp || ''
  }
})
vi.stubGlobal('RTCIceCandidate', class {
  candidate: string
  sdpMid: string | null
  sdpMLineIndex: number | null
  constructor(init: RTCIceCandidateInit) {
    this.candidate = init.candidate || ''
    this.sdpMid = init.sdpMid || null
    this.sdpMLineIndex = init.sdpMLineIndex || null
  }
})

describe('P2PManager', () => {
  let manager: P2PManager
  let mockChannel: Channel

  beforeEach(() => {
    manager = new P2PManager('local-player-id')

    // Create mock Phoenix channel
    const eventHandlers: Map<string, (payload: unknown) => void> = new Map()
    mockChannel = {
      on: vi.fn((event: string, callback: (payload: unknown) => void) => {
        eventHandlers.set(event, callback)
      }),
      push: vi.fn().mockReturnValue({
        receive: vi.fn().mockReturnThis(),
      }),
      // Helper to trigger events
      _trigger: (event: string, payload: unknown) => {
        const handler = eventHandlers.get(event)
        if (handler) handler(payload)
      },
    } as unknown as Channel & { _trigger: (event: string, payload: unknown) => void }
  })

  afterEach(() => {
    vi.restoreAllMocks()
  })

  describe('constructor', () => {
    it('should create manager with local player ID', () => {
      const mgr = new P2PManager('test-player')
      expect(mgr).toBeInstanceOf(P2PManager)
    })
  })

  describe('setSignalingChannel', () => {
    it('should register event handlers on channel', () => {
      manager.setSignalingChannel(mockChannel)

      expect(mockChannel.on).toHaveBeenCalledWith('offer', expect.any(Function))
      expect(mockChannel.on).toHaveBeenCalledWith('answer', expect.any(Function))
      expect(mockChannel.on).toHaveBeenCalledWith('ice_candidate', expect.any(Function))
      expect(mockChannel.on).toHaveBeenCalledWith('peer_joined', expect.any(Function))
      expect(mockChannel.on).toHaveBeenCalledWith('peer_left', expect.any(Function))
    })

    it('should handle peer_joined event and initiate connection if we have higher ID', async () => {
      manager.setSignalingChannel(mockChannel)

      // 'local-player-id' > 'aaa-player' lexicographically
      ;(mockChannel as unknown as { _trigger: Function })._trigger('peer_joined', {
        player_id: 'aaa-player',
      })

      // Wait for async operations
      await new Promise((r) => setTimeout(r, 10))

      // Should have created a peer connection and pushed an offer
      expect(mockChannel.push).toHaveBeenCalledWith('offer', expect.objectContaining({
        to: 'aaa-player',
      }))
    })

    it('should not initiate connection if we have lower ID', () => {
      manager.setSignalingChannel(mockChannel)

      // 'local-player-id' < 'zzz-player' lexicographically
      ;(mockChannel as unknown as { _trigger: Function })._trigger('peer_joined', {
        player_id: 'zzz-player',
      })

      // Should not push offer (waiting for other peer to initiate)
      expect(mockChannel.push).not.toHaveBeenCalledWith('offer', expect.anything())
    })

    it('should handle peer_left event', () => {
      const disconnectHandler = vi.fn()
      manager.onDisconnected(disconnectHandler)
      manager.setSignalingChannel(mockChannel)

      // First connect to a peer
      ;(mockChannel as unknown as { _trigger: Function })._trigger('peer_joined', {
        player_id: 'aaa-player',
      })

      // Then they leave
      ;(mockChannel as unknown as { _trigger: Function })._trigger('peer_left', {
        player_id: 'aaa-player',
      })

      expect(disconnectHandler).toHaveBeenCalledWith('aaa-player')
    })
  })

  describe('connectToPlayers', () => {
    it('should not connect to self', async () => {
      manager.setSignalingChannel(mockChannel)
      await manager.connectToPlayers(['local-player-id'])

      expect(mockChannel.push).not.toHaveBeenCalled()
    })

    it('should only connect to players with lower IDs', async () => {
      manager.setSignalingChannel(mockChannel)
      await manager.connectToPlayers(['aaa-player', 'zzz-player'])

      // Should only initiate to 'aaa-player' since 'local-player-id' > 'aaa-player'
      expect(mockChannel.push).toHaveBeenCalledWith('offer', expect.objectContaining({
        to: 'aaa-player',
      }))

      // Should not initiate to 'zzz-player' since 'local-player-id' < 'zzz-player'
      const offerCalls = (mockChannel.push as ReturnType<typeof vi.fn>).mock.calls.filter(
        (call) => call[0] === 'offer'
      )
      expect(offerCalls.every((call) => call[1].to !== 'zzz-player')).toBe(true)
    })
  })

  describe('event handlers', () => {
    it('should set connected handler', () => {
      const handler = vi.fn()
      manager.onConnected(handler)

      // Handler is stored internally
      expect(manager).toBeInstanceOf(P2PManager)
    })

    it('should set disconnected handler', () => {
      const handler = vi.fn()
      manager.onDisconnected(handler)

      expect(manager).toBeInstanceOf(P2PManager)
    })
  })

  describe('getPeers', () => {
    it('should return peers map', () => {
      const peers = manager.getPeers()
      expect(peers).toBeInstanceOf(Map)
      expect(peers.size).toBe(0)
    })
  })

  describe('getConnectedPeers', () => {
    it('should return empty array when no peers', () => {
      const connected = manager.getConnectedPeers()
      expect(connected).toEqual([])
    })
  })

  describe('isFullyConnected', () => {
    it('should return true for single player (no peers needed)', () => {
      expect(manager.isFullyConnected(1)).toBe(true)
    })

    it('should return false when expecting peers but none connected', () => {
      expect(manager.isFullyConnected(2)).toBe(false)
    })
  })

  describe('disconnect', () => {
    it('should clear signaling channel', () => {
      manager.setSignalingChannel(mockChannel)
      manager.disconnect()

      // Manager should be disconnected
      expect(manager.getConnectedPeers()).toEqual([])
    })

    it('should disconnect all peers', () => {
      const disconnectHandler = vi.fn()
      manager.onDisconnected(disconnectHandler)
      manager.setSignalingChannel(mockChannel)

      // Create a peer
      ;(mockChannel as unknown as { _trigger: Function })._trigger('peer_joined', {
        player_id: 'aaa-player',
      })

      manager.disconnect()

      expect(disconnectHandler).toHaveBeenCalledWith('aaa-player')
    })
  })

  describe('offer handling', () => {
    it('should ignore offers not addressed to us', () => {
      manager.setSignalingChannel(mockChannel)

      ;(mockChannel as unknown as { _trigger: Function })._trigger('offer', {
        type: 'offer',
        from: 'other-player',
        to: 'different-player', // Not us
        sdp: { type: 'offer', sdp: 'test' },
      })

      // Should not send answer since offer wasn't for us
      expect(mockChannel.push).not.toHaveBeenCalledWith('answer', expect.anything())
    })

    it('should handle offers addressed to us', async () => {
      manager.setSignalingChannel(mockChannel)

      ;(mockChannel as unknown as { _trigger: Function })._trigger('offer', {
        type: 'offer',
        from: 'other-player',
        to: 'local-player-id', // Us
        sdp: { type: 'offer', sdp: 'test' },
      })

      // Wait for async handling
      await new Promise((r) => setTimeout(r, 10))

      expect(mockChannel.push).toHaveBeenCalledWith('answer', expect.objectContaining({
        to: 'other-player',
      }))
    })
  })

  describe('answer handling', () => {
    it('should ignore answers not addressed to us', () => {
      manager.setSignalingChannel(mockChannel)

      ;(mockChannel as unknown as { _trigger: Function })._trigger('answer', {
        type: 'answer',
        from: 'other-player',
        to: 'different-player',
        sdp: { type: 'answer', sdp: 'test' },
      })

      // No error thrown - answer silently ignored
    })
  })

  describe('ICE candidate handling', () => {
    it('should ignore ICE candidates not addressed to us', () => {
      manager.setSignalingChannel(mockChannel)

      ;(mockChannel as unknown as { _trigger: Function })._trigger('ice_candidate', {
        type: 'ice_candidate',
        from: 'other-player',
        to: 'different-player',
        candidate: { candidate: 'test', sdpMid: '0', sdpMLineIndex: 0 },
      })

      // No error thrown - candidate silently ignored
    })
  })
})
