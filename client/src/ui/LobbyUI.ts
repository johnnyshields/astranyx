/**
 * Lobby UI Manager
 *
 * Manages DOM interactions for the multiplayer lobby screen.
 */

import type { RoomInfo } from '../network/PhoenixClient.ts'

export interface LobbyUICallbacks {
  onQuickmatch: () => void
  onCreateRoom: (roomId: string) => void
  onJoinRoom: (roomId: string) => void
  onLeaveRoom: () => void
  onStartGame: () => void
  onRefreshRooms: () => void
  onBackToTitle: () => void
}

/** Truncate long player IDs for display */
function truncatePlayerId(playerId: string): string {
  return playerId.length > 20
    ? playerId.slice(0, 8) + '...' + playerId.slice(-8)
    : playerId
}

export class LobbyUI {
  private callbacks: LobbyUICallbacks

  // Screens
  private lobbyScreen: HTMLElement | null = null
  private roomListView: HTMLElement | null = null
  private roomWaitingView: HTMLElement | null = null
  private connectingView: HTMLElement | null = null

  // Room List elements
  private roomList: HTMLElement | null = null
  private roomNameInput: HTMLInputElement | null = null
  private lobbyError: HTMLElement | null = null

  // Room Waiting elements
  private currentRoomName: HTMLElement | null = null
  private playerList: HTMLElement | null = null
  private btnStartGame: HTMLButtonElement | null = null
  private connectionStatus: HTMLElement | null = null

  // Connecting elements
  private peerStatus: HTMLElement | null = null

  // State
  private localPlayerId = ''

  constructor(callbacks: LobbyUICallbacks) {
    this.callbacks = callbacks
    this.bindElements()
    this.setupEventListeners()
  }

  private bindElements(): void {
    // Screens
    this.lobbyScreen = document.getElementById('lobbyScreen')
    this.roomListView = document.getElementById('roomListView')
    this.roomWaitingView = document.getElementById('roomWaitingView')
    this.connectingView = document.getElementById('connectingView')

    // Room List
    this.roomList = document.getElementById('roomList')
    this.roomNameInput = document.getElementById('roomNameInput') as HTMLInputElement
    this.lobbyError = document.getElementById('lobbyError')

    // Room Waiting
    this.currentRoomName = document.getElementById('currentRoomName')
    this.playerList = document.getElementById('playerList')
    this.btnStartGame = document.getElementById('btnStartGame') as HTMLButtonElement
    this.connectionStatus = document.getElementById('connectionStatus')

    // Connecting
    this.peerStatus = document.getElementById('peerStatus')
  }

  private setupEventListeners(): void {
    // Quickmatch button
    document.getElementById('btnQuickmatch')?.addEventListener('click', () => {
      this.callbacks.onQuickmatch()
    })

    // Create room button
    document.getElementById('btnCreateRoom')?.addEventListener('click', () => {
      const roomName = this.roomNameInput?.value.trim()
      if (roomName) {
        this.callbacks.onCreateRoom(roomName)
      } else {
        this.showError('Please enter a room name')
      }
    })

    // Enter key in room name input
    this.roomNameInput?.addEventListener('keydown', (e) => {
      if (e.key === 'Enter') {
        const roomName = this.roomNameInput?.value.trim()
        if (roomName) {
          this.callbacks.onCreateRoom(roomName)
        }
      }
    })

    // Refresh rooms button
    document.getElementById('btnRefreshRooms')?.addEventListener('click', () => {
      this.callbacks.onRefreshRooms()
    })

    // Back to title button
    document.getElementById('btnBackToTitle')?.addEventListener('click', () => {
      this.callbacks.onBackToTitle()
    })

    // Start game button
    this.btnStartGame?.addEventListener('click', () => {
      this.callbacks.onStartGame()
    })

    // Leave room button
    document.getElementById('btnLeaveRoom')?.addEventListener('click', () => {
      this.callbacks.onLeaveRoom()
    })
  }

  // ==========================================================================
  // View Management
  // ==========================================================================

  show(): void {
    this.lobbyScreen?.classList.remove('hidden')
  }

  hide(): void {
    this.lobbyScreen?.classList.add('hidden')
    // Reset to room list view
    this.showRoomList()
  }

  showRoomList(): void {
    this.roomListView?.classList.remove('hidden')
    this.roomWaitingView?.classList.add('hidden')
    this.connectingView?.classList.add('hidden')
    this.hideError()
  }

  showRoomWaiting(roomId: string, isHost: boolean): void {
    this.roomListView?.classList.add('hidden')
    this.roomWaitingView?.classList.remove('hidden')
    this.connectingView?.classList.add('hidden')

    if (this.currentRoomName) {
      this.currentRoomName.textContent = roomId.toUpperCase()
    }

    // Enable start button only for host
    this.setStartGameEnabled(isHost)

    // Clear input
    if (this.roomNameInput) {
      this.roomNameInput.value = ''
    }
  }

  showConnecting(): void {
    this.roomListView?.classList.add('hidden')
    this.roomWaitingView?.classList.add('hidden')
    this.connectingView?.classList.remove('hidden')
  }

  // ==========================================================================
  // Room List
  // ==========================================================================

  updateRoomList(rooms: RoomInfo[]): void {
    if (!this.roomList) return

    if (rooms.length === 0) {
      this.roomList.innerHTML = '<div class="room-list-empty">NO ROOMS AVAILABLE</div>'
      return
    }

    this.roomList.innerHTML = rooms
      .filter(room => room.status === 'waiting')
      .map(room => `
        <div class="room-item" data-room-id="${room.id}">
          <span class="room-name">${room.id.toUpperCase()}</span>
          <span class="room-players">${room.player_count}/${room.max_players}</span>
        </div>
      `)
      .join('')

    // Add click handlers
    this.roomList.querySelectorAll('.room-item').forEach(el => {
      el.addEventListener('click', () => {
        const roomId = el.getAttribute('data-room-id')
        if (roomId) {
          this.callbacks.onJoinRoom(roomId)
        }
      })
    })

    if (this.roomList.innerHTML === '') {
      this.roomList.innerHTML = '<div class="room-list-empty">NO ROOMS AVAILABLE</div>'
    }
  }

  // ==========================================================================
  // Player List
  // ==========================================================================

  setLocalPlayerId(playerId: string): void {
    this.localPlayerId = playerId
  }

  updatePlayerList(players: string[], hostId: string): void {
    if (!this.playerList) return

    this.playerList.innerHTML = players
      .map(playerId => {
        const isHost = playerId === hostId
        const isLocal = playerId === this.localPlayerId
        const classes = ['player-item']
        if (isHost) classes.push('host')
        if (isLocal) classes.push('local')

        const displayName = truncatePlayerId(playerId)

        return `
          <div class="${classes.join(' ')}">
            <span class="player-name">${displayName}</span>
            ${isLocal ? '<span class="player-tag">YOU</span>' : ''}
          </div>
        `
      })
      .join('')
  }

  // ==========================================================================
  // Connection Status
  // ==========================================================================

  updateConnectionStatus(status: string): void {
    if (this.connectionStatus) {
      this.connectionStatus.textContent = status.toUpperCase()
    }
  }

  updatePeerStatus(peers: Map<string, 'connecting' | 'connected'>): void {
    if (!this.peerStatus) return

    const items: string[] = []
    for (const [playerId, state] of peers) {
      const displayName = truncatePlayerId(playerId)

      items.push(`
        <div class="peer-status-item">
          <span class="peer-name">${displayName}</span>
          <span class="peer-state ${state}">${state.toUpperCase()}</span>
        </div>
      `)
    }

    this.peerStatus.innerHTML = items.join('')
  }

  // ==========================================================================
  // Controls
  // ==========================================================================

  setStartGameEnabled(enabled: boolean): void {
    if (this.btnStartGame) {
      this.btnStartGame.disabled = !enabled
    }
  }

  // ==========================================================================
  // Error Handling
  // ==========================================================================

  showError(message: string): void {
    if (this.lobbyError) {
      this.lobbyError.textContent = message
      this.lobbyError.style.display = 'block'
    }
  }

  hideError(): void {
    if (this.lobbyError) {
      this.lobbyError.style.display = 'none'
    }
  }

  // ==========================================================================
  // Cleanup
  // ==========================================================================

  destroy(): void {
    // Nothing to clean up for now
    // Event listeners are attached to static DOM elements
  }
}
