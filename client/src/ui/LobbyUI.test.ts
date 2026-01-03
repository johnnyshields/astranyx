import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest'
import { LobbyUI, type LobbyUICallbacks } from './LobbyUI'

describe('LobbyUI', () => {
  let callbacks: LobbyUICallbacks
  let lobbyUI: LobbyUI

  // Create mock DOM elements
  const createMockElements = () => {
    // Screens
    const lobbyScreen = document.createElement('div')
    lobbyScreen.id = 'lobbyScreen'
    lobbyScreen.classList.add('hidden')

    const roomListView = document.createElement('div')
    roomListView.id = 'roomListView'

    const roomWaitingView = document.createElement('div')
    roomWaitingView.id = 'roomWaitingView'
    roomWaitingView.classList.add('hidden')

    const connectingView = document.createElement('div')
    connectingView.id = 'connectingView'
    connectingView.classList.add('hidden')

    // Room List elements
    const roomList = document.createElement('div')
    roomList.id = 'roomList'

    const roomNameInput = document.createElement('input')
    roomNameInput.id = 'roomNameInput'

    const playerNameInput = document.createElement('input')
    playerNameInput.id = 'playerNameInput'

    const lobbyError = document.createElement('div')
    lobbyError.id = 'lobbyError'

    // Room Waiting elements
    const currentRoomName = document.createElement('div')
    currentRoomName.id = 'currentRoomName'

    const playerList = document.createElement('div')
    playerList.id = 'playerList'

    const btnStartGame = document.createElement('button')
    btnStartGame.id = 'btnStartGame'

    const connectionStatus = document.createElement('div')
    connectionStatus.id = 'connectionStatus'

    // Connecting elements
    const peerStatus = document.createElement('div')
    peerStatus.id = 'peerStatus'

    // Buttons
    const btnQuickmatch = document.createElement('button')
    btnQuickmatch.id = 'btnQuickmatch'

    const btnCreateRoom = document.createElement('button')
    btnCreateRoom.id = 'btnCreateRoom'

    const btnRefreshRooms = document.createElement('button')
    btnRefreshRooms.id = 'btnRefreshRooms'

    const btnBackToTitle = document.createElement('button')
    btnBackToTitle.id = 'btnBackToTitle'

    const btnLeaveRoom = document.createElement('button')
    btnLeaveRoom.id = 'btnLeaveRoom'

    // Add all elements to document
    document.body.appendChild(lobbyScreen)
    document.body.appendChild(roomListView)
    document.body.appendChild(roomWaitingView)
    document.body.appendChild(connectingView)
    document.body.appendChild(roomList)
    document.body.appendChild(roomNameInput)
    document.body.appendChild(playerNameInput)
    document.body.appendChild(lobbyError)
    document.body.appendChild(currentRoomName)
    document.body.appendChild(playerList)
    document.body.appendChild(btnStartGame)
    document.body.appendChild(connectionStatus)
    document.body.appendChild(peerStatus)
    document.body.appendChild(btnQuickmatch)
    document.body.appendChild(btnCreateRoom)
    document.body.appendChild(btnRefreshRooms)
    document.body.appendChild(btnBackToTitle)
    document.body.appendChild(btnLeaveRoom)
  }

  beforeEach(() => {
    // Clear DOM
    document.body.innerHTML = ''
    localStorage.clear()

    // Create mock elements
    createMockElements()

    // Create mock callbacks
    callbacks = {
      onQuickmatch: vi.fn(),
      onCreateRoom: vi.fn(),
      onJoinRoom: vi.fn(),
      onLeaveRoom: vi.fn(),
      onStartGame: vi.fn(),
      onRefreshRooms: vi.fn(),
      onBackToTitle: vi.fn(),
    }

    lobbyUI = new LobbyUI(callbacks)
  })

  afterEach(() => {
    document.body.innerHTML = ''
    localStorage.clear()
  })

  describe('constructor', () => {
    it('creates LobbyUI instance', () => {
      expect(lobbyUI).toBeDefined()
    })

    it('generates default player name', () => {
      const name = lobbyUI.getPlayerName()
      expect(name).toMatch(/^PILOT-\d{4}$/)
    })

    it('loads saved player name from localStorage', () => {
      localStorage.setItem('astranyx_player_name', 'CustomName')
      const newLobbyUI = new LobbyUI(callbacks)
      expect(newLobbyUI.getPlayerName()).toBe('CustomName')
    })
  })

  describe('show/hide', () => {
    it('shows lobby screen', () => {
      lobbyUI.show()
      const screen = document.getElementById('lobbyScreen')
      expect(screen?.classList.contains('hidden')).toBe(false)
    })

    it('hides lobby screen', () => {
      lobbyUI.show()
      lobbyUI.hide()
      const screen = document.getElementById('lobbyScreen')
      expect(screen?.classList.contains('hidden')).toBe(true)
    })
  })

  describe('view switching', () => {
    it('shows room list view', () => {
      lobbyUI.showRoomList()
      expect(document.getElementById('roomListView')?.classList.contains('hidden')).toBe(false)
      expect(document.getElementById('roomWaitingView')?.classList.contains('hidden')).toBe(true)
      expect(document.getElementById('connectingView')?.classList.contains('hidden')).toBe(true)
    })

    it('shows room waiting view for host', () => {
      lobbyUI.showRoomWaiting('test-room', true)
      expect(document.getElementById('roomListView')?.classList.contains('hidden')).toBe(true)
      expect(document.getElementById('roomWaitingView')?.classList.contains('hidden')).toBe(false)
      expect(document.getElementById('currentRoomName')?.textContent).toBe('TEST-ROOM')
      expect((document.getElementById('btnStartGame') as HTMLButtonElement).disabled).toBe(false)
    })

    it('shows room waiting view for guest (start disabled)', () => {
      lobbyUI.showRoomWaiting('test-room', false)
      expect((document.getElementById('btnStartGame') as HTMLButtonElement).disabled).toBe(true)
    })

    it('shows connecting view', () => {
      lobbyUI.showConnecting()
      expect(document.getElementById('connectingView')?.classList.contains('hidden')).toBe(false)
    })
  })

  describe('room list', () => {
    it('displays rooms', () => {
      lobbyUI.updateRoomList([
        { id: 'room1', host: 'player1', player_count: 2, max_players: 4, status: 'waiting' },
        { id: 'room2', host: 'player2', player_count: 1, max_players: 4, status: 'waiting' },
      ])

      const roomList = document.getElementById('roomList')
      expect(roomList?.querySelectorAll('.room-item').length).toBe(2)
    })

    it('shows empty message when no rooms', () => {
      lobbyUI.updateRoomList([])
      const roomList = document.getElementById('roomList')
      expect(roomList?.innerHTML).toContain('NO ROOMS AVAILABLE')
    })

    it('filters out non-waiting rooms', () => {
      lobbyUI.updateRoomList([
        { id: 'room1', host: 'player1', player_count: 2, max_players: 4, status: 'waiting' },
        { id: 'room2', host: 'player2', player_count: 4, max_players: 4, status: 'playing' },
      ])

      const roomList = document.getElementById('roomList')
      expect(roomList?.querySelectorAll('.room-item').length).toBe(1)
    })

    it('calls onJoinRoom when room clicked', () => {
      lobbyUI.updateRoomList([
        { id: 'room1', host: 'player1', player_count: 2, max_players: 4, status: 'waiting' },
      ])

      const roomItem = document.querySelector('.room-item')
      roomItem?.dispatchEvent(new MouseEvent('click', { bubbles: true }))

      expect(callbacks.onJoinRoom).toHaveBeenCalledWith('room1')
    })
  })

  describe('player list', () => {
    it('displays players', () => {
      lobbyUI.setLocalPlayerId('local-player')
      lobbyUI.updatePlayerList(['host-player', 'local-player'], 'host-player')

      const playerList = document.getElementById('playerList')
      expect(playerList?.querySelectorAll('.player-item').length).toBe(2)
    })

    it('marks host player', () => {
      lobbyUI.updatePlayerList(['host-player', 'other-player'], 'host-player')
      const playerList = document.getElementById('playerList')
      expect(playerList?.querySelector('.host')).toBeTruthy()
    })

    it('marks local player with YOU tag', () => {
      lobbyUI.setLocalPlayerId('local-player')
      lobbyUI.updatePlayerList(['host-player', 'local-player'], 'host-player')

      const playerList = document.getElementById('playerList')
      expect(playerList?.innerHTML).toContain('YOU')
    })

    it('uses custom player names', () => {
      lobbyUI.setPlayerName('player-123', 'CustomName')
      lobbyUI.updatePlayerList(['player-123'], 'player-123')

      const playerList = document.getElementById('playerList')
      expect(playerList?.innerHTML).toContain('CUSTOMNAME')
    })
  })

  describe('connection status', () => {
    it('updates connection status', () => {
      lobbyUI.updateConnectionStatus('connected')
      expect(document.getElementById('connectionStatus')?.textContent).toBe('CONNECTED')
    })

    it('updates peer status', () => {
      const peers = new Map<string, 'connecting' | 'connected'>()
      peers.set('peer1', 'connected')
      peers.set('peer2', 'connecting')

      lobbyUI.updatePeerStatus(peers)

      const peerStatus = document.getElementById('peerStatus')
      expect(peerStatus?.querySelectorAll('.peer-status-item').length).toBe(2)
    })
  })

  describe('controls', () => {
    it('enables start game button', () => {
      lobbyUI.setStartGameEnabled(true)
      expect((document.getElementById('btnStartGame') as HTMLButtonElement).disabled).toBe(false)
    })

    it('disables start game button', () => {
      lobbyUI.setStartGameEnabled(false)
      expect((document.getElementById('btnStartGame') as HTMLButtonElement).disabled).toBe(true)
    })
  })

  describe('error handling', () => {
    it('shows error message', () => {
      lobbyUI.showError('Test error')
      const error = document.getElementById('lobbyError')
      expect(error?.textContent).toBe('Test error')
      expect(error?.style.display).toBe('block')
    })

    it('hides error message', () => {
      lobbyUI.showError('Test error')
      lobbyUI.hideError()
      const error = document.getElementById('lobbyError')
      expect(error?.style.display).toBe('none')
    })
  })

  describe('button callbacks', () => {
    it('calls onQuickmatch', () => {
      document.getElementById('btnQuickmatch')?.click()
      expect(callbacks.onQuickmatch).toHaveBeenCalled()
    })

    it('calls onCreateRoom with room name', () => {
      const input = document.getElementById('roomNameInput') as HTMLInputElement
      input.value = 'test-room'
      document.getElementById('btnCreateRoom')?.click()
      expect(callbacks.onCreateRoom).toHaveBeenCalledWith('test-room')
    })

    it('shows error when creating room without name', () => {
      document.getElementById('btnCreateRoom')?.click()
      expect(document.getElementById('lobbyError')?.style.display).toBe('block')
    })

    it('calls onCreateRoom on Enter key', () => {
      const input = document.getElementById('roomNameInput') as HTMLInputElement
      input.value = 'enter-room'
      input.dispatchEvent(new KeyboardEvent('keydown', { key: 'Enter' }))
      expect(callbacks.onCreateRoom).toHaveBeenCalledWith('enter-room')
    })

    it('calls onRefreshRooms', () => {
      document.getElementById('btnRefreshRooms')?.click()
      expect(callbacks.onRefreshRooms).toHaveBeenCalled()
    })

    it('calls onBackToTitle', () => {
      document.getElementById('btnBackToTitle')?.click()
      expect(callbacks.onBackToTitle).toHaveBeenCalled()
    })

    it('calls onStartGame', () => {
      document.getElementById('btnStartGame')?.click()
      expect(callbacks.onStartGame).toHaveBeenCalled()
    })

    it('calls onLeaveRoom', () => {
      document.getElementById('btnLeaveRoom')?.click()
      expect(callbacks.onLeaveRoom).toHaveBeenCalled()
    })
  })

  describe('destroy', () => {
    it('destroys without error', () => {
      expect(() => lobbyUI.destroy()).not.toThrow()
    })
  })
})
