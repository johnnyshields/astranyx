/**
 * ASTRANYX - Main Entry Point
 *
 * This is the minimal boot loader that handles:
 * 1. Initial loading screen
 * 2. Progressive module loading
 * 3. Error handling
 *
 * Heavy modules (Game, Simulation, Renderer) are lazy-loaded
 * to minimize initial bundle size and improve load times.
 */

import { Boot } from './boot/Boot.ts'
import { MultiplayerManager, type MultiplayerState } from './network/MultiplayerManager.ts'
import { LobbyUI } from './ui/LobbyUI.ts'
import type { Engine } from './core/Engine.ts'
import type { Game } from './game/Game.ts'
import { SafeConsole } from './core/SafeConsole.ts'

// Server URL - configurable via environment or auto-detect
function getServerUrl(): string {
  // Check for explicit env variable (set via Vite's define)
  if (typeof import.meta.env?.VITE_SERVER_URL === 'string') {
    return import.meta.env.VITE_SERVER_URL
  }

  // Production: use same host as client
  if (window.location.hostname !== 'localhost' && window.location.hostname !== '127.0.0.1') {
    const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:'
    return `${protocol}//${window.location.host}/socket`
  }

  // Development: localhost server on port 4200
  return 'ws://localhost:4200/socket'
}

const SERVER_URL = getServerUrl()

async function main() {
  const boot = new Boot()

  // Optional: Add progress listener for custom UI
  boot.onProgress((state) => {
    SafeConsole.log(`[Boot] ${state.phase}: ${state.progress}% - ${state.message}`)
  })

  try {
    // Run boot sequence (loads Engine module)
    const { Engine } = await boot.run()

    // Get canvas element
    const canvas = document.getElementById('game') as HTMLCanvasElement
    if (!canvas) {
      throw new Error('Canvas element not found')
    }

    // Create engine instance
    const engine = new Engine(canvas)

    // Optional: Track engine init progress
    engine.onProgress((phase, _progress) => {
      const messages: Record<string, string> = {
        renderer: 'INITIALIZING RENDERER...',
        input: 'CONFIGURING INPUT...',
        game: 'LOADING GAME...',
        ready: 'READY',
      }
      const loading = document.getElementById('loading')
      if (loading) {
        loading.textContent = messages[phase] ?? 'LOADING...'
      }
    })

    // Initialize engine (lazy loads Game module)
    await engine.init()

    // Hide loading screen and start
    boot.hideLoading()
    engine.start()

    // Setup multiplayer after engine is ready
    setupMultiplayer(engine)

    SafeConsole.log('ASTRANYX initialized')

  } catch (error) {
    const message = error instanceof Error ? error.message : 'Unknown error'
    boot.showError(`INITIALIZATION FAILED: ${message}`)
    SafeConsole.error('Failed to initialize:', error)
  }
}

/**
 * Setup multiplayer components
 */
function setupMultiplayer(engine: Engine): void {
  const game = engine.getGame()
  let multiplayer: MultiplayerManager | null = null
  let lobbyUI: LobbyUI | null = null

  const titleScreen = document.getElementById('titleScreen')
  const lobbyScreen = document.getElementById('lobbyScreen')

  // Create lobby UI with callbacks
  lobbyUI = new LobbyUI({
    onQuickmatch: async () => {
      if (!multiplayer) return
      lobbyUI?.hideError()
      try {
        await multiplayer.quickmatch()
      } catch (error) {
        lobbyUI?.showError((error as Error).message)
      }
    },

    onCreateRoom: async (roomId: string) => {
      if (!multiplayer) return
      lobbyUI?.hideError()
      try {
        await multiplayer.createRoom(roomId)
      } catch (error) {
        lobbyUI?.showError((error as Error).message)
      }
    },

    onJoinRoom: async (roomId: string) => {
      if (!multiplayer) return
      lobbyUI?.hideError()
      try {
        await multiplayer.joinRoom(roomId)
      } catch (error) {
        lobbyUI?.showError((error as Error).message)
      }
    },

    onLeaveRoom: () => {
      multiplayer?.leaveRoom()
    },

    onStartGame: async () => {
      if (!multiplayer) return
      try {
        await multiplayer.startGame()
      } catch (error) {
        lobbyUI?.showError((error as Error).message)
      }
    },

    onRefreshRooms: async () => {
      if (!multiplayer) return
      try {
        const rooms = await multiplayer.listRooms()
        lobbyUI?.updateRoomList(rooms)
      } catch (error) {
        SafeConsole.error('Failed to refresh rooms:', error)
      }
    },

    onBackToTitle: () => {
      multiplayer?.disconnect()
      multiplayer = null
      lobbyScreen?.classList.add('hidden')
      titleScreen?.classList.remove('hidden')
    },
  })

  // Handle multiplayer button click
  document.getElementById('btnMultiplayer')?.addEventListener('click', async () => {
    titleScreen?.classList.add('hidden')
    lobbyScreen?.classList.remove('hidden')
    lobbyUI?.showRoomList()
    lobbyUI?.hideError()

    // Connect to server
    multiplayer = new MultiplayerManager({ serverUrl: SERVER_URL })

    // Wire up state changes
    multiplayer.onStateChange((state: MultiplayerState) => {
      handleMultiplayerStateChange(state, multiplayer!, lobbyUI!, game)
    })

    multiplayer.onLobbyUpdate((lobby) => {
      if (lobby.currentRoom) {
        lobbyUI?.updatePlayerList(
          lobby.currentRoom.players,
          lobby.currentRoom.host
        )
        lobbyUI?.setStartGameEnabled(lobby.currentRoom.isHost && lobby.currentRoom.players.length >= 1)
      }
      lobbyUI?.updateRoomList(lobby.rooms)
    })

    multiplayer.onError((error) => {
      SafeConsole.error('Multiplayer error:', error)
      lobbyUI?.showError(error.message)
    })

    multiplayer.onReady(() => {
      // Start the multiplayer game
      startMultiplayerGame(multiplayer!, game, lobbyUI!)
    })

    try {
      await multiplayer.connect()
      lobbyUI?.setLocalPlayerId(multiplayer.getLocalPlayerId())

      // Auto-refresh room list on connect
      const rooms = await multiplayer.listRooms()
      lobbyUI?.updateRoomList(rooms)
    } catch (error) {
      lobbyUI?.showError('Failed to connect to server. Local play still available.')
      SafeConsole.error('Failed to connect:', error)
    }
  })
}

/**
 * Handle multiplayer state changes
 */
function handleMultiplayerStateChange(
  state: MultiplayerState,
  multiplayer: MultiplayerManager,
  lobbyUI: LobbyUI,
  _game: Game
): void {
  SafeConsole.log('Multiplayer state:', state)

  switch (state) {
    case 'connecting':
      lobbyUI.updateConnectionStatus('Connecting to server...')
      break

    case 'connected':
      lobbyUI.updateConnectionStatus('Connected')
      lobbyUI.showRoomList()
      break

    case 'joining_room':
      lobbyUI.updateConnectionStatus('Joining room...')
      break

    case 'in_lobby': {
      const lobby = multiplayer.getLobbyState()
      if (lobby.currentRoom) {
        lobbyUI.showRoomWaiting(lobby.currentRoom.id, lobby.currentRoom.isHost)
        lobbyUI.updateConnectionStatus('Waiting for players...')
      }
      break
    }

    case 'starting':
      lobbyUI.updateConnectionStatus('Starting game...')
      break

    case 'connecting_peers':
      lobbyUI.showConnecting()
      // TODO: Show peer connection status
      break

    case 'ready':
      // Game will be started via onReady callback
      break

    case 'playing':
      // Game is now running
      break

    case 'error':
      lobbyUI.showRoomList()
      break

    case 'disconnected':
      lobbyUI.showRoomList()
      lobbyUI.updateConnectionStatus('Disconnected')
      break
  }
}

/**
 * Start the multiplayer game
 */
function startMultiplayerGame(
  multiplayer: MultiplayerManager,
  game: Game,
  lobbyUI: LobbyUI
): void {
  const netcode = multiplayer.getNetcode()
  if (!netcode) {
    SafeConsole.error('No netcode available')
    return
  }

  // Hide lobby
  lobbyUI.hide()

  // Set up chat/voice handlers
  game.setChatHandler(() => {
    SafeConsole.log('Chat opened (C key) - TODO: implement chat UI')
    // TODO: Implement text chat UI
    // Could use WebRTC data channel for P2P chat messages
  })

  game.setVoiceToggleHandler((enabled) => {
    SafeConsole.log(`Voice ${enabled ? 'enabled' : 'disabled'} (V key) - TODO: implement voice chat`)
    // TODO: Implement WebRTC voice chat
    // Would need to request microphone access and set up audio tracks
  })

  // Start the game
  game.startMultiplayer(
    multiplayer.getLocalPlayerId(),
    multiplayer.getPlayerIds(),
    multiplayer.getPlayerOrder(),
    netcode,
    multiplayer.getSeed()
  )

  // Mark multiplayer as playing
  multiplayer.setPlaying()

  SafeConsole.log('Multiplayer game started!')
}

// Start the application
main()
