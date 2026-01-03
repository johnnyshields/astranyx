defmodule AstranyxWeb.RoomChannel do
  @moduledoc """
  Room channel for lobby coordination.

  Does NOT handle game simulation - that's P2P between clients.
  Handles:
  - Room join/leave
  - Player presence
  - Game start coordination
  - Relay messages between players (for P2P setup)
  """
  use Phoenix.Channel

  alias Astranyx.Game.Lobby
  alias Astranyx.TurnCredentials

  @impl true
  def join("room:" <> room_id, params, socket) do
    player_id = socket.assigns.player_id
    is_host = params["host"] == true

    result =
      if is_host do
        Lobby.create_room(room_id, player_id)
      else
        Lobby.join_room(room_id, player_id)
      end

    case result do
      {:ok, room} ->
        socket = assign(socket, :room_id, room_id)

        # Defer broadcast until after join completes
        send(self(), {:after_join, player_id, room.players})

        {:ok, %{room: room, player_id: player_id}, socket}

      {:error, reason} ->
        {:error, %{reason: reason}}
    end
  end

  @impl true
  def handle_info({:after_join, player_id, players}, socket) do
    broadcast_from(socket, "player_joined", %{
      player_id: player_id,
      players: players
    })

    {:noreply, socket}
  end

  @impl true
  def handle_in("start_game", _payload, socket) do
    player_id = socket.assigns.player_id
    room_id = socket.assigns.room_id

    case Lobby.start_game(room_id, player_id) do
      {:ok, room} ->
        # Generate deterministic seed for all players
        seed = :rand.uniform(2_147_483_647)

        # Generate TURN credentials for this game session
        # Credentials are only provided when a game actually starts
        turn_credentials =
          try do
            TurnCredentials.generate(room_id)
          rescue
            _ -> nil
          end

        # Broadcast to all players including sender
        broadcast(socket, "game_starting", %{
          room: room,
          # Assign player indices for deterministic simulation
          player_order: Enum.with_index(room.players) |> Map.new(),
          seed: seed,
          # TURN credentials - only available at game start
          turn: turn_credentials
        })

        {:reply, :ok, socket}

      {:error, reason} ->
        {:reply, {:error, %{reason: reason}}, socket}
    end
  end

  @impl true
  def handle_in("list_rooms", _payload, socket) do
    rooms = Lobby.list_rooms()
    {:reply, {:ok, %{rooms: rooms}}, socket}
  end

  @impl true
  def handle_in("ready", _payload, socket) do
    # Player signals they're ready to start P2P connections
    broadcast_from(socket, "player_ready", %{
      player_id: socket.assigns.player_id
    })

    {:noreply, socket}
  end

  @impl true
  def handle_in("ping", _payload, socket) do
    {:reply, {:ok, %{pong: System.system_time(:millisecond)}}, socket}
  end

  @impl true
  def handle_in("refresh_turn_credentials", _payload, socket) do
    room_id = socket.assigns.room_id
    credentials = TurnCredentials.generate(room_id)
    {:reply, {:ok, %{turn: credentials}}, socket}
  rescue
    _ -> {:reply, {:error, %{reason: "TURN not configured"}}, socket}
  end

  @impl true
  def terminate(_reason, socket) do
    player_id = socket.assigns.player_id
    room_id = socket.assigns[:room_id]

    if room_id do
      Lobby.leave_room(room_id, player_id)

      broadcast_from(socket, "player_left", %{
        player_id: player_id
      })
    end

    :ok
  end
end
