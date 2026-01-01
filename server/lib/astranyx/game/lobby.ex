defmodule Astranyx.Game.Lobby do
  @moduledoc """
  Lobby management for matchmaking and room coordination.

  The server does NOT run game simulation - that happens P2P between clients.
  This module handles:
  - Creating/listing rooms
  - Player presence in rooms
  - Coordinating game start
  """
  use GenServer
  require Logger

  @max_players_per_room 4

  # Client API

  def start_link(_opts) do
    GenServer.start_link(__MODULE__, %{}, name: __MODULE__)
  end

  def create_room(room_id, host_player_id) do
    GenServer.call(__MODULE__, {:create_room, room_id, host_player_id})
  end

  def join_room(room_id, player_id) do
    GenServer.call(__MODULE__, {:join_room, room_id, player_id})
  end

  def leave_room(room_id, player_id) do
    GenServer.cast(__MODULE__, {:leave_room, room_id, player_id})
  end

  def list_rooms do
    GenServer.call(__MODULE__, :list_rooms)
  end

  def get_room(room_id) do
    GenServer.call(__MODULE__, {:get_room, room_id})
  end

  def start_game(room_id, player_id) do
    GenServer.call(__MODULE__, {:start_game, room_id, player_id})
  end

  # Server callbacks

  @impl true
  def init(_) do
    {:ok, %{rooms: %{}}}
  end

  @impl true
  def handle_call({:create_room, room_id, host_player_id}, _from, state) do
    if Map.has_key?(state.rooms, room_id) do
      {:reply, {:error, :room_exists}, state}
    else
      room = %{
        id: room_id,
        host: host_player_id,
        players: [host_player_id],
        # :waiting | :starting | :playing
        status: :waiting,
        created_at: System.system_time(:millisecond)
      }

      state = put_in(state, [:rooms, room_id], room)
      Logger.info("Room #{room_id} created by #{host_player_id}")

      {:reply, {:ok, room}, state}
    end
  end

  @impl true
  def handle_call({:join_room, room_id, player_id}, _from, state) do
    case Map.get(state.rooms, room_id) do
      nil ->
        {:reply, {:error, :room_not_found}, state}

      %{status: :playing} ->
        {:reply, {:error, :game_in_progress}, state}

      %{players: players} when length(players) >= @max_players_per_room ->
        {:reply, {:error, :room_full}, state}

      room ->
        if player_id in room.players do
          {:reply, {:ok, room}, state}
        else
          room = %{room | players: room.players ++ [player_id]}
          state = put_in(state, [:rooms, room_id], room)
          Logger.info("Player #{player_id} joined room #{room_id}")

          {:reply, {:ok, room}, state}
        end
    end
  end

  @impl true
  def handle_call(:list_rooms, _from, state) do
    rooms =
      state.rooms
      |> Map.values()
      |> Enum.map(fn room ->
        %{
          id: room.id,
          host: room.host,
          player_count: length(room.players),
          max_players: @max_players_per_room,
          status: room.status
        }
      end)

    {:reply, rooms, state}
  end

  @impl true
  def handle_call({:get_room, room_id}, _from, state) do
    {:reply, Map.get(state.rooms, room_id), state}
  end

  @impl true
  def handle_call({:start_game, room_id, player_id}, _from, state) do
    case Map.get(state.rooms, room_id) do
      nil ->
        {:reply, {:error, :room_not_found}, state}

      %{host: host} when host != player_id ->
        {:reply, {:error, :not_host}, state}

      %{players: []} ->
        {:reply, {:error, :not_enough_players}, state}

      room ->
        room = %{room | status: :playing}
        state = put_in(state, [:rooms, room_id], room)
        Logger.info("Game started in room #{room_id}")

        {:reply, {:ok, room}, state}
    end
  end

  @impl true
  def handle_cast({:leave_room, room_id, player_id}, state) do
    case Map.get(state.rooms, room_id) do
      nil ->
        {:noreply, state}

      room ->
        players = List.delete(room.players, player_id)
        state = update_room_after_leave(state, room_id, room, players)
        {:noreply, state}
    end
  end

  defp update_room_after_leave(state, room_id, _room, []) do
    Logger.info("Room #{room_id} deleted (empty)")
    update_in(state, [:rooms], &Map.delete(&1, room_id))
  end

  defp update_room_after_leave(state, room_id, room, players) do
    new_host = if room.host in players, do: room.host, else: hd(players)
    room = %{room | players: players, host: new_host}
    put_in(state, [:rooms, room_id], room)
  end
end
