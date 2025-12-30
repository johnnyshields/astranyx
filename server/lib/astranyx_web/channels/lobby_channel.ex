defmodule AstranyxWeb.LobbyChannel do
  @moduledoc """
  Lobby channel for browsing available rooms.

  This channel allows players to list rooms without joining one first.
  """
  use Phoenix.Channel

  alias Astranyx.Game.Lobby

  @impl true
  def join("lobby:main", _params, socket) do
    {:ok, %{player_id: socket.assigns.player_id}, socket}
  end

  @impl true
  def handle_in("list_rooms", _payload, socket) do
    rooms = Lobby.list_rooms()
    {:reply, {:ok, %{rooms: rooms}}, socket}
  end
end
