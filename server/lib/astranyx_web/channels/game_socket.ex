defmodule AstranyxWeb.GameSocket do
  @moduledoc """
  Socket for game connections.

  Handles:
  - WebRTC signaling (SDP exchange, ICE candidates)
  - Game room channels
  - Player presence
  """
  use Phoenix.Socket

  # Channels
  channel "lobby:*", AstranyxWeb.LobbyChannel
  channel "room:*", AstranyxWeb.RoomChannel
  channel "signaling:*", AstranyxWeb.SignalingChannel

  @impl true
  def connect(params, socket, _connect_info) do
    player_id = params["player_id"] || generate_player_id()

    socket =
      socket
      |> assign(:player_id, player_id)
      |> assign(:connected_at, System.system_time(:millisecond))

    {:ok, socket}
  end

  @impl true
  def id(socket), do: "player:#{socket.assigns.player_id}"

  defp generate_player_id do
    :crypto.strong_rand_bytes(8) |> Base.url_encode64(padding: false)
  end
end
