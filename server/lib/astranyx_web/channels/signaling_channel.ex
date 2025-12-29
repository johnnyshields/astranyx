defmodule AstranyxWeb.SignalingChannel do
  @moduledoc """
  WebRTC signaling channel.

  Handles SDP offer/answer exchange and ICE candidate relay
  between peers for establishing WebRTC DataChannel connections.
  """
  use Phoenix.Channel

  @impl true
  def join("signaling:" <> room_id, _params, socket) do
    socket = assign(socket, :room_id, room_id)

    # Notify others in the room
    broadcast_from(socket, "peer_joined", %{
      player_id: socket.assigns.player_id
    })

    {:ok, %{player_id: socket.assigns.player_id}, socket}
  end

  @impl true
  def handle_in("offer", %{"sdp" => sdp, "to" => target_player}, socket) do
    # Relay SDP offer to specific peer
    broadcast_from(socket, "offer", %{
      from: socket.assigns.player_id,
      to: target_player,
      sdp: sdp
    })

    {:noreply, socket}
  end

  @impl true
  def handle_in("answer", %{"sdp" => sdp, "to" => target_player}, socket) do
    # Relay SDP answer to specific peer
    broadcast_from(socket, "answer", %{
      from: socket.assigns.player_id,
      to: target_player,
      sdp: sdp
    })

    {:noreply, socket}
  end

  @impl true
  def handle_in("ice_candidate", %{"candidate" => candidate, "to" => target_player}, socket) do
    # Relay ICE candidate to specific peer
    broadcast_from(socket, "ice_candidate", %{
      from: socket.assigns.player_id,
      to: target_player,
      candidate: candidate
    })

    {:noreply, socket}
  end

  @impl true
  def terminate(_reason, socket) do
    broadcast_from(socket, "peer_left", %{
      player_id: socket.assigns.player_id
    })

    :ok
  end
end
