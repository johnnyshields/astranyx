defmodule AstranyxWeb.GameSocketTest do
  use AstranyxWeb.ChannelCase, async: false

  describe "connect/3" do
    test "connects successfully with provided player_id" do
      {:ok, socket} = connect(AstranyxWeb.GameSocket, %{"player_id" => "test_player"})

      assert socket.assigns.player_id == "test_player"
      assert is_integer(socket.assigns.connected_at)
    end

    test "generates player_id when not provided" do
      {:ok, socket} = connect(AstranyxWeb.GameSocket, %{})

      assert socket.assigns.player_id != nil
      assert String.length(socket.assigns.player_id) > 0
      assert is_integer(socket.assigns.connected_at)
    end

    test "connects with empty params" do
      {:ok, socket} = connect(AstranyxWeb.GameSocket, %{})

      assert socket.assigns.player_id != nil
    end
  end

  describe "id/1" do
    test "returns player socket id" do
      {:ok, socket} = connect(AstranyxWeb.GameSocket, %{"player_id" => "test_player"})

      assert AstranyxWeb.GameSocket.id(socket) == "player:test_player"
    end
  end

  describe "channel routing" do
    test "routes lobby:* to LobbyChannel" do
      {:ok, socket} = connect(AstranyxWeb.GameSocket, %{"player_id" => "test_player"})
      {:ok, _reply, _socket} = subscribe_and_join(socket, "lobby:main", %{})
    end

    test "routes room:* to RoomChannel" do
      {:ok, socket} = connect(AstranyxWeb.GameSocket, %{"player_id" => "test_player"})

      # We need to create a room first as host
      {:ok, _reply, socket} = subscribe_and_join(socket, "room:test_room", %{"host" => true})

      # Verify we're in the room channel
      assert socket.assigns.room_id == "test_room"
    end

    test "routes signaling:* to SignalingChannel" do
      {:ok, socket} = connect(AstranyxWeb.GameSocket, %{"player_id" => "test_player"})
      {:ok, reply, socket} = subscribe_and_join(socket, "signaling:test_room", %{})

      assert reply.player_id == "test_player"
      assert socket.assigns.room_id == "test_room"
    end
  end
end
