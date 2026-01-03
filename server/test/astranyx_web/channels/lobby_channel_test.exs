defmodule AstranyxWeb.LobbyChannelTest do
  use AstranyxWeb.ChannelCase, async: false

  alias Astranyx.Game.Lobby

  setup do
    # Reset Lobby state without killing the process
    Lobby.reset()

    {:ok, socket} = connect(AstranyxWeb.GameSocket, %{"player_id" => "test_player"})
    {:ok, socket: socket}
  end

  describe "join" do
    test "joins lobby:main channel successfully", %{socket: socket} do
      {:ok, reply, _socket} = subscribe_and_join(socket, "lobby:main", %{})

      assert reply.player_id == "test_player"
    end
  end

  describe "list_rooms" do
    test "returns empty list when no rooms", %{socket: socket} do
      {:ok, _reply, socket} = subscribe_and_join(socket, "lobby:main", %{})

      ref = push(socket, "list_rooms", %{})
      assert_reply ref, :ok, %{rooms: rooms}

      assert rooms == []
    end

    test "returns list of available rooms", %{socket: socket} do
      # Create some rooms
      {:ok, _room} = Lobby.create_room("room1", "player1")
      {:ok, _room} = Lobby.create_room("room2", "player2")
      {:ok, _room} = Lobby.join_room("room1", "player3")

      {:ok, _reply, socket} = subscribe_and_join(socket, "lobby:main", %{})

      ref = push(socket, "list_rooms", %{})
      assert_reply ref, :ok, %{rooms: rooms}

      assert length(rooms) == 2

      room1 = Enum.find(rooms, &(&1.id == "room1"))
      assert room1.host == "player1"
      assert room1.player_count == 2
      assert room1.max_players == 4
      assert room1.status == :waiting

      room2 = Enum.find(rooms, &(&1.id == "room2"))
      assert room2.player_count == 1
    end
  end
end
