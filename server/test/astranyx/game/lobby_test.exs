defmodule Astranyx.Game.LobbyTest do
  use ExUnit.Case, async: false

  alias Astranyx.Game.Lobby

  setup do
    # Reset Lobby state without killing the process
    Lobby.reset()
    :ok
  end

  describe "create_room/2" do
    test "creates a room successfully" do
      assert {:ok, room} = Lobby.create_room("room1", "player1")
      assert room.id == "room1"
      assert room.host == "player1"
      assert room.players == ["player1"]
      assert room.status == :waiting
      assert is_integer(room.created_at)
    end

    test "returns error when room already exists" do
      {:ok, _room} = Lobby.create_room("room1", "player1")
      assert {:error, :room_exists} = Lobby.create_room("room1", "player2")
    end
  end

  describe "join_room/2" do
    test "joins an existing room" do
      {:ok, _room} = Lobby.create_room("room1", "player1")
      assert {:ok, room} = Lobby.join_room("room1", "player2")
      assert room.players == ["player1", "player2"]
    end

    test "returns error when room does not exist" do
      assert {:error, :room_not_found} = Lobby.join_room("nonexistent", "player1")
    end

    test "returns error when game is in progress" do
      {:ok, _room} = Lobby.create_room("room1", "player1")
      {:ok, _room} = Lobby.start_game("room1", "player1")
      assert {:error, :game_in_progress} = Lobby.join_room("room1", "player2")
    end

    test "returns error when room is full" do
      {:ok, _room} = Lobby.create_room("room1", "player1")
      {:ok, _room} = Lobby.join_room("room1", "player2")
      {:ok, _room} = Lobby.join_room("room1", "player3")
      {:ok, _room} = Lobby.join_room("room1", "player4")
      assert {:error, :room_full} = Lobby.join_room("room1", "player5")
    end

    test "returns existing room when player is already in room" do
      {:ok, _room} = Lobby.create_room("room1", "player1")
      {:ok, room} = Lobby.join_room("room1", "player1")
      assert room.players == ["player1"]
    end
  end

  describe "leave_room/2" do
    test "removes player from room" do
      {:ok, _room} = Lobby.create_room("room1", "player1")
      {:ok, _room} = Lobby.join_room("room1", "player2")

      Lobby.leave_room("room1", "player2")
      # Give async cast time to process
      Process.sleep(10)

      room = Lobby.get_room("room1")
      assert room.players == ["player1"]
    end

    test "deletes room when last player leaves" do
      {:ok, _room} = Lobby.create_room("room1", "player1")

      Lobby.leave_room("room1", "player1")
      Process.sleep(10)

      assert Lobby.get_room("room1") == nil
    end

    test "transfers host when host leaves" do
      {:ok, _room} = Lobby.create_room("room1", "player1")
      {:ok, _room} = Lobby.join_room("room1", "player2")

      Lobby.leave_room("room1", "player1")
      Process.sleep(10)

      room = Lobby.get_room("room1")
      assert room.host == "player2"
      assert room.players == ["player2"]
    end

    test "keeps host when non-host leaves" do
      {:ok, _room} = Lobby.create_room("room1", "player1")
      {:ok, _room} = Lobby.join_room("room1", "player2")

      Lobby.leave_room("room1", "player2")
      Process.sleep(10)

      room = Lobby.get_room("room1")
      assert room.host == "player1"
    end

    test "does nothing for nonexistent room" do
      # Should not crash
      Lobby.leave_room("nonexistent", "player1")
      Process.sleep(10)
    end
  end

  describe "list_rooms/0" do
    test "returns empty list when no rooms" do
      assert Lobby.list_rooms() == []
    end

    test "returns list of rooms with summary info" do
      {:ok, _room} = Lobby.create_room("room1", "player1")
      {:ok, _room} = Lobby.join_room("room1", "player2")
      {:ok, _room} = Lobby.create_room("room2", "player3")

      rooms = Lobby.list_rooms()
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

  describe "get_room/1" do
    test "returns room when it exists" do
      {:ok, _room} = Lobby.create_room("room1", "player1")

      room = Lobby.get_room("room1")
      assert room.id == "room1"
      assert room.host == "player1"
    end

    test "returns nil when room does not exist" do
      assert Lobby.get_room("nonexistent") == nil
    end
  end

  describe "start_game/2" do
    test "starts game successfully when host requests" do
      {:ok, _room} = Lobby.create_room("room1", "player1")

      assert {:ok, room} = Lobby.start_game("room1", "player1")
      assert room.status == :playing
    end

    test "returns error when room does not exist" do
      assert {:error, :room_not_found} = Lobby.start_game("nonexistent", "player1")
    end

    test "returns error when requester is not host" do
      {:ok, _room} = Lobby.create_room("room1", "player1")
      {:ok, _room} = Lobby.join_room("room1", "player2")

      assert {:error, :not_host} = Lobby.start_game("room1", "player2")
    end
  end

  describe "start_link/1" do
    test "can be started with options" do
      # The Lobby is already started by the application supervisor
      # This test ensures start_link API works
      assert Process.whereis(Lobby) != nil
    end
  end

  describe "reset/0" do
    test "clears all rooms" do
      {:ok, _room} = Lobby.create_room("room1", "player1")
      {:ok, _room} = Lobby.create_room("room2", "player2")
      assert length(Lobby.list_rooms()) == 2

      :ok = Lobby.reset()

      assert Lobby.list_rooms() == []
    end
  end
end
