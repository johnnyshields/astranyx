defmodule AstranyxWeb.RoomChannelTest do
  use AstranyxWeb.ChannelCase, async: false

  alias Astranyx.Game.Lobby

  setup do
    # Set up TURN credentials for testing
    System.put_env("TURN_SECRET", "test-secret-123")
    System.put_env("TURN_URLS", "turn:test.example.com:3478")

    # Reset Lobby state without killing the process
    Lobby.reset()

    on_exit(fn ->
      System.delete_env("TURN_SECRET")
      System.delete_env("TURN_URLS")
    end)

    {:ok, socket} = connect(AstranyxWeb.GameSocket, %{"player_id" => "test_player"})
    {:ok, socket: socket}
  end

  describe "join as host" do
    test "creates a new room when joining as host", %{socket: socket} do
      {:ok, reply, _socket} = subscribe_and_join(socket, "room:test_room", %{"host" => true})

      assert reply.room.id == "test_room"
      assert reply.room.host == "test_player"
      assert reply.room.players == ["test_player"]
      assert reply.room.status == :waiting
      assert reply.player_id == "test_player"
    end

    test "broadcasts player_joined after joining as host", %{socket: socket} do
      {:ok, _reply, socket} = subscribe_and_join(socket, "room:test_room", %{"host" => true})

      # After join message is sent asynchronously
      assert_broadcast "player_joined", %{player_id: "test_player", players: ["test_player"]}

      # Clean up
      leave(socket)
    end

    test "returns error when room already exists", %{socket: socket} do
      {:ok, _room} = Lobby.create_room("test_room", "other_player")

      assert {:error, %{reason: :room_exists}} =
               subscribe_and_join(socket, "room:test_room", %{"host" => true})
    end
  end

  describe "join as guest" do
    test "joins existing room as guest", %{socket: socket} do
      {:ok, _room} = Lobby.create_room("test_room", "host_player")

      {:ok, reply, _socket} = subscribe_and_join(socket, "room:test_room", %{})

      assert reply.room.id == "test_room"
      assert reply.room.players == ["host_player", "test_player"]
      assert reply.player_id == "test_player"
    end

    test "returns error when room does not exist", %{socket: socket} do
      assert {:error, %{reason: :room_not_found}} =
               subscribe_and_join(socket, "room:nonexistent", %{})
    end

    test "broadcasts player_joined to other members", %{socket: socket} do
      {:ok, _room} = Lobby.create_room("test_room", "host_player")
      {:ok, _reply, socket} = subscribe_and_join(socket, "room:test_room", %{})

      assert_broadcast "player_joined", %{
        player_id: "test_player",
        players: ["host_player", "test_player"]
      }

      leave(socket)
    end
  end

  describe "start_game" do
    test "host can start game", %{socket: socket} do
      {:ok, _reply, socket} = subscribe_and_join(socket, "room:test_room", %{"host" => true})

      # Wait for after_join broadcast
      assert_broadcast "player_joined", _

      ref = push(socket, "start_game", %{})
      assert_reply ref, :ok

      assert_broadcast "game_starting", payload
      assert payload.room.status == :playing
      assert is_integer(payload.seed)
      assert is_map(payload.player_order)
      assert payload.turn != nil
    end

    test "non-host cannot start game", %{socket: socket} do
      {:ok, _room} = Lobby.create_room("test_room", "host_player")
      {:ok, _reply, socket} = subscribe_and_join(socket, "room:test_room", %{})

      # Wait for after_join broadcast
      assert_broadcast "player_joined", _

      ref = push(socket, "start_game", %{})
      assert_reply ref, :error, %{reason: :not_host}
    end

    test "includes TURN credentials in game_starting broadcast", %{socket: socket} do
      {:ok, _reply, socket} = subscribe_and_join(socket, "room:test_room", %{"host" => true})
      assert_broadcast "player_joined", _

      ref = push(socket, "start_game", %{})
      assert_reply ref, :ok

      assert_broadcast "game_starting", payload
      assert payload.turn != nil
      assert Map.has_key?(payload.turn, :username)
      assert Map.has_key?(payload.turn, :credential)
      assert Map.has_key?(payload.turn, :urls)
    end
  end

  describe "start_game without TURN configured" do
    setup do
      System.delete_env("TURN_SECRET")
      :ok
    end

    test "game starts but turn is nil", %{socket: socket} do
      {:ok, _reply, socket} = subscribe_and_join(socket, "room:test_room", %{"host" => true})
      assert_broadcast "player_joined", _

      ref = push(socket, "start_game", %{})
      assert_reply ref, :ok

      assert_broadcast "game_starting", payload
      assert payload.turn == nil
    end
  end

  describe "list_rooms" do
    test "returns list of available rooms", %{socket: socket} do
      {:ok, _room} = Lobby.create_room("room1", "player1")
      {:ok, _room} = Lobby.create_room("room2", "player2")

      {:ok, _reply, socket} = subscribe_and_join(socket, "room:room1", %{})
      assert_broadcast "player_joined", _

      ref = push(socket, "list_rooms", %{})
      assert_reply ref, :ok, %{rooms: rooms}

      assert length(rooms) == 2
      room_ids = Enum.map(rooms, & &1.id)
      assert "room1" in room_ids
      assert "room2" in room_ids
    end
  end

  describe "ready" do
    test "broadcasts player_ready to other members", %{socket: socket} do
      {:ok, _reply, socket} = subscribe_and_join(socket, "room:test_room", %{"host" => true})
      assert_broadcast "player_joined", _

      push(socket, "ready", %{})

      assert_broadcast "player_ready", %{player_id: "test_player"}
    end
  end

  describe "ping" do
    test "returns pong with timestamp", %{socket: socket} do
      {:ok, _reply, socket} = subscribe_and_join(socket, "room:test_room", %{"host" => true})
      assert_broadcast "player_joined", _

      ref = push(socket, "ping", %{})
      assert_reply ref, :ok, %{pong: timestamp}

      assert is_integer(timestamp)
    end
  end

  describe "refresh_turn_credentials" do
    test "returns new TURN credentials", %{socket: socket} do
      {:ok, _reply, socket} = subscribe_and_join(socket, "room:test_room", %{"host" => true})
      assert_broadcast "player_joined", _

      ref = push(socket, "refresh_turn_credentials", %{})
      assert_reply ref, :ok, %{turn: credentials}

      assert Map.has_key?(credentials, :username)
      assert Map.has_key?(credentials, :credential)
      assert Map.has_key?(credentials, :urls)
    end
  end

  describe "refresh_turn_credentials without TURN configured" do
    setup do
      System.delete_env("TURN_SECRET")
      :ok
    end

    test "returns error when TURN not configured", %{socket: socket} do
      {:ok, _reply, socket} = subscribe_and_join(socket, "room:test_room", %{"host" => true})
      assert_broadcast "player_joined", _

      ref = push(socket, "refresh_turn_credentials", %{})
      assert_reply ref, :error, %{reason: "TURN not configured"}
    end
  end

  describe "terminate" do
    test "removes player from room on disconnect", %{socket: socket} do
      {:ok, _room} = Lobby.create_room("test_room", "host_player")
      {:ok, _reply, socket} = subscribe_and_join(socket, "room:test_room", %{})
      assert_broadcast "player_joined", _

      # Verify player is in room
      room = Lobby.get_room("test_room")
      assert "test_player" in room.players

      # Close connection - unlink first to avoid exit
      Process.unlink(socket.channel_pid)
      close(socket)
      Process.sleep(50)

      # Verify player was removed
      room = Lobby.get_room("test_room")
      refute "test_player" in room.players
    end

    test "broadcasts player_left on disconnect", %{socket: socket} do
      {:ok, _room} = Lobby.create_room("test_room", "host_player")
      {:ok, _reply, socket} = subscribe_and_join(socket, "room:test_room", %{})
      assert_broadcast "player_joined", _

      # Leave triggers terminate callback
      Process.unlink(socket.channel_pid)
      close(socket)

      assert_broadcast "player_left", %{player_id: "test_player"}
    end
  end
end
