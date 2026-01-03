defmodule AstranyxWeb.SignalingChannelTest do
  use AstranyxWeb.ChannelCase, async: false

  setup do
    {:ok, socket} = connect(AstranyxWeb.GameSocket, %{"player_id" => "test_player"})
    {:ok, socket: socket}
  end

  describe "join" do
    test "joins signaling channel for a room", %{socket: socket} do
      {:ok, reply, _socket} = subscribe_and_join(socket, "signaling:room123", %{})

      assert reply.player_id == "test_player"
    end

    test "assigns room_id to socket", %{socket: socket} do
      {:ok, _reply, socket} = subscribe_and_join(socket, "signaling:room123", %{})

      assert socket.assigns.room_id == "room123"
    end

    test "broadcasts peer_joined after joining", %{socket: socket} do
      {:ok, _reply, socket} = subscribe_and_join(socket, "signaling:room123", %{})

      assert_broadcast "peer_joined", %{player_id: "test_player"}

      leave(socket)
    end
  end

  describe "offer" do
    test "relays SDP offer to other peers", %{socket: socket} do
      {:ok, _reply, socket} = subscribe_and_join(socket, "signaling:room123", %{})
      assert_broadcast "peer_joined", _

      push(socket, "offer", %{"sdp" => "v=0\r\n...", "to" => "target_player"})

      assert_broadcast "offer", %{
        from: "test_player",
        to: "target_player",
        sdp: "v=0\r\n..."
      }
    end
  end

  describe "answer" do
    test "relays SDP answer to other peers", %{socket: socket} do
      {:ok, _reply, socket} = subscribe_and_join(socket, "signaling:room123", %{})
      assert_broadcast "peer_joined", _

      push(socket, "answer", %{"sdp" => "v=0\r\n...", "to" => "target_player"})

      assert_broadcast "answer", %{
        from: "test_player",
        to: "target_player",
        sdp: "v=0\r\n..."
      }
    end
  end

  describe "ice_candidate" do
    test "relays ICE candidate to other peers", %{socket: socket} do
      {:ok, _reply, socket} = subscribe_and_join(socket, "signaling:room123", %{})
      assert_broadcast "peer_joined", _

      candidate = %{
        "candidate" => "candidate:1 1 UDP 2122252543 192.168.1.1 12345 typ host",
        "sdpMLineIndex" => 0,
        "sdpMid" => "0"
      }

      push(socket, "ice_candidate", %{"candidate" => candidate, "to" => "target_player"})

      assert_broadcast "ice_candidate", %{
        from: "test_player",
        to: "target_player",
        candidate: ^candidate
      }
    end
  end

  describe "terminate" do
    test "broadcasts peer_left on disconnect", %{socket: socket} do
      {:ok, _reply, socket} = subscribe_and_join(socket, "signaling:room123", %{})
      assert_broadcast "peer_joined", _

      # Close the socket to trigger terminate
      Process.unlink(socket.channel_pid)
      close(socket)

      assert_broadcast "peer_left", %{player_id: "test_player"}
    end
  end
end
