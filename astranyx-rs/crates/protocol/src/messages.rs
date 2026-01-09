//! Network message types.
//!
//! All messages exchanged between peers in the lockstep protocol.

use astranyx_core::PlayerInput;
use serde::{Deserialize, Serialize};

/// Unique identifier for a peer in the network.
pub type PeerId = u8;

/// Frame number in the simulation.
pub type FrameNumber = u32;

/// All possible game messages.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum GameMessage {
    /// Input for a single frame.
    Input(InputMessage),

    /// Batch of inputs for multiple frames.
    InputBatch(InputBatchMessage),

    /// Heartbeat for RTT measurement.
    Heartbeat(HeartbeatMessage),

    /// Response to heartbeat.
    HeartbeatAck(HeartbeatAckMessage),

    /// Request state sync (for late joiners or desync recovery).
    SyncRequest(SyncRequestMessage),

    /// Full state sync response.
    SyncResponse(SyncResponseMessage),

    /// Hash of current state (for desync detection).
    StateHash(StateHashMessage),

    /// Game is starting.
    GameStart(GameStartMessage),

    /// Player has paused.
    Pause(PauseMessage),

    /// Player has resumed.
    Resume(ResumeMessage),

    /// Player is disconnecting gracefully.
    Disconnect(DisconnectMessage),
}

/// Input for a single frame.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InputMessage {
    pub peer_id: PeerId,
    pub frame: FrameNumber,
    pub input: PlayerInput,
}

/// Batch of inputs for multiple frames.
/// Used to reduce packet overhead by combining multiple frames.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InputBatchMessage {
    pub peer_id: PeerId,
    pub start_frame: FrameNumber,
    pub inputs: Vec<PlayerInput>,
}

/// Heartbeat for measuring RTT.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HeartbeatMessage {
    pub peer_id: PeerId,
    pub sequence: u32,
    pub timestamp_ms: u64,
}

/// Response to heartbeat, echoing back the timestamp.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HeartbeatAckMessage {
    pub peer_id: PeerId,
    pub sequence: u32,
    pub echo_timestamp_ms: u64,
    pub local_timestamp_ms: u64,
}

/// Request a state sync at a specific frame.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SyncRequestMessage {
    pub peer_id: PeerId,
    pub frame: FrameNumber,
}

/// Full state sync response.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SyncResponseMessage {
    pub peer_id: PeerId,
    pub frame: FrameNumber,
    pub state_data: Vec<u8>,
}

/// Hash of state for desync detection.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateHashMessage {
    pub peer_id: PeerId,
    pub frame: FrameNumber,
    pub hash: u64,
}

/// Game start message with initial configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GameStartMessage {
    pub seed: u32,
    pub player_count: u8,
    pub local_player_index: u8,
    pub input_delay: u8,
}

/// Player has paused the game.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PauseMessage {
    pub peer_id: PeerId,
    pub frame: FrameNumber,
}

/// Player has resumed the game.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResumeMessage {
    pub peer_id: PeerId,
}

/// Player is disconnecting.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DisconnectMessage {
    pub peer_id: PeerId,
    pub reason: DisconnectReason,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum DisconnectReason {
    Quit,
    Timeout,
    Error,
}

/// Signaling messages (sent via WebSocket to Phoenix server).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SignalingMessage {
    /// Join a room.
    JoinRoom { room_id: String, player_name: String },

    /// Leave a room.
    LeaveRoom { room_id: String },

    /// Room state update from server.
    RoomState { players: Vec<String>, ready: Vec<bool> },

    /// Mark self as ready.
    Ready { ready: bool },

    /// Server signals game should start.
    StartGame { seed: u32, player_order: Vec<String> },

    /// WebRTC offer.
    Offer { target: String, sdp: String },

    /// WebRTC answer.
    Answer { target: String, sdp: String },

    /// WebRTC ICE candidate.
    IceCandidate { target: String, candidate: String },
}
