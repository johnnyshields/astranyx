//! Binary codec for network messages.
//!
//! Provides efficient serialization for network transmission.

use crate::GameMessage;
use thiserror::Error;

/// Errors that can occur during encoding/decoding.
#[derive(Debug, Error)]
pub enum CodecError {
    #[error("encode error: {0}")]
    Encode(#[from] bincode::error::EncodeError),

    #[error("decode error: {0}")]
    Decode(#[from] bincode::error::DecodeError),
}

/// Encode a message to bytes.
pub fn encode(message: &GameMessage) -> Result<Vec<u8>, CodecError> {
    Ok(bincode::serde::encode_to_vec(message, bincode::config::standard())?)
}

/// Decode a message from bytes.
pub fn decode(data: &[u8]) -> Result<GameMessage, CodecError> {
    let (message, _) = bincode::serde::decode_from_slice(data, bincode::config::standard())?;
    Ok(message)
}

/// Estimate the encoded size of a message.
/// Useful for buffer allocation.
pub fn estimate_size(message: &GameMessage) -> usize {
    match message {
        GameMessage::Input(_) => 8,      // peer_id + frame + input
        GameMessage::InputBatch(m) => 8 + m.inputs.len() * 2,
        GameMessage::Heartbeat(_) => 16,
        GameMessage::HeartbeatAck(_) => 24,
        GameMessage::SyncRequest(_) => 8,
        GameMessage::SyncResponse(m) => 12 + m.state_data.len(),
        GameMessage::StateHash(_) => 16,
        GameMessage::GameStart(_) => 8,
        GameMessage::Pause(_) => 8,
        GameMessage::Resume(_) => 4,
        GameMessage::Disconnect(_) => 4,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{InputMessage, HeartbeatMessage};
    use astranyx_core::PlayerInput;

    #[test]
    fn roundtrip_input() {
        let msg = GameMessage::Input(InputMessage {
            peer_id: 1,
            frame: 12345,
            input: PlayerInput::from_bits(PlayerInput::UP | PlayerInput::FIRE),
        });

        let encoded = encode(&msg).unwrap();
        let decoded = decode(&encoded).unwrap();

        if let (GameMessage::Input(orig), GameMessage::Input(dec)) = (&msg, &decoded) {
            assert_eq!(orig.peer_id, dec.peer_id);
            assert_eq!(orig.frame, dec.frame);
            assert_eq!(orig.input.bits, dec.input.bits);
        } else {
            panic!("wrong message type");
        }
    }

    #[test]
    fn roundtrip_heartbeat() {
        let msg = GameMessage::Heartbeat(HeartbeatMessage {
            peer_id: 2,
            sequence: 100,
            timestamp_ms: 1234567890,
        });

        let encoded = encode(&msg).unwrap();
        let decoded = decode(&encoded).unwrap();

        if let (GameMessage::Heartbeat(orig), GameMessage::Heartbeat(dec)) = (&msg, &decoded) {
            assert_eq!(orig.peer_id, dec.peer_id);
            assert_eq!(orig.sequence, dec.sequence);
            assert_eq!(orig.timestamp_ms, dec.timestamp_ms);
        } else {
            panic!("wrong message type");
        }
    }

    #[test]
    fn compact_encoding() {
        let msg = GameMessage::Input(InputMessage {
            peer_id: 1,
            frame: 100,
            input: PlayerInput::from_bits(PlayerInput::FIRE),
        });

        let encoded = encode(&msg).unwrap();
        // Should be very compact
        assert!(encoded.len() < 16, "encoded size was {}", encoded.len());
    }
}
