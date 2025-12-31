--------------------------------- MODULE LockstepNetwork ---------------------------------
\* P2P Networking and Synchronization Model
\*
\* This module models aspects NOT covered by LockstepState.tla:
\* 1. Message delivery: loss, duplication, reordering
\* 2. Peer lifecycle: connecting, connected, disconnected
\* 3. InputBuffer: per-frame input storage
\* 4. Checksum-based desync detection
\*
\* Implementation references:
\* - InputBuffer.ts: Per-frame input storage
\* - P2PManager.ts: WebRTC peer connections
\* - LockstepNetcode.ts: Message handling
\*
\* ============================================================================
\* FOCUS vs LockstepState
\* ============================================================================
\*
\* INCLUDED:
\* - Message network with loss/duplication/reordering
\* - Peer connection state machine (connecting -> connected <-> disconnected)
\* - InputBuffer per-frame storage (Map<frame, Map<peerId, input>>)
\* - Checksum comparison for desync detection
\*
\* EXCLUDED (covered by other modules):
\* - Leader election (see LeaderElection.tla)
\* - Owner-authoritative events (see LockstepState.tla)
\* - State sync with term validation (see LockstepState.tla)
\* ============================================================================

EXTENDS Integers, FiniteSets, Sequences

CONSTANT Peer
CONSTANT MaxFrame
CONSTANT MaxMessages      \* Maximum messages in network

----
\* Variables

\* Peer connection state: "disconnected", "connecting", "connected"
VARIABLE connectionState

\* Network: set of in-flight messages
\* Each message is: <<type, from, to, frame, checksum>>
\* type: "input" | "input_request"
VARIABLE network

\* InputBuffer: peer -> frame -> has_input (boolean)
\* Simplification: we track presence only, not actual input data
VARIABLE inputBuffer

\* Checksum per peer per frame (for desync detection)
\* peer -> frame -> checksum (0 = no checksum yet)
VARIABLE checksums

\* Current frame per peer
VARIABLE frame

\* Whether peer has detected desync
VARIABLE desynced

vars == <<connectionState, network, inputBuffer, checksums, frame, desynced>>

----
\* Helpers

MinPeer == CHOOSE p \in Peer : \A q \in Peer : p <= q
ConnectedPeers == {p \in Peer : connectionState[p] = "connected"}
IsConnected(p) == connectionState[p] = "connected"

\* Check if peer has all inputs for a frame
HasAllInputs(p, f) ==
    \A q \in ConnectedPeers : inputBuffer[p][f][q]

\* Get minimum frame across connected peers
MinConnectedFrame ==
    IF ConnectedPeers = {} THEN 0
    ELSE CHOOSE f \in {frame[p] : p \in ConnectedPeers} :
         \A q \in ConnectedPeers : frame[q] >= f

----
\* Initial state

Init ==
    /\ connectionState = [p \in Peer |-> IF p = MinPeer THEN "connected" ELSE "disconnected"]
    /\ network = {}
    /\ inputBuffer = [p \in Peer |-> [f \in 0..MaxFrame |-> [q \in Peer |-> FALSE]]]
    /\ checksums = [p \in Peer |-> [f \in 0..MaxFrame |-> 0]]
    /\ frame = [p \in Peer |-> 0]
    /\ desynced = [p \in Peer |-> FALSE]

----
\* Connection State Machine (P2PManager.ts)

\* Implementation: connectToPeer() - initiate connection
StartConnecting(p) ==
    /\ connectionState[p] = "disconnected"
    /\ connectionState' = [connectionState EXCEPT ![p] = "connecting"]
    /\ UNCHANGED <<network, inputBuffer, checksums, frame, desynced>>

\* Implementation: DataChannel.onopen
ConnectionEstablished(p) ==
    /\ connectionState[p] = "connecting"
    /\ connectionState' = [connectionState EXCEPT ![p] = "connected"]
    /\ UNCHANGED <<network, inputBuffer, checksums, frame, desynced>>

\* Implementation: connection.onconnectionstatechange -> "disconnected"/"failed"
\* Also: peer_left event from Phoenix
Disconnect(p) ==
    /\ connectionState[p] \in {"connecting", "connected"}
    /\ connectionState' = [connectionState EXCEPT ![p] = "disconnected"]
    \* Clear any pending messages to/from this peer
    /\ network' = {m \in network : m[2] # p /\ m[3] # p}
    /\ UNCHANGED <<inputBuffer, checksums, frame, desynced>>

\* Implementation: peer_joined event triggers reconnect attempt
Reconnect(p) ==
    /\ connectionState[p] = "disconnected"
    /\ connectionState' = [connectionState EXCEPT ![p] = "connecting"]
    /\ UNCHANGED <<network, inputBuffer, checksums, frame, desynced>>

----
\* Message Network (models unreliable delivery)

\* Implementation: dataChannel.send() for input broadcast
\* InputBuffer.ts:64 storeInput()
SendInput(sender) ==
    /\ IsConnected(sender)
    /\ Cardinality(network) < MaxMessages
    /\ frame[sender] <= MaxFrame
    \* Send to all connected peers
    /\ \E receiver \in ConnectedPeers \ {sender} :
       \E checksum \in {1, 2, 3} :  \* Abstract checksum values
           LET msg == <<"input", sender, receiver, frame[sender], checksum>>
           IN /\ network' = network \union {msg}
              /\ checksums' = [checksums EXCEPT ![sender][frame[sender]] = checksum]
    /\ UNCHANGED <<connectionState, inputBuffer, frame, desynced>>

\* Message delivery (non-deterministic: can deliver, lose, or duplicate)
\* This models unreliable DataChannel (ordered: false, maxRetransmits: 0)
DeliverMessage(msg) ==
    /\ msg \in network
    /\ IsConnected(msg[3])  \* Receiver must be connected
    /\ LET type == msg[1]
           sender == msg[2]
           receiver == msg[3]
           f == msg[4]
           checksum == msg[5]
       IN IF type = "input"
          THEN /\ inputBuffer' = [inputBuffer EXCEPT ![receiver][f][sender] = TRUE]
               /\ checksums' = [checksums EXCEPT ![receiver][f] = checksum]
          ELSE UNCHANGED <<inputBuffer, checksums>>
    /\ network' = network \ {msg}
    /\ UNCHANGED <<connectionState, frame, desynced>>

\* Message loss (unreliable network)
LoseMessage(msg) ==
    /\ msg \in network
    /\ network' = network \ {msg}
    /\ UNCHANGED <<connectionState, inputBuffer, checksums, frame, desynced>>

\* Message duplication (rare but possible)
DuplicateMessage(msg) ==
    /\ msg \in network
    /\ Cardinality(network) < MaxMessages
    \* Create duplicate with same content (idempotent receive)
    /\ UNCHANGED vars  \* Duplication is already in set

----
\* Input Buffer Operations (InputBuffer.ts)

\* Implementation: storeInput() for local input
StoreLocalInput(p) ==
    /\ IsConnected(p)
    /\ frame[p] <= MaxFrame
    /\ ~inputBuffer[p][frame[p]][p]  \* Haven't stored yet
    /\ \E checksum \in {1, 2, 3} :
       /\ inputBuffer' = [inputBuffer EXCEPT ![p][frame[p]][p] = TRUE]
       /\ checksums' = [checksums EXCEPT ![p][frame[p]] = checksum]
    /\ UNCHANGED <<connectionState, network, frame, desynced>>

\* Implementation: tryAdvanceFrame() in LockstepNetcode.ts
AdvanceFrame(p) ==
    /\ IsConnected(p)
    /\ frame[p] < MaxFrame
    /\ HasAllInputs(p, frame[p])  \* All inputs received
    /\ ~desynced[p]                \* Not in desync state
    /\ frame' = [frame EXCEPT ![p] = frame[p] + 1]
    /\ UNCHANGED <<connectionState, network, inputBuffer, checksums, desynced>>

----
\* Desync Detection (InputBuffer.ts:128 checkDesync())

\* Implementation: checkDesync() compares checksums
DetectDesync(p) ==
    /\ IsConnected(p)
    /\ ~desynced[p]
    /\ frame[p] > 0
    \* Check for checksum mismatch with any peer at previous frame
    /\ \E q \in ConnectedPeers \ {p} :
       /\ checksums[p][frame[p]-1] # 0
       /\ checksums[q][frame[p]-1] # 0
       /\ checksums[p][frame[p]-1] # checksums[q][frame[p]-1]
    /\ desynced' = [desynced EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<connectionState, network, inputBuffer, checksums, frame>>

\* Implementation: State sync reception clears desync (see LockstepState.tla)
ClearDesync(p) ==
    /\ desynced[p]
    /\ desynced' = [desynced EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<connectionState, network, inputBuffer, checksums, frame>>

----
\* State Machine

Next ==
    \* Connection management
    \/ \E p \in Peer : StartConnecting(p)
    \/ \E p \in Peer : ConnectionEstablished(p)
    \/ \E p \in Peer : Disconnect(p)
    \/ \E p \in Peer : Reconnect(p)
    \* Message network
    \/ \E p \in Peer : SendInput(p)
    \/ \E m \in network : DeliverMessage(m)
    \/ \E m \in network : LoseMessage(m)
    \* Input buffer
    \/ \E p \in Peer : StoreLocalInput(p)
    \/ \E p \in Peer : AdvanceFrame(p)
    \* Desync
    \/ \E p \in Peer : DetectDesync(p)
    \/ \E p \in Peer : ClearDesync(p)

Fairness ==
    /\ WF_vars(\E p \in Peer : ConnectionEstablished(p))
    /\ WF_vars(\E m \in network : DeliverMessage(m))
    /\ WF_vars(\E p \in Peer : AdvanceFrame(p))
    /\ WF_vars(\E p \in Peer : ClearDesync(p))

Spec == Init /\ [][Next]_vars /\ Fairness

----
\* Safety Properties

\* Type invariant
TypeInvariant ==
    /\ \A p \in Peer : connectionState[p] \in {"disconnected", "connecting", "connected"}
    /\ \A p \in Peer : frame[p] >= 0 /\ frame[p] <= MaxFrame
    /\ \A p \in Peer : desynced[p] \in BOOLEAN
    /\ Cardinality(network) <= MaxMessages

\* Frames stay bounded (within 1 of each other among connected peers)
ConnectedFrameBoundedDrift ==
    \A p, q \in ConnectedPeers :
        frame[p] - frame[q] <= 1 /\ frame[q] - frame[p] <= 1

\* A peer can only advance if it has all inputs
NoAdvanceWithoutInputs ==
    \A p \in ConnectedPeers :
        frame[p] > 0 => HasAllInputs(p, frame[p] - 1)

\* Desync detection is possible (checksums are comparable)
DesyncDetectable ==
    \A p \in ConnectedPeers :
        desynced[p] =>
            \E q \in ConnectedPeers \ {p} :
                checksums[p][frame[p]-1] # checksums[q][frame[p]-1]

----
\* Liveness Properties

\* If messages keep being delivered, frames eventually advance
EventualProgress ==
    (\A p \in ConnectedPeers : frame[p] < MaxFrame) ~>
    (\E p \in ConnectedPeers : frame[p] > 0)

\* Desync is eventually cleared (by state sync)
DesyncEventuallyCleared ==
    \A p \in Peer : desynced[p] ~> ~desynced[p]

----
\* State constraint for bounded model checking

StateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ Cardinality(network) <= MaxMessages

===============================================================================
