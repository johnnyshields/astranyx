--------------------------------- MODULE LockstepNetwork ---------------------------------
\* P2P Networking and Synchronization Model
\*
\* This module models aspects NOT covered by LockstepState.tla:
\* 1. Message delivery: loss, duplication, reordering
\* 2. Peer lifecycle: connecting, connected, disconnected
\* 3. InputBuffer: per-frame input storage
\* 4. Checksum-based desync detection
\* 5. WebRTC-specific behaviors: ICE restart, connection flapping
\* 6. Network partitions: symmetric, asymmetric, partial
\*
\* Implementation references:
\* - InputBuffer.ts: Per-frame input storage
\* - P2PManager.ts: WebRTC peer connections
\* - LockstepNetcode.ts: Message handling
\* - WebRTCClient.ts: ICE restart handling
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
\* - ICE restart (WebRTC NAT traversal recovery)
\* - Connection flapping (rapid connect/disconnect cycles)
\* - Partial network partitions (A<->B ok, A<->C partitioned)
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
CONSTANT MaxFlaps         \* Maximum connection flap count before stabilization

----
\* Variables

\* Peer connection state: "disconnected", "connecting", "connected", "ice_restarting"
\* Implementation: RTCPeerConnection.connectionState + custom ice_restarting flag
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

\* Partial partition matrix: partitioned[p1][p2] = TRUE means p1 cannot reach p2
\* Note: Can be asymmetric (p1->p2 blocked but p2->p1 ok)
VARIABLE partitioned

\* Connection flap counter per peer (for detecting unstable connections)
\* Implementation: P2PManager tracks reconnection attempts
VARIABLE flapCount

\* ICE restart in progress: peer -> boolean
\* Implementation: RTCPeerConnection.restartIce() pending
VARIABLE iceRestarting

vars == <<connectionState, network, inputBuffer, checksums, frame, desynced, partitioned, flapCount, iceRestarting>>

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

\* Check if two peers can communicate (not partitioned)
CanReach(from, to) ==
    /\ IsConnected(from)
    /\ IsConnected(to)
    /\ ~partitioned[from][to]

\* Check if peer is in ICE restart state
IsIceRestarting(p) == iceRestarting[p]

\* Check if peer has exceeded flap threshold (unstable connection)
IsFlapping(p) == flapCount[p] >= MaxFlaps

----
\* Initial state

Init ==
    /\ connectionState = [p \in Peer |-> IF p = MinPeer THEN "connected" ELSE "disconnected"]
    /\ network = {}
    /\ inputBuffer = [p \in Peer |-> [f \in 0..MaxFrame |-> [q \in Peer |-> FALSE]]]
    /\ checksums = [p \in Peer |-> [f \in 0..MaxFrame |-> 0]]
    /\ frame = [p \in Peer |-> 0]
    /\ desynced = [p \in Peer |-> FALSE]
    /\ partitioned = [p \in Peer |-> [q \in Peer |-> FALSE]]  \* No partitions initially
    /\ flapCount = [p \in Peer |-> 0]
    /\ iceRestarting = [p \in Peer |-> FALSE]

----
\* Connection State Machine (P2PManager.ts)

\* Implementation: connectToPeer() - initiate connection
StartConnecting(p) ==
    /\ connectionState[p] = "disconnected"
    /\ ~IsFlapping(p)  \* Don't reconnect if flapping too much
    /\ connectionState' = [connectionState EXCEPT ![p] = "connecting"]
    /\ UNCHANGED <<network, inputBuffer, checksums, frame, desynced, partitioned, flapCount, iceRestarting>>

\* Implementation: DataChannel.onopen
ConnectionEstablished(p) ==
    /\ connectionState[p] \in {"connecting", "ice_restarting"}
    /\ connectionState' = [connectionState EXCEPT ![p] = "connected"]
    /\ iceRestarting' = [iceRestarting EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<network, inputBuffer, checksums, frame, desynced, partitioned, flapCount>>

\* Implementation: connection.onconnectionstatechange -> "disconnected"/"failed"
\* Also: peer_left event from Phoenix
Disconnect(p) ==
    /\ connectionState[p] \in {"connecting", "connected", "ice_restarting"}
    /\ connectionState' = [connectionState EXCEPT ![p] = "disconnected"]
    \* Clear any pending messages to/from this peer
    /\ network' = {m \in network : m[2] # p /\ m[3] # p}
    \* Increment flap counter
    /\ flapCount' = [flapCount EXCEPT ![p] = flapCount[p] + 1]
    /\ iceRestarting' = [iceRestarting EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<inputBuffer, checksums, frame, desynced, partitioned>>

\* Implementation: peer_joined event triggers reconnect attempt
Reconnect(p) ==
    /\ connectionState[p] = "disconnected"
    /\ ~IsFlapping(p)  \* Backoff if flapping
    /\ connectionState' = [connectionState EXCEPT ![p] = "connecting"]
    /\ UNCHANGED <<network, inputBuffer, checksums, frame, desynced, partitioned, flapCount, iceRestarting>>

----
\* Message Network (models unreliable delivery)

\* Implementation: dataChannel.send() for input broadcast
\* InputBuffer.ts:64 storeInput()
SendInput(sender) ==
    /\ IsConnected(sender)
    /\ Cardinality(network) < MaxMessages
    /\ frame[sender] <= MaxFrame
    \* Send to all connected peers (partition-aware)
    /\ \E receiver \in ConnectedPeers \ {sender} :
       /\ CanReach(sender, receiver)  \* Partition check
       /\ \E checksum \in {1, 2, 3} :  \* Abstract checksum values
           LET msg == <<"input", sender, receiver, frame[sender], checksum>>
           IN /\ network' = network \union {msg}
              /\ checksums' = [checksums EXCEPT ![sender][frame[sender]] = checksum]
    /\ UNCHANGED <<connectionState, inputBuffer, frame, desynced, partitioned, flapCount, iceRestarting>>

\* Message delivery (non-deterministic: can deliver, lose, or duplicate)
\* This models unreliable DataChannel (ordered: false, maxRetransmits: 0)
DeliverMessage(msg) ==
    /\ msg \in network
    /\ IsConnected(msg[3])  \* Receiver must be connected
    /\ ~partitioned[msg[2]][msg[3]]  \* Not partitioned
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
    /\ UNCHANGED <<connectionState, frame, desynced, partitioned, flapCount, iceRestarting>>

\* Message loss (unreliable network)
LoseMessage(msg) ==
    /\ msg \in network
    /\ network' = network \ {msg}
    /\ UNCHANGED <<connectionState, inputBuffer, checksums, frame, desynced, partitioned, flapCount, iceRestarting>>

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
    /\ UNCHANGED <<connectionState, network, frame, desynced, partitioned, flapCount, iceRestarting>>

\* Implementation: tryAdvanceFrame() in LockstepNetcode.ts
AdvanceFrame(p) ==
    /\ IsConnected(p)
    /\ frame[p] < MaxFrame
    /\ HasAllInputs(p, frame[p])  \* All inputs received
    /\ ~desynced[p]                \* Not in desync state
    /\ frame' = [frame EXCEPT ![p] = frame[p] + 1]
    /\ UNCHANGED <<connectionState, network, inputBuffer, checksums, desynced, partitioned, flapCount, iceRestarting>>

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
    /\ UNCHANGED <<connectionState, network, inputBuffer, checksums, frame, partitioned, flapCount, iceRestarting>>

\* Implementation: State sync reception clears desync (see LockstepState.tla)
ClearDesync(p) ==
    /\ desynced[p]
    /\ desynced' = [desynced EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<connectionState, network, inputBuffer, checksums, frame, partitioned, flapCount, iceRestarting>>

----
\* ICE Restart (WebRTC NAT traversal recovery)
\*
\* Implementation: RTCPeerConnection.restartIce()
\* Triggered when:
\* - Connection state becomes "disconnected" or "failed"
\* - ICE connection check fails
\* - Network interface changes (e.g., WiFi -> cellular)

\* Start ICE restart process
\* Implementation: P2PManager detects connection issue, calls restartIce()
StartIceRestart(p) ==
    /\ IsConnected(p)
    /\ ~iceRestarting[p]
    /\ connectionState' = [connectionState EXCEPT ![p] = "ice_restarting"]
    /\ iceRestarting' = [iceRestarting EXCEPT ![p] = TRUE]
    \* Messages in flight may be lost during ICE restart
    /\ network' = {m \in network : m[2] # p /\ m[3] # p}
    /\ UNCHANGED <<inputBuffer, checksums, frame, desynced, partitioned, flapCount>>

\* ICE restart succeeds - connection re-established
\* Implementation: RTCPeerConnection.oniceconnectionstatechange -> "connected"
IceRestartSuccess(p) ==
    /\ connectionState[p] = "ice_restarting"
    /\ iceRestarting[p]
    /\ connectionState' = [connectionState EXCEPT ![p] = "connected"]
    /\ iceRestarting' = [iceRestarting EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<network, inputBuffer, checksums, frame, desynced, partitioned, flapCount>>

\* ICE restart fails - fall back to full reconnect
\* Implementation: RTCPeerConnection.oniceconnectionstatechange -> "failed"
IceRestartFailed(p) ==
    /\ connectionState[p] = "ice_restarting"
    /\ iceRestarting[p]
    /\ connectionState' = [connectionState EXCEPT ![p] = "disconnected"]
    /\ iceRestarting' = [iceRestarting EXCEPT ![p] = FALSE]
    /\ flapCount' = [flapCount EXCEPT ![p] = flapCount[p] + 1]
    /\ UNCHANGED <<network, inputBuffer, checksums, frame, desynced, partitioned>>

----
\* Network Partitions
\*
\* Models various partition scenarios:
\* - Symmetric: A and B cannot communicate (bidirectional)
\* - Asymmetric: A->B blocked but B->A works
\* - Partial: A<->B ok, B<->C ok, A<->C partitioned

\* Create asymmetric partition (one direction blocked)
\* Implementation: Network conditions, firewall, NAT issues
CreateAsymmetricPartition(from, to) ==
    /\ from # to
    /\ ~partitioned[from][to]  \* Not already partitioned
    /\ partitioned' = [partitioned EXCEPT ![from][to] = TRUE]
    \* Drop in-flight messages affected by partition
    /\ network' = {m \in network : ~(m[2] = from /\ m[3] = to)}
    /\ UNCHANGED <<connectionState, inputBuffer, checksums, frame, desynced, flapCount, iceRestarting>>

\* Create symmetric partition (both directions blocked)
\* Implementation: Complete network isolation between two peers
CreateSymmetricPartition(p1, p2) ==
    /\ p1 # p2
    /\ ~partitioned[p1][p2] \/ ~partitioned[p2][p1]  \* At least one direction not partitioned
    /\ partitioned' = [partitioned EXCEPT ![p1][p2] = TRUE, ![p2][p1] = TRUE]
    \* Drop all messages between these peers
    /\ network' = {m \in network :
         ~((m[2] = p1 /\ m[3] = p2) \/ (m[2] = p2 /\ m[3] = p1))}
    /\ UNCHANGED <<connectionState, inputBuffer, checksums, frame, desynced, flapCount, iceRestarting>>

\* Heal partition (restore connectivity)
\* Implementation: Network conditions improve, TURN fallback succeeds
HealPartition(from, to) ==
    /\ partitioned[from][to]
    /\ partitioned' = [partitioned EXCEPT ![from][to] = FALSE]
    /\ UNCHANGED <<connectionState, network, inputBuffer, checksums, frame, desynced, flapCount, iceRestarting>>

\* Heal all partitions (network fully recovers)
HealAllPartitions ==
    /\ \E p, q \in Peer : partitioned[p][q]  \* At least one partition exists
    /\ partitioned' = [p \in Peer |-> [q \in Peer |-> FALSE]]
    /\ UNCHANGED <<connectionState, network, inputBuffer, checksums, frame, desynced, flapCount, iceRestarting>>

----
\* Connection Flapping
\*
\* Models rapid connect/disconnect cycles that can destabilize the system.
\* Implementation: P2PManager tracks reconnection attempts and backs off.

\* Reset flap counter (connection stabilized)
\* Implementation: After sustained connection, reset backoff
ResetFlapCount(p) ==
    /\ IsConnected(p)
    /\ flapCount[p] > 0
    /\ flapCount' = [flapCount EXCEPT ![p] = 0]
    /\ UNCHANGED <<connectionState, network, inputBuffer, checksums, frame, desynced, partitioned, iceRestarting>>

\* Connection flap (immediate disconnect after connect)
\* Models unstable network conditions
ConnectionFlap(p) ==
    /\ connectionState[p] = "connected"
    /\ flapCount[p] < MaxFlaps  \* Still within tolerance
    /\ connectionState' = [connectionState EXCEPT ![p] = "disconnected"]
    /\ flapCount' = [flapCount EXCEPT ![p] = flapCount[p] + 1]
    /\ network' = {m \in network : m[2] # p /\ m[3] # p}
    /\ UNCHANGED <<inputBuffer, checksums, frame, desynced, partitioned, iceRestarting>>

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
    \* ICE restart
    \/ \E p \in Peer : StartIceRestart(p)
    \/ \E p \in Peer : IceRestartSuccess(p)
    \/ \E p \in Peer : IceRestartFailed(p)
    \* Network partitions
    \/ \E p, q \in Peer : CreateAsymmetricPartition(p, q)
    \/ \E p, q \in Peer : CreateSymmetricPartition(p, q)
    \/ \E p, q \in Peer : HealPartition(p, q)
    \/ HealAllPartitions
    \* Connection flapping
    \/ \E p \in Peer : ResetFlapCount(p)
    \/ \E p \in Peer : ConnectionFlap(p)

Fairness ==
    /\ WF_vars(\E p \in Peer : ConnectionEstablished(p))
    /\ WF_vars(\E m \in network : DeliverMessage(m))
    /\ WF_vars(\E p \in Peer : AdvanceFrame(p))
    /\ WF_vars(\E p \in Peer : ClearDesync(p))
    /\ WF_vars(\E p \in Peer : IceRestartSuccess(p))  \* ICE restart eventually resolves
    /\ WF_vars(\E p, q \in Peer : HealPartition(p, q))  \* Partitions eventually heal
    /\ WF_vars(\E p \in Peer : ResetFlapCount(p))  \* Flapping eventually stabilizes

Spec == Init /\ [][Next]_vars /\ Fairness

----
\* Safety Properties

\* Type invariant
TypeInvariant ==
    /\ \A p \in Peer : connectionState[p] \in {"disconnected", "connecting", "connected", "ice_restarting"}
    /\ \A p \in Peer : frame[p] >= 0 /\ frame[p] <= MaxFrame
    /\ \A p \in Peer : desynced[p] \in BOOLEAN
    /\ \A p \in Peer : iceRestarting[p] \in BOOLEAN
    /\ \A p \in Peer : flapCount[p] >= 0 /\ flapCount[p] <= MaxFlaps + 1
    /\ \A p, q \in Peer : partitioned[p][q] \in BOOLEAN
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

\* ICE restarting peer is not considered "connected" for message delivery
IceRestartingNotConnected ==
    \A p \in Peer : iceRestarting[p] => connectionState[p] = "ice_restarting"

\* Flapping peers eventually stop reconnecting (backoff works)
FlappingPeersBackedOff ==
    \A p \in Peer : flapCount[p] >= MaxFlaps =>
        connectionState[p] \in {"disconnected", "connected", "ice_restarting"}

\* Partitions are reflexively false (peer can always reach itself)
NoSelfPartition ==
    \A p \in Peer : ~partitioned[p][p]

----
\* Liveness Properties

\* If messages keep being delivered, frames eventually advance
EventualProgress ==
    (\A p \in ConnectedPeers : frame[p] < MaxFrame) ~>
    (\E p \in ConnectedPeers : frame[p] > 0)

\* Desync is eventually cleared (by state sync)
DesyncEventuallyCleared ==
    \A p \in Peer : desynced[p] ~> ~desynced[p]

\* ICE restart eventually completes (success or failure)
IceRestartEventuallyCompletes ==
    \A p \in Peer : iceRestarting[p] ~> ~iceRestarting[p]

\* Partitions eventually heal (network recovers)
PartitionsEventuallyHeal ==
    (\E p, q \in Peer : partitioned[p][q]) ~> (\A p, q \in Peer : ~partitioned[p][q])

----
\* State constraint for bounded model checking

StateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ \A p \in Peer : flapCount[p] <= MaxFlaps + 1
    /\ Cardinality(network) <= MaxMessages

===============================================================================
