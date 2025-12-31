--------------------------------- MODULE LockstepNetcode ---------------------------------
\* P2P Lockstep Netcode with Leader Election
\*
\* Models a deterministic lockstep simulation where:
\* 1. All peers must submit input before any peer advances
\* 2. Each peer advances independently (deterministic simulation ensures sync)
\* 3. Leader election uses Raft-inspired consensus
\* 4. Leader sends heartbeats to maintain authority
\*
\* This model matches the TypeScript implementation in client/src/network/
\*
\* Properties verified:
\* - Election Safety: No two leaders in same term
\* - Lockstep Safety: Frames advance together (via input collection)
\* - Liveness: Leader eventually elected, frames eventually advance

EXTENDS Integers, FiniteSets

CONSTANT Peer
CONSTANT MaxFrame
CONSTANT MaxTerm

----
\* Variables

\* Current simulation frame for each peer
VARIABLE frame

\* Election term for each peer
VARIABLE currentTerm

\* Peer state: "Follower", "Candidate", "Leader"
VARIABLE state

\* Who this peer voted for in current term (0 = none)
VARIABLE votedFor

\* Votes received by each peer (set of voters)
VARIABLE votesReceived

\* Set of peers who have submitted input for current frame
\* (models InputBuffer.hasAllInputs check)
VARIABLE inputsReceived

\* Whether each peer has received a heartbeat this "round"
\* (models leader liveness detection)
VARIABLE heartbeatReceived

vars == <<frame, currentTerm, state, votedFor, votesReceived, inputsReceived, heartbeatReceived>>

----
\* Helpers

IsMajority(votes) == Cardinality(votes) * 2 > Cardinality(Peer)

MinPeer == CHOOSE p \in Peer : \A q \in Peer : p <= q

\* Minimum frame across all peers (for lockstep check)
MinFrame == CHOOSE f \in {frame[p] : p \in Peer} : \A q \in Peer : frame[q] >= f

----
\* Initial state

Init ==
    /\ frame = [p \in Peer |-> 0]
    /\ currentTerm = [p \in Peer |-> 0]
    /\ state = [p \in Peer |-> IF p = MinPeer THEN "Leader" ELSE "Follower"]
    /\ votedFor = [p \in Peer |-> 0]
    /\ votesReceived = [p \in Peer |-> {}]
    /\ inputsReceived = {}
    /\ heartbeatReceived = [p \in Peer |-> TRUE]  \* Start with heartbeat

----
\* Frame Advance Actions (matches LockstepNetcode.ts)

\* Peer submits input for current frame
\* Implementation: tick() -> inputBuffer.storeInput() -> broadcastInput()
\* Note: No leader required - inputs can be submitted anytime
SubmitInput(p) ==
    /\ p \notin inputsReceived
    /\ frame[p] = MinFrame                           \* Only submit for current frame
    /\ inputsReceived' = inputsReceived \union {p}
    /\ UNCHANGED <<frame, currentTerm, state, votedFor, votesReceived, heartbeatReceived>>

\* Peer advances frame when all inputs received
\* Implementation: tryAdvanceFrame() - each peer advances independently
\* Lockstep guarantee: deterministic simulation + same inputs = same state
AdvanceFrame(p) ==
    /\ inputsReceived = Peer                         \* All peers submitted (hasAllInputs)
    /\ frame[p] < MaxFrame                           \* Not at max frame
    /\ frame[p] = MinFrame                           \* Peer at minimum frame
    /\ frame' = [frame EXCEPT ![p] = frame[p] + 1]   \* This peer advances
    \* Reset inputs when ALL peers have advanced
    /\ inputsReceived' = IF \A q \in Peer : frame'[q] > MinFrame
                         THEN {}
                         ELSE inputsReceived
    /\ UNCHANGED <<currentTerm, state, votedFor, votesReceived, heartbeatReceived>>

----
\* Leader Heartbeat Actions (matches LeaderElection.ts)

\* Leader broadcasts heartbeat
\* Implementation: broadcastHeartbeat() every 500ms
BroadcastHeartbeat(leader) ==
    /\ state[leader] = "Leader"
    /\ heartbeatReceived' = [p \in Peer |-> TRUE]    \* All peers receive heartbeat
    /\ UNCHANGED <<frame, currentTerm, state, votedFor, votesReceived, inputsReceived>>

\* Reset heartbeat flag (models time passing without heartbeat)
\* Implementation: election timer checks timeSinceHeartbeat >= electionTimeout
ExpireHeartbeat(p) ==
    /\ heartbeatReceived[p] = TRUE
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<frame, currentTerm, state, votedFor, votesReceived, inputsReceived>>

----
\* Election Actions (matches LeaderElection.ts)

\* Follower starts election (timeout with no heartbeat)
\* Implementation: startElection()
StartElection(p) ==
    /\ state[p] = "Follower"
    /\ heartbeatReceived[p] = FALSE                  \* Heartbeat timed out
    /\ currentTerm[p] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![p] = currentTerm[p] + 1]
    /\ state' = [state EXCEPT ![p] = "Candidate"]
    /\ votedFor' = [votedFor EXCEPT ![p] = p]
    /\ votesReceived' = [votesReceived EXCEPT ![p] = {p}]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = TRUE]  \* Reset timer
    /\ UNCHANGED <<frame, inputsReceived>>

\* Vote for candidate (grant vote if valid)
\* Implementation: handleRequestVote()
Vote(voter, candidate) ==
    /\ state[candidate] = "Candidate"
    /\ voter # candidate
    /\ currentTerm[candidate] >= currentTerm[voter]
    /\ frame[candidate] >= frame[voter]              \* Log comparison: candidate at least as up-to-date
    /\ \/ votedFor[voter] = 0                        \* Haven't voted
       \/ currentTerm[candidate] > currentTerm[voter] \* Higher term resets
    /\ votedFor' = [votedFor EXCEPT ![voter] = candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![voter] = currentTerm[candidate]]
    /\ votesReceived' = [votesReceived EXCEPT ![candidate] = votesReceived[candidate] \union {voter}]
    /\ state' = [state EXCEPT ![voter] = "Follower"]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![voter] = TRUE]  \* Reset timer
    /\ UNCHANGED <<frame, inputsReceived>>

\* Candidate becomes leader with majority
\* Implementation: checkElectionResult() -> becomeLeader()
BecomeLeader(p) ==
    /\ state[p] = "Candidate"
    /\ IsMajority(votesReceived[p])
    /\ state' = [state EXCEPT ![p] = "Leader"]
    /\ UNCHANGED <<frame, currentTerm, votedFor, votesReceived, inputsReceived, heartbeatReceived>>

\* Leader steps down on seeing higher term
\* Implementation: stepDown()
Stepdown(p) ==
    /\ state[p] = "Leader"
    /\ \E q \in Peer : currentTerm[q] > currentTerm[p]
    /\ state' = [state EXCEPT ![p] = "Follower"]
    /\ heartbeatReceived' = [heartbeatReceived EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<frame, currentTerm, votedFor, votesReceived, inputsReceived>>

\* Candidate retries election (timeout)
\* Implementation: election timer fires -> startElection()
RetryElection(p) ==
    /\ state[p] = "Candidate"
    /\ currentTerm[p] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![p] = currentTerm[p] + 1]
    /\ votedFor' = [votedFor EXCEPT ![p] = p]
    /\ votesReceived' = [votesReceived EXCEPT ![p] = {p}]
    /\ UNCHANGED <<frame, state, inputsReceived, heartbeatReceived>>

----
\* State Machine

Next ==
    \* Frame advance (lockstep)
    \/ \E p \in Peer : SubmitInput(p)
    \/ \E p \in Peer : AdvanceFrame(p)
    \* Heartbeat (leader liveness)
    \/ \E p \in Peer : BroadcastHeartbeat(p)
    \/ \E p \in Peer : ExpireHeartbeat(p)
    \* Elections
    \/ \E p \in Peer : StartElection(p)
    \/ \E v, c \in Peer : Vote(v, c)
    \/ \E p \in Peer : BecomeLeader(p)
    \/ \E p \in Peer : Stepdown(p)
    \/ \E p \in Peer : RetryElection(p)

Fairness ==
    /\ WF_vars(\E p \in Peer : SubmitInput(p))
    /\ WF_vars(\E p \in Peer : AdvanceFrame(p))
    /\ WF_vars(\E p \in Peer : BroadcastHeartbeat(p))
    /\ WF_vars(\E p \in Peer : BecomeLeader(p))
    /\ WF_vars(\E p \in Peer : RetryElection(p))

Spec == Init /\ [][Next]_vars /\ Fairness

----
\* Safety Properties

\* No two leaders in the same term
\* Implementation guarantee: majority voting ensures uniqueness
NoTwoLeadersInSameTerm ==
    \A i, j \in Peer :
        (i # j /\ state[i] = "Leader" /\ state[j] = "Leader")
        => currentTerm[i] # currentTerm[j]

\* Frames stay within one of each other (lockstep with bounded drift)
\* Implementation: peers advance independently but same inputs = same timing
FrameBoundedDrift ==
    \A i, j \in Peer : frame[i] - frame[j] <= 1 /\ frame[j] - frame[i] <= 1

\* Frames are non-negative and bounded
TypeInvariant ==
    /\ \A p \in Peer : frame[p] >= 0 /\ frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] >= 0 /\ currentTerm[p] <= MaxTerm
    /\ inputsReceived \subseteq Peer
    /\ \A p \in Peer : state[p] \in {"Leader", "Follower", "Candidate"}

\* Leader is at least as up-to-date as any other peer
\* (consequence of log comparison in Vote action)
LeaderUpToDate ==
    \A leader, p \in Peer :
        state[leader] = "Leader" => frame[leader] >= frame[p] - 1

----
\* Liveness Properties

\* Eventually there is a leader
EventuallyLeader ==
    <>(\E p \in Peer : state[p] = "Leader")

\* Frames eventually advance (given fairness)
EventuallyProgress ==
    [](MinFrame < MaxFrame => <>(MinFrame > 0))

----
\* State constraint for finite model checking

StateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] <= MaxTerm

===============================================================================
