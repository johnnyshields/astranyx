---- MODULE MCLockstepState ----
\* Model-checking extensions for LockstepState.tla

EXTENDS LockstepState, TLC

MCStateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ \A p \in Peer : currentTerm[p] <= MaxTerm
    /\ \A p \in Peer : Cardinality(pendingEvents[p]) <= MaxEvents

PeerSymmetry == Permutations(Peer)

====
