---- MODULE MCLockstepMessageLoss ----
\* Model-checking extensions for LockstepMessageLoss.tla

EXTENDS LockstepMessageLoss, TLC

MCStateConstraint ==
    /\ \A p \in Peer : frame[p] <= MaxFrame
    /\ Cardinality(network) <= MaxMessages

PeerSymmetry == Permutations(Peer)

====
