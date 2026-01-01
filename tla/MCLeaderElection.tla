---- MODULE MCLeaderElection ----
\* Model-checking extensions for LeaderElection.tla

EXTENDS LeaderElection, TLC

MCStateConstraint ==
    /\ \A p \in Peer : currentTerm[p] <= MaxTerm
    /\ \A p \in Peer : frame[p] <= MaxFrame

PeerSymmetry == Permutations(Peer)

====
