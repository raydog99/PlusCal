------------------------------ MODULE DispersedLedger ------------------------------

EXTENDS Integers, TLC

\* Constants and variables
CONSTANT N \* Number of nodes
CONSTANT Value \* Set of possible values

VARIABLE state \* State of each node

\* Constants
InitState == [phase |-> "idle", x |-> NULL]

\* Init predicate
Init ==
    /\ state \in [1..N -> InitState]

\* Algorithm steps

\* Phase 1: Node proposes a value
Propose(p) ==
    /\ state[p].phase = "idle"
    /\ LET m == CHOOSE m \in Value : TRUE
       IN state' = [state EXCEPT ![p].x = m, ![p].phase = "prepare"]

\* Phase 2: DispersedLedger protocol steps for preparing and committing
DispersedLedgerAgree(p) ==
    /\ state[p].phase = "prepare"
    /\ LET v == CHOOSE v \in Value : \A q \in 1..N : state[q].phase = "prepare" => state[q].x = v
       IN state' = [state EXCEPT ![p].phase = "commit", ![p].x = v]

\* Next state relation
Next ==
    \E p \in 1..N :
        \/ Propose(p)
        \/ DispersedLedgerAgree(p)

\* Safety properties

\* Agreement: All nodes decide the same value
Agreement ==
    \A p, q \in 1..N : state[p].phase = "commit" /\ state[q].phase = "commit" => state[p].x = state[q].x

\* Liveness properties

\* Termination: All nodes eventually decide
Termination ==
    \A p \in 1..N : state[p].phase = "commit"

\* Combined specification
Spec == Init /\ [][Next]_state

\* Properties to check
Properties == Agreement /\ Termination

=============================================================================
