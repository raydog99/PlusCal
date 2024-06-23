------------------------------ MODULE Paxos ------------------------------

EXTENDS Integers, TLC

CONSTANT N \* Number of proposers and acceptors
CONSTANT Value \* Set of possible values

\* Variables
VARIABLE proposers, acceptors \* State of each proposer and acceptor

\* Constants
InitState == [ballotNum |-> 0, acceptedBallotNum |-> 0, acceptedValue |-> NULL]

\* Init predicate
Init ==
    /\ proposers \in [1..N -> InitState]
    /\ acceptors \in [1..N -> InitState]

\* Algorithm steps

\* Phase 1: Proposers prepare and send prepare requests
Prepare(p) ==
    /\ proposers[p].ballotNum = 0
    /\ LET ballotNum = CHOOSE n \in Nat : TRUE
       IN proposers' = [proposers EXCEPT ![p].ballotNum = ballotNum]

\* Phase 2: Acceptors respond to prepare requests and send accept requests
Accept(p) ==
    /\ acceptors[p].ballotNum = 0
    /\ LET ballotNum = proposers[p].ballotNum, value = proposers[p].acceptedValue
       IN acceptors' = [acceptors EXCEPT ![p].ballotNum = ballotNum, ![p].acceptedBallotNum = ballotNum, ![p].acceptedValue = value]

\* Next state relation
Next ==
    \E p \in 1..N :
        \/ Prepare(p)
        \/ Accept(p)

\* Safety properties

\* Agreement: All acceptors decide the same value
Agreement ==
    \A p, q \in 1..N : acceptors[p].acceptedBallotNum = acceptors[q].acceptedBallotNum => acceptors[p].acceptedValue = acceptors[q].acceptedValue

\* Liveness properties

\* Termination: All acceptors eventually decide
Termination ==
    \A p \in 1..N : acceptors[p].acceptedBallotNum > 0

\* Combined specification
Spec == Init /\ [][Next]_<<proposers, acceptors>>

\* Properties to check
Properties == Agreement /\ Termination

=============================================================================