------------------------------- CONFIG EWD998 -------------------------------
CONSTANT N = 3
CONSTRAINTS StateConstraint
SPECIFICATION Spec
INVARIANT Inv TypeOK
PROPERTIES Liveness
VIEW View
CHECK_DEADLOCK FALSE
=============================================================================

------------------------------- MODULE EWD998 -------------------------------
(***************************************************************************)
(* TLA+ specification of an algorithm for distributed termination          *)
(* detection on a ring, due to Shmuel Safra, published as EWD 998:         *)
(* Shmuel Safra's version of termination detection.                        *)
(* https://www.cs.utexas.edu/users/EWD/ewd09xx/EWD998.PDF                  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Functions, Sequences, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0} \* At least one node.

Node == 0 .. N-1
Color == {"white", "black"}
Token == [pos : Node, q : Int, color : Color]

VARIABLES
 messages,
 active,     \* activation status of nodes
 color,      \* color of nodes
 counter,    \* nb of sent messages - nb of rcvd messages per node
 pending,    \* nb of messages in transit to node
 token       \* token structure

View == <<active, color, counter, pending, token>>
vars == <<active, color, counter, pending, token, messages>>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter \in [Node -> Int]
  /\ pending \in [Node -> Nat]
  /\ token \in Token
------------------------------------------------------------------------------

Init ==
  /\ messages = {}
  (* EWD840 but nodes *)
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  (* Rule 0 *)
  /\ counter = [i \in Node |-> 0] \* c properly initialized
  /\ pending = [i \in Node |-> 0]
  /\ token = [pos |-> 0, q |-> 0, color |-> "black"]

InitiateProbe ==
  (* Rules 1 + 5 + 6 *)
  /\ token.pos = 0
  /\ \* previous round not conclusive if:
     \/ token.color = "black"
     \/ color[0] = "black"
     \/ counter[0] + token.q > 0
  /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
  /\ color' = [ color EXCEPT ![0] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter, pending, messages>>

PassToken(i) ==
  (* Rules 2 + 4 + 7 *)
  /\ ~ active[i] \* If machine i is active, keep the token.
  /\ token.pos = i
  /\ token' = [token EXCEPT !.pos = @ - 1,
                            !.q = @ + counter[i],
                            !.color = IF color[i] = "black" THEN "black" ELSE @]
  /\ color' = [ color EXCEPT ![i] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter, pending, messages>>

System == \/ InitiateProbe
          \/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------

SendMsg(i) ==
  \* Only allowed to send msgs if node i is active.
  /\ active[i]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  \* Non-deterministically choose a receiver node.
  /\ \E j \in Node \ {i} :
          /\ pending' = [pending EXCEPT ![j] = @ + 1]
          /\ [from |-> i, dest |-> j] \notin messages
          /\ messages' = messages \union {[from |-> i, dest |-> j]}
          \* Note that we don't blacken node i as in EWD840 if node i
          \* sends a message to node j with j > i
  /\ UNCHANGED <<active, color, token>>

RecvMsg(m) ==
  LET i == m.dest
  IN
  /\ pending[i] > 0
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  (* Rule 3 *)
  /\ color' = [ color EXCEPT ![i] = "black" ]
  \* Receipt of a message activates i.
  /\ active' = [ active EXCEPT ![i] = TRUE ]

  /\ messages' = messages \ {m}
  /\ UNCHANGED <<token>>

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, counter, pending, token, messages>>

Environment ==
    \/ \E i \in Node : SendMsg(i) \/ Deactivate(i)
    \/ \E m \in messages: RecvMsg(m)

-----------------------------------------------------------------------------

Next ==
  System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

(***************************************************************************)
(* Bound the otherwise infinite state space that TLC has to check.         *)
(***************************************************************************)
StateConstraint ==
  /\ \A i \in Node : counter[i] <= 3 /\ pending[i] <= 3
  /\ token.q <= 9

-----------------------------------------------------------------------------

(***************************************************************************)
(* Main safety property: if there is a white token at node 0 and there are *)
(* no in-flight messages then every node is inactive.                      *)
(***************************************************************************)
terminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ token.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]
  /\ pending[0] = 0

(***************************************************************************)
(* The number of messages on their way. "in-flight"                        *)
(***************************************************************************)
B == FoldFunction(+, 0, pending)

(***************************************************************************)
(* The system has terminated if no node is active and there are no         *)
(* in-flight messages.                                                     *)
(***************************************************************************)
Termination ==
  /\ \A i \in Node : ~ active[i]
  /\ B = 0

TerminationDetection ==
  terminationDetected => Termination

(***************************************************************************)
(* Safra's inductive invariant                                             *)
(***************************************************************************)
Inv ==
  /\ P0:: B = FoldFunction(+, 0, counter)
     (* (Ai: t < i < N: machine nr.i is passive) /\ *)
     (* (Si: t < i < N: ci.i) = q *)
  /\ \/ P1:: /\ \A i \in (token.pos+1)..N-1: ~ active[i] \* machine nr.i is passive
             /\ IF token.pos = N-1
                THEN token.q = 0
                ELSE token.q = FoldFunctionOnSet(+, 0, counter, (token.pos+1..N-1))
     (* (Si: 0 <= i <= t: c.i) + q > 0. *)
     \/ P2:: FoldFunctionOnSet(+, 0, counter, 0..token.pos) + token.q > 0
     (* Ei: 0 <= i <= t : machine nr.i is black. *)
     \/ P3:: \E i \in 0..token.pos : color[i] = "black"
     (* The token is black. *)
     \/ P4:: token.color = "black"

(***************************************************************************)
(* Liveness property: termination is eventually detected.                  *)
(***************************************************************************)
Liveness ==
  Termination ~> terminationDetected

=============================================================================
