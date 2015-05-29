---------------------- MODULE SimpleAllocator ----------------------
EXTENDS FiniteSet, TLAPS
CONSTANTS Clients, Resources
ASSUME IsFiniteSet(Resources)
VARIABLES
  unsat,   /* unsat[c] denotes the outstanding requests of client c */
  alloc    /* alloc[c] denotes the resources allocated to client c */
--------------------------------------------------------------------
TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]

available ==   /* set of resources free for allocation */
  Resources \ (UNION {alloc[c] : c \in Clients})
--------------------------------------------------------------------
Init == /* initially, no resources have been requested or allocated */
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]

Request(c,S) == /* Client c requests set S of resources */
  /\ S /= {} /\ unsat[c] = {} /\ alloc[c] = {}
  /\ unsat' = [unsat EXCEPT ![c]=S]
  /\ UNCHANGED alloc

Allocate(c,S) == /* Set of available resources are allocated to client c */
  /\ S /= {} /\ S \subseteq avaiable \intersect unsat[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \union S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

Return(c, S) == /* Client c returns a set of resources that it holds. */
  /\ S /= {} /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED unsat

Next == /* The system's next-state relation */
  \E c \in Clients, S \in SUBSET Resources :
    Request(c,S) \/ Allocate(c,S) \/ Return(c,S)

vars == <<unsat, alloc>>
--------------------------------------------------------------------
SimpleAllocator == /* The complete high−level specification */
  /\ Init /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(Return(c, alloc[c]))
  /\ \A c \in Clients : SF_vars(\E S \in SUBSET Resources : Allocate(c,S))
--------------------------------------------------------------------
Safety == \A c_1, c_2 \in Clients : c_1 /= c_2 => alloc[c_1] \intersect alloc[c_2] = {}
Liveness == \A c \in Clients, r \in Resources : r \in unsat[c] ~> r \in alloc[c]
--------------------------------------------------------------------
THEOREM SimpleAllocator => []TypeInvariant
THEOREM SimpleAllocator => []Safety
THEOREM SimpleAllocator => Liveness
====================================================================
