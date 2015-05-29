------------------------------- MODULE Paxos -------------------------------
(***************************************************************************)
(* This is a TLA+ specification of the Paxos Consensus algorithm,          *)
(* described in                                                            *)
(*                                                                         *)
(*  Paxos Made Simple:                                                     *)
(*   http://research.microsoft.com/en-us/um/people/lamport/pubs/pubs.html#paxos-simple *)
(*                                                                         *)
(* and a TLAPS-checked proof of its correctness.  This was mostly done as  *)
(* a test to see how the SMT backend of TLAPS is now working.              *)
(***************************************************************************)
EXTENDS Integers, TLAPS

CONSTANTS Acceptors, Values, Quorums

ASSUME QuorumAssumption == 
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}                 

(***************************************************************************)
(* The following lemma is an immediate consequence of the assumption.      *)
(***************************************************************************)
LEMMA QuorumNonEmpty == \A Q \in Quorums : Q # {}
BY QuorumAssumption

Ballots == Nat

VARIABLES msgs,    \* The set of messages that have been sent.
          maxBal,  \* maxBal[a] is the highest-number ballot acceptor a
                   \*   has participated in.
          maxVBal, \* maxVBal[a] is the highest ballot in which a has
          maxVal   \*   voted, and maxVal[a] is the value it voted for
                   \*   in that ballot.

vars == <<msgs, maxBal, maxVBal, maxVal>>

Send(m) == msgs' = msgs \cup {m}

None == CHOOSE v : v \notin Values

Init == /\ msgs = {}
        /\ maxVBal = [a \in Acceptors |-> -1]
        /\ maxBal  = [a \in Acceptors |-> -1]
        /\ maxVal  = [a \in Acceptors |-> None]
(***************************************************************************)
(* Phase 1a: A leader selects a ballot number b and sends a 1a message     *)
(* with ballot b to a majority of acceptors.  It can do this only if it    *)
(* has not already sent a 1a message for ballot b.                         *)
(***************************************************************************)
Phase1a(b) == /\ ~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b)
              /\ Send([type |-> "1a", bal |-> b])
              /\ UNCHANGED <<maxVBal, maxBal, maxVal>>
(***************************************************************************)
(* Phase 1b: If an acceptor receives a 1a message with ballot b greater    *)
(* than that of any 1a message to which it has already responded, then it  *)
(* responds to the request with a promise not to accept any more proposals *)
(* for ballots numbered less than b and with the highest-numbered ballot   *)
(* (if any) for which it has voted for a value and the value it voted for  *)
(* in that ballot.  That promise is made in a 1b message.                  *)
(***************************************************************************)
Phase1b(a) == 
  /\ \E m \in msgs : 
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ Send([type |-> "1b", bal |-> m.bal, maxVBal |-> maxVBal[a], 
                  maxVal |-> maxVal[a], acc |-> a])
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
  /\ UNCHANGED <<maxVBal, maxVal>>
(***************************************************************************)
(* Phase 2a: If the leader receives a response to its 1b message (for      *)
(* ballot b) from a quorum of acceptors, then it sends a 2a message to all *)
(* acceptors for a proposal in ballot b with a value v, where v is the     *)
(* value of the highest-numbered proposal among the responses, or is any   *)
(* value if the responses reported no proposals.  The leader can send only *)
(* one 2a message for any ballot.                                          *)
(***************************************************************************)
Phase2a(b) ==
  /\ ~ \E m \in msgs : (m.type = "2a") /\ (m.bal = b) 
  /\ \E v \in Values :
       /\ \E Q \in Quorums :
            \E S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)} :
               /\ \A a \in Q : \E m \in S : m.acc = a
               /\ \/ \A m \in S : m.maxVBal = -1
                  \/ \E c \in 0..(b-1) : 
                        /\ \A m \in S : m.maxVBal =< c
                        /\ \E m \in S : /\ m.maxVBal = c
                                        /\ m.maxVal = v
       /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>
(***************************************************************************)
(* Phase 2b: If an acceptor receives a 2a message for a ballot numbered    *)
(* b, it votes for the message's value in ballot b unless it has already   *)
(* responded to a 1a request for a ballot number greater than or equal to  *)
(* b.                                                                      *)
(***************************************************************************)
Phase2b(a) == 
  \E m \in msgs :
    /\ m.type = "2a" 
    /\ m.bal >= maxBal[a]
    /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ maxVal' = [maxVal EXCEPT ![a] = m.val]

Next == \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a) 

Spec == Init /\ [][Next]_vars       
-----------------------------------------------------------------------------
(***************************************************************************)
(* How a value is chosen:                                                  *)
(*                                                                         *)
(* This spec does not contain any actions in which a value is explicitly   *)
(* chosen (or a chosen value learned).  Wnat it means for a value to be    *)
(* chosen is defined by the operator Chosen, where Chosen(v) means that v  *)
(* has been chosen.  From this definition, it is obvious how a process     *)
(* learns that a value has been chosen from messages of type "2b".         *)
(***************************************************************************)
VotedForIn(a, v, b) == \E m \in msgs : /\ m.type = "2b"
                                       /\ m.val  = v
                                       /\ m.bal  = b
                                       /\ m.acc  = a

ChosenIn(v, b) == \E Q \in Quorums :
                     \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)
(***************************************************************************)
(* The consistency condition that a consensus algorithm must satisfy is    *)
(* the invariance of the following state predicate Consistency.            *)
(***************************************************************************)
Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => (v1 = v2)
-----------------------------------------------------------------------------
(***************************************************************************)
(* This section of the spec defines the invariant Inv.                     *)
(***************************************************************************)
Messages ==      [type : {"1a"}, bal : Ballots]
            \cup [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                    maxVal : Values \cup {None}, acc : Acceptors]
            \cup [type : {"2a"}, bal : Ballots, val : Values]
            \cup [type : {"2b"}, bal : Ballots, val : Values, acc : Acceptors]
        

TypeOK == /\ msgs \in SUBSET Messages
          /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
          /\ maxBal \in  [Acceptors -> Ballots \cup {-1}]
          /\ maxVal \in  [Acceptors -> Values \cup {None}]
          /\ \A a \in Acceptors : maxBal[a] >= maxVBal[a]
(***************************************************************************)
(* WontVoteIn(a, b) is a predicate that implies that a has not voted and   *)
(* never will vote in ballot b.                                            *)
(***************************************************************************)                                       
WontVoteIn(a, b) == /\ \A v \in Values : ~ VotedForIn(a, v, b)
                    /\ maxBal[a] > b
(***************************************************************************)
(* The predicate SafeAt(v, b) implies that no value other than perhaps v   *)
(* has been or ever will be chosen in any ballot numbered less than b.     *)
(***************************************************************************)                   
SafeAt(v, b) == 
  \A c \in 0..(b-1) :
    \E Q \in Quorums : 
      \A a \in Q : VotedForIn(a, v, c) \/ WontVoteIn(a, c)

MsgInv ==
  \A m \in msgs : 
    /\ (m.type = "1b") => /\ m.bal =< maxBal[m.acc]
                          /\ \/ /\ m.maxVal \in Values
                                /\ m.maxVBal \in Ballots
                                /\ SafeAt(m.maxVal, m.maxVBal)
                             \/ /\ m.maxVal = None
                                /\ m.maxVBal = -1
    /\ (m.type = "2a") => 
         /\ SafeAt(m.val, m.bal)
         /\ \A ma \in msgs : (ma.type = "2a") /\ (ma.bal = m.bal)
                                => (ma = m)
    /\ (m.type = "2b") => 
         /\ \E ma \in msgs : /\ ma.type = "2a"
                             /\ ma.bal  = m.bal
                             /\ ma.val  = m.val
         /\ m.bal =< maxVBal[m.acc]
(***************************************************************************)
(* The following two lemmas are simple consequences of the definitions.    *)
(***************************************************************************)
LEMMA VotedInv == 
        MsgInv /\ TypeOK => 
            \A a \in Acceptors, v \in Values, b \in Ballots :
                VotedForIn(a, v, b) => SafeAt(v, b) /\ b =< maxVBal[a]
  BY DEF VotedForIn, WontVoteIn, MsgInv, Messages, TypeOK


LEMMA VotedOnce == 
        MsgInv =>  \A a \in Acceptors, b \in Ballots, v1, v2 \in Values :
                       VotedForIn(a, v1, b) /\ VotedForIn(a, v2, b) => (v1 = v2)
BY DEF MsgInv, VotedForIn

AccInv ==
  \A a \in Acceptors:
    /\ (maxVal[a] = None) <=> (maxVBal[a] = -1)
    /\ maxVBal[a] =< maxBal[a]
    /\ (maxVBal[a] >= 0) => SafeAt(maxVal[a], maxVBal[a])  
(***************************************************************************)
(* Inv is the complete inductive invariant.                                *)
(***************************************************************************)
Inv == TypeOK /\ MsgInv /\ AccInv
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma shows that (the invariant implies that) the         *)
(* predicate SafeAt(v, b) is stable, meaning that once it becomes true, it *)
(* remains true throughout the rest of the excecution.                     *)
(***************************************************************************)

LEMMA SafeAtStable ==
  Inv /\ Next /\ TypeOK' =>
    \A v \in Values, b \in Ballots: SafeAt(v, b) => SafeAt(v, b)'
<1> SUFFICES ASSUME NEW v \in Values, NEW b \in Ballots,
                    Inv, TypeOK', SafeAt(v, b)
             PROVE Next => SafeAt(v, b)'
   OBVIOUS
<1> USE DEF Send, Inv, MsgInv, AccInv, Ballots
<1> USE TRUE /\ TRUE
<1>1. ASSUME NEW bb \in Ballots, Phase1a(bb)
      PROVE SafeAt(v, b)'
   BY Z3, <1>1 DEF Phase1a, SafeAt, VotedForIn, WontVoteIn
<1>2. ASSUME NEW a \in Acceptors, Phase1b(a)
      PROVE SafeAt(v, b)'
   BY Z3, <1>2, QuorumAssumption DEF Phase1b, TypeOK, SafeAt, WontVoteIn, VotedForIn, None
<1>3. ASSUME NEW bb \in Ballots, Phase2a(bb)
      PROVE SafeAt(v, b)'
   OMITTED
<1>4. ASSUME NEW a \in Acceptors, Phase2b(a)
      PROVE SafeAt(v, b)'
   <2>1. PICK m \in msgs : Phase2b(a)!(m)
      BY <1>4 DEF Phase2b
   <2>2. \A aa \in Acceptors, bb \in Ballots, vv \in Values :
        VotedForIn(aa, vv, bb) => VotedForIn(aa, vv, bb)'
      BY <2>1 DEF TypeOK, VotedForIn
   <2>3. \A aa \in Acceptors, bb \in Ballots : maxBal[aa] > bb => maxBal'[aa] > bb
      BY <2>1 DEF TypeOK
   <2>4. ASSUME NEW aa \in Acceptors, NEW bb \in Ballots,
                WontVoteIn(aa, bb), NEW vv \in Values,
                VotedForIn(aa, vv, bb)'
         PROVE FALSE
      <3>1. ~ VotedForIn(aa, vv, bb)
         BY <2>4 DEF WontVoteIn
      <3> DEFINE mm == [type |-> "2b", val |-> vv, bal |-> bb, acc |-> aa]
      <3>2. mm \notin msgs
         BY <3>1 DEF VotedForIn
      <3>3. mm \in msgs'
         <4>1. ASSUME NEW m1 \in Messages,
                      /\ m1 . type  =  "2b"
                      /\ m1 . val  =  vv
                      /\ m1 . bal  =  bb
                      /\ m1 . acc  =  aa
               PROVE  m1 = [type |-> "2b", val |-> vv, bal |-> bb, acc |-> aa]
            <5>1. m1 \in [type : {"2b"}, bal : Nat, val : Values, acc : Acceptors]
               BY <4>1 DEF Messages
            <5>2. m1 =  [type |-> "2b", val |-> m1.val, bal |-> m1.bal, acc |-> m1.acc]
               <6>1. PICK xt \in {"2b"}, xb \in Nat, xv \in Values, xa \in Acceptors : m1 = [type |-> xt, val |->xv, bal |-> xb, acc |-> xa]
                  BY <5>1
               <6>2. QED
                  BY <6>1
            <5>3. QED
               BY <4>1, <5>2
         <4>2. QED
            OMITTED
      <3>4. mm = [type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a]
         BY <2>1, <3>2, <3>3 DEF Phase2b, TypeOK
      <3>5. aa = a /\ m.bal = bb
         BY <3>4
      <3>6. QED
         BY <2>1, <2>4, <3>5 DEF Phase2b, WontVoteIn, TypeOK
   <2>5. \A aa \in Acceptors, bb \in Ballots : WontVoteIn(aa, bb) => WontVoteIn(aa, bb)'
      BY <2>3, <2>4 DEF WontVoteIn
   <2>6. QED
      BY <2>2, <2>5, QuorumAssumption DEF SafeAt
<1>5. QED
   BY <1>1, <1>2, <1>3, <1>4 DEF Next


THEOREM Invariant == Spec => []Inv
<1> USE DEF Ballots
<1>1. Init => Inv
   BY Z3 DEF Init, Inv, TypeOK, AccInv, MsgInv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, Next
               PROVE  Inv'
    <3> Inv /\ UNCHANGED vars => Inv'
       BY SMTT(10) DEF vars, Inv, TypeOK, MsgInv, AccInv, SafeAt, VotedForIn, WontVoteIn
    <3> QED
       OBVIOUS
  <2> USE DEF Inv
  <2>1. TypeOK'
    PROOF OMITTED
  <2>2. AccInv'
    PROOF OMITTED
  <2>3. MsgInv'
    <3> SUFFICES ASSUME NEW m \in msgs'
                 PROVE  MsgInv!(m)'
      BY DEF MsgInv
    <3> USE DEF Send, Inv
    <3>1. ASSUME NEW b \in Ballots, Phase1a(b)
          PROVE  MsgInv!(m)'
      PROOF OMITTED  
    <3>2. ASSUME NEW a \in Acceptors, Phase1b(a)
          PROVE  MsgInv!(m)'
      PROOF OMITTED
    <3>3. ASSUME NEW b \in Ballots, Phase2a(b)
          PROVE  MsgInv!(m)'
      PROOF OMITTED
    <3>4. ASSUME NEW a \in Acceptors, Phase2b(a)
          PROVE  MsgInv!(m)'
      PROOF OMITTED
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4, SMT DEF Next
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Inv
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

    
THEOREM Consistent == Spec => []Consistency
<1> USE DEF Ballots
<1>1. Inv => Consistency
  <2> SUFFICES ASSUME Inv,  
                      NEW v1 \in Values,  NEW v2 \in Values, 
                      NEW b1 \in Ballots, NEW b2 \in Ballots,
                      ChosenIn(v1, b1), ChosenIn(v2, b2),
                      b1 =< b2
               PROVE  v1 = v2
    BY Z3 DEF Consistency, Chosen
  <2>1. CASE b1 = b2
    BY <2>1, QuorumAssumption, VotedOnce, Z3 DEF ChosenIn, Inv
  <2>2. CASE b1 < b2
    <3>1. SafeAt(v2, b2)
      BY VotedInv, QuorumNonEmpty, QuorumAssumption, Z3 DEF ChosenIn, Inv
    <3>2. PICK Q2 \in Quorums : 
                  \A a \in Q2 : VotedForIn(a, v2, b1) \/ WontVoteIn(a, b1)
      BY <3>1, <2>2, Z3 DEF SafeAt
    <3>3. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1)
      BY DEF ChosenIn
    <3>4. QED
      BY <3>2, <3>3, QuorumAssumption, VotedOnce, Z3 DEF WontVoteIn, Inv
  <2>3. QED
    BY <2>1, <2>2, Z3
<1>2. QED
  BY Invariant, <1>1, PTL
-----------------------------------------------------------------------------
chosenBar == {v \in Values : Chosen(v)}

C == INSTANCE Consensus WITH chosen <- chosenBar
(***************************************************************************)
(* The following theorem asserts that this specification of Paxos refines  *)
(* the trivial specification of consensus in module Consensus.             *)
(***************************************************************************)
THEOREM Refinement == Spec => C!Spec
<1>1. Init => C!Init
  BY QuorumNonEmpty, Z3 DEF Init, C!Init, chosenBar, Chosen, ChosenIn, VotedForIn
<1>2. TypeOK' /\ Consistency' /\ [Next]_vars => [C!Next]_chosenBar
  <2> SUFFICES ASSUME TypeOK', Consistency', Next, chosenBar' # chosenBar
               PROVE  C!Next
    <3>1. UNCHANGED vars => UNCHANGED chosenBar
      BY Z3 DEF vars, chosenBar, Chosen, ChosenIn, VotedForIn
    <3>2. QED
      BY <3>1, Z3
  <2>1. chosenBar \subseteq chosenBar'
    BY Z3 DEF Send, chosenBar, Chosen, ChosenIn, VotedForIn, Next, Phase1a, Phase1b, Phase2a, Phase2b
  <2>2. \A v, w \in chosenBar': v = w
    BY Z3 DEF Consistency, chosenBar, ChosenIn, TypeOK
  <2>3. chosenBar = {}
    BY <2>1, <2>2, SetExtensionality, Z3
  <2>4. \E v \in Values : chosenBar' = {v}
    BY <2>1, <2>2, <2>3, Z3 DEF chosenBar
  <2>5. QED
    BY <2>3, <2>4 DEF C!Next
<1>3. QED
  BY <1>1, <1>2, Invariant, Consistent, PTL DEF Spec, C!Spec, Inv

-----------------------------------------------------------------------------
(***************************************************************************)
(* It took about 10 hours to write the invariance proofs, a few of those   *)
(* hours (perhaps 3) were due to my original invariant not being the       *)
(* correct one--that is, it was an invariant but not an inductive          *)
(* invariant.                                                              *)
(*                                                                         *)
(* The refinement proof took about 1-1/2 hours.  It took that long because *)
(* I started writing a more complicated proof and then realized how easy   *)
(* it was to prove.  By some sort of editing error, I lost my original     *)
(* refinement proof.  I recreated it from scratch in 1/2 hour.             *)
(*                                                                         *)
(* The proofs total about 180 lines.  A fix to the SMT backend removed     *)
(* about 50 lines from the proof when running with Z3.  Had I started the  *)
(* proof with the current version of the SMT backend, it probably would    *)
(* have saved me a couple of hours.                                        *)
(***************************************************************************)
=============================================================================
\* Modification History
\* Last modified Tue Mar 18 11:37:57 CET 2014 by doligez
\* Last modified Sat Nov 24 18:54:35 GMT-03:00 2012 by merz
\* Last modified Sat Nov 24 18:53:09 GMT-03:00 2012 by merz
\* Last modified Fri Nov 23 09:22:09 PST 2012 by lamport
\* Created Sat Nov 17 16:02:06 PST 2012 by lamport
