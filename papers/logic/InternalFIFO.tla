---------------------- MODULE InternalFIFO ----------------------
EXTENDS Naturals, Sequences, TLAPS
CONSTANT Message
VARIABLES in, out, q
-----------------------------------------------------------------
NoMsg == CHOOSE x : x \notin Message

Init ==
  /\ q = << >>
  /\ in = NoMsg
  /\ out = NoMsg

Enq ==
  /\ in' \in Message \ {in}
  /\ q' = Append(q, in')
  /\ out' = out

Deq ==
  /\ q /= << >>
  /\ out' = Head(q)
  /\ q' = Tail(q)
  /\ in' = in

Next == Enq \/ Deq
vars == <<in, out, q>>
FifoI == Init /\ [][Next]_vars /\ WF_vars(Deq)
-----------------------------------------------------------------
TypeInvariant == q \in Seq(Message)

THEOREM FifoI => []TypeInvariant
<1>1. Init => TypeInvariant
   BY DEF Init, TypeInvariant
<1>2. TypeInvariant /\ [Next]_vars => TypeInvariant'
   BY DEF TypeInvariant, Next, Enq, Deq, vars
<1>3. QED
   BY PTL, <1>1, <1>2 DEF FifoI

Inv ==
  LET oq == << out >> \o q IN
    /\ in = oq[Len(oq)]
    /\ \A i \in 1..Len(oq)-1 : oq[i] /= oq[i+1]

THEOREM FifoI => []([Deq => out' /= out]_vars)
<1>1. Inv /\ Inv' /\ [Next]_vars => [Deq => out' /= out]_vars
   BY DEF Inv, Next, vars, Enq, Deq
<1>2. FifoI => []Inv
   <3>1. Init => Inv
      BY DEF Init, Inv
   <3>2. Inv /\ [Next]_vars => Inv'
      BY DEF Inv, Next, Enq, Deq, vars
   <3>3. QED
      BY PTL, <3>1, <3>2 DEF FifoI
<1>3. QED
   BY PTL, <1>1, <1>2 DEF FifoI

at(k,x) ==
  /\ k \in 1..Len(q)
  /\ q[k] = x
=================================================================
