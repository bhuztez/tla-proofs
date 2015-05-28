---------------------------- MODULE InnerFIFO -------------------------------
EXTENDS Naturals, Sequences, TLAPS
CONSTANT Message
VARIABLES in, out, q
InChan  == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out
-----------------------------------------------------------------------------
Init == /\ InChan!Init
        /\ OutChan!Init
        /\ q = << >>

TypeInvariant  ==  /\ InChan!TypeInvariant
                   /\ OutChan!TypeInvariant
                   /\ q \in Seq(Message)

SSend(msg)  ==  /\ InChan!Send(msg) \* Send msg on channel `in'.
                /\ UNCHANGED <<out, q>>

BufRcv == /\ InChan!Rcv              \* Receive message from channel `in'.
          /\ q' = Append(q, in.val)  \*   and append it to tail of q.
          /\ UNCHANGED out

BufSend == /\ q /= << >>              \* Enabled only if q is nonempty.
           /\ OutChan!Send(Head(q))   \* Send Head(q) on channel `out'
           /\ q' = Tail(q)            \*   and remove it from q.
           /\ UNCHANGED in

RRcv == /\ OutChan!Rcv          \* Receive message from channel `out'.
        /\ UNCHANGED <<in, q>>

Next == \/ \E msg \in Message : SSend(msg)
        \/ BufRcv
        \/ BufSend
        \/ RRcv 

Spec == Init /\ [][Next]_<<in, out, q>>
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
<1>1. Init => TypeInvariant
   BY DEF Init, TypeInvariant, InChan!Init, InChan!TypeInvariant, OutChan!Init, OutChan!TypeInvariant
<1>2. TypeInvariant /\ [Next]_<<in, out, q>> => TypeInvariant'
   <2>1. ASSUME NEW msg \in Message PROVE TypeInvariant /\ SSend(msg) => TypeInvariant'
      BY DEF SSend, InChan!Send, TypeInvariant, InChan!TypeInvariant, OutChan!TypeInvariant
   <2>2. TypeInvariant /\ BufRcv => TypeInvariant'
      BY DEF BufRcv, InChan!Rcv, TypeInvariant, InChan!TypeInvariant, OutChan!TypeInvariant
   <2>3. TypeInvariant /\ BufSend => TypeInvariant'
      BY DEF BufSend, OutChan!Send, TypeInvariant, InChan!TypeInvariant, OutChan!TypeInvariant
   <2>4. TypeInvariant /\ RRcv => TypeInvariant'
      BY DEF RRcv, OutChan!Rcv, TypeInvariant, InChan!TypeInvariant, OutChan!TypeInvariant
   <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF Next, TypeInvariant, InChan!TypeInvariant, OutChan!TypeInvariant
<1>3. QED
   BY PTL, <1>1, <1>2 DEF Spec
=============================================================================
