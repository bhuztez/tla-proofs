-------------------------- MODULE Channel -----------------------------
EXTENDS Naturals, TLAPS
CONSTANT Data
VARIABLE chan 

TypeInvariant  ==  chan \in [val : Data,  rdy : {0, 1},  ack : {0, 1}]
-----------------------------------------------------------------------
Init  ==  /\ TypeInvariant
          /\ chan.ack = chan.rdy 

Send(d) ==  /\ chan.rdy = chan.ack
            /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Rcv     ==  /\ chan.rdy /= chan.ack
            /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next  ==  (\E d \in Data : Send(d)) \/ Rcv

Spec  ==  Init /\ [][Next]_chan
-----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
<1>1. Init => TypeInvariant
   BY DEF Init, TypeInvariant
<1>2. TypeInvariant /\ [Next]_chan => TypeInvariant'
   <2>1. TypeInvariant /\ Rcv => TypeInvariant'
      BY DEF TypeInvariant, Rcv
   <2>2. ASSUME NEW d \in Data PROVE TypeInvariant /\ Send(d) => TypeInvariant'
      BY DEF TypeInvariant, Send
   <2>3. QED
      BY <2>1, <2>2 DEF TypeInvariant, Next
<1>3. QED
   BY PTL, <1>1, <1>2 DEF Spec
=======================================================================
