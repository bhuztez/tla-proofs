------------------ MODULE AsynchInterface ---------------------
EXTENDS Naturals, TLAPS

CONSTANT  Data
VARIABLES val, rdy, ack

TypeInvariant == /\ val \in Data
                 /\ rdy \in {0, 1}
                 /\ ack \in {0, 1}
---------------------------------------------------------------
Init == /\ val \in Data
        /\ rdy \in {0, 1}
        /\ ack = rdy

Send == /\ rdy = ack
        /\ val' \in Data
        /\ rdy' = 1 - rdy
        /\ UNCHANGED ack

Rcv  == /\ rdy /= ack
        /\ ack' = 1 - ack
        /\ UNCHANGED <<val, rdy>>

Next == Send \/ Rcv

Spec == Init /\ [][Next]_<<val, rdy, ack>>
---------------------------------------------------------------
THEOREM Spec => []TypeInvariant
<1>1. Init => TypeInvariant
   BY DEF Init, TypeInvariant
<1>2. TypeInvariant /\ [Next]_<<val, rdy, ack>> => TypeInvariant'
   BY DEF TypeInvariant, Next, Send, Rcv
<1>3. QED
   BY PTL, <1>1, <1>2 DEF Spec
===============================================================
