---------------------- MODULE HourClock ----------------------
EXTENDS Naturals, TLAPS

VARIABLE hr
HCini == hr \in (1 .. 12)
HCnxt == hr' = IF hr /= 12 THEN hr + 1 ELSE 1
HC == HCini /\ [][HCnxt]_hr
--------------------------------------------------------------
THEOREM HC => []HCini
<1>1. HCini /\ [HCnxt]_hr => HCini'
   BY DEF HCini, HCnxt
<1>2. QED
   BY PTL, <1>1 DEF HC
==============================================================
