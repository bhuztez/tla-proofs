---------------------- MODULE HourClock2 ----------------------
EXTENDS HourClock

HCnxt2  ==  hr' = (hr % 12) + 1
HC2  ==  HCini /\ [][HCnxt2]_hr
---------------------------------------------------------------
THEOREM HC <=> HC2
<1>1. HC <=> [](HCini /\ [HCnxt]_hr)
   <2>1. HCini /\ [HCnxt]_hr => HCini'
      BY DEF HCini, HCnxt
   <2>2. QED
      BY PTL, <2>1 DEF HC
<1>2. HC2 <=> [](HCini /\ [HCnxt2]_hr)
   <3>1. HCini /\ [HCnxt2]_hr => HCini'
      BY Z3 DEF HCini, HCnxt2
   <3>2. QED
      BY PTL, <3>1 DEF HC2
<1>3. ([](HCini /\ [HCnxt]_hr)) <=> ([](HCini /\ [HCnxt2]_hr))
   <4>1. (HCini /\ HCnxt) <=> (HCini /\ HCnxt2)
      BY Z3 DEF HCini, HCnxt, HCnxt2
   <4>2. QED
      BY PTL, <4>1
<1>4. QED
   BY PTL, <1>1, <1>2, <1>3
===============================================================
