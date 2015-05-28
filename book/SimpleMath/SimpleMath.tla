----------------------------- MODULE SimpleMath -----------------------------
EXTENDS TLAPS
CONSTANTS a, b, c, d, e, f, g
-----------------------------------------------------------------------------
THEOREM \A F, G \in {TRUE, FALSE} : (F => G) <=> ~F \/ G
<1> QED
    OBVIOUS

THEOREM ~ \A F, G \in {TRUE, FALSE} : (F \/ G) => (F /\ G)
<1> QED
    OBVIOUS

THEOREM {1, 2, 2, 3, 3, 3} = {3, 1, 1, 2}
<1> QED
    OBVIOUS

THEOREM {1, 2} \cup {2, 3, 4} = {5, 4, 3, 2, 1} \cap {1, 2, 3, 4}
<1> QED
    OBVIOUS

THEOREM {1, 3} \subseteq {3, 2, 1}
<1> QED
    OBVIOUS

THEOREM {a, b, c} \ {c} = {a, b}
<1> QED
    OBVIOUS

THEOREM {a, b} \in {{a, b}, c, {d, e}}
<1> QED
    OBVIOUS


SomeSets == SUBSET {a, b, c, d, e}

THEOREM \A S, T \in SomeSets : (S \subseteq T) <=> S = (S \cap T)
<1> QED
    OBVIOUS
=============================================================================
