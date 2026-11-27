------------------------------- MODULE Override --------------------------------
\* A .cfg wrapper that replaces pure operators (`Ok <- Bound`, a parameterized
\* `B <- Le`) and a builtin (`Nat <- SmallNat`). The certified lowering runs the
\* configured replacement bodies, not the shadowed ones, and the emitted
\* certificate carries one override obligation per applied use site.
EXTENDS Naturals
CONSTANT Proc
CONSTANT B(_, _)
Le(a, b) == a <= b
Ok(v) == v < 2
Bound(v) == v <= 2
SmallNat == 0 .. 3
VARIABLES pc, tag
Init == /\ pc = [p \in Proc |-> 0]
        /\ tag = 0
Step == \E p \in Proc :
          /\ Ok(pc[p])
          /\ B(pc[p], 2)
          /\ pc[p] \in Nat
          /\ pc' = [pc EXCEPT ![p] = @ + 1]
          /\ tag' = tag
Next == Step
Inv == \A p \in Proc : pc[p] \in 0 .. 3
===============================================================================
