---- MODULE InstPassOpReexport ----
\* Passing a qualified operator inherited from a declaration-free extended module
\* through a parameterized INSTANCE preserves the full public signature (prefix
\* parameters followed by the inherited definition's own parameters).
EXTENDS Naturals

---- MODULE Source ----
EXTENDS InstPassOpCommon
CONSTANT k
Read == (HERE::k) + 1
====

---- MODULE Leaf ----
CONSTANT m
Get == m
====

---- MODULE PureMid ----
Inner(q) == INSTANCE Leaf WITH m <- q
====

---- MODULE Use3 ----
CONSTANT F(_, _, _)
Val == F(0, 1, 2)
====

---- MODULE Use2 ----
CONSTANT F(_, _)
Val == F(10, 3)
====

---- MODULE Use1 ----
CONSTANT F(_)
Val == F(3)
====

S(n) == INSTANCE Source WITH k <- n
Outer(p) == INSTANCE PureMid
I3(G(_, _, _)) == INSTANCE Use3 WITH F <- G
I2(G(_, _)) == INSTANCE Use2 WITH F <- G
I1(G(_)) == INSTANCE Use1 WITH F <- G

VARIABLE x
Init == x = 0
Next == UNCHANGED x
Inv == /\ I3(S!Pair)!Val = <<1, 2>>
       /\ I2(S!Twice)!Val = 6
       /\ I2(Outer!Inner!Get)!Val = 3
       /\ I1(S!Read!HERE)!Val = 3
       /\ I1(S!Read!1)!Val = 3
====
