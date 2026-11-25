---- MODULE InstPassOp ----
\* Qualified operator names from parameterized instances (e.g. O!Read, O!Pair)
\* passed as operator arguments to another parameterized instance or operator.
EXTENDS Naturals

---- MODULE Source ----
EXTENDS Naturals
CONSTANT k
Read == k + 1
Pair(v) == <<v, k>>
====

---- MODULE UseOp ----
CONSTANT F(_)
Val == F(4)
====

---- MODULE UseOp2 ----
CONSTANT F(_, _)
Val2 == F(4, 9)
====

---- MODULE Outer ----
EXTENDS Naturals
CONSTANT a
S(n) == INSTANCE Source WITH k <- a + n
Apply1(F(_), x) == F(x)
Run == Apply1(S!Read, 3)
====

O(p) == INSTANCE Source WITH k <- p
C(G(_)) == INSTANCE UseOp WITH F <- G
C2(G(_, _)) == INSTANCE UseOp2 WITH F <- G
Out(a) == INSTANCE Outer WITH a <- a
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Inv == /\ C(O!Read)!Val = 5
       /\ C2(O!Pair)!Val2 = <<9, 4>>
       /\ Out(10)!Run = 14
====
