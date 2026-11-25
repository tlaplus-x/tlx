---- MODULE InstNested ----
\* 2-level and 3-level nested parameterized INSTANCEs referencing CONSTANT and
\* VARIABLE declarations, including under ENABLED and through an unparameterized
\* nested module inside a parameterized instance.
EXTENDS Naturals

---- MODULE Level3 ----
EXTENDS Naturals
CONSTANT c3
VARIABLE v3
Read3 == c3 + v3
Step3 == v3' = v3 + c3
CanStep3 == ENABLED Step3
====

---- MODULE Level2 ----
EXTENDS Naturals
CONSTANT c2
VARIABLE v2
K(p3) == INSTANCE Level3 WITH c3 <- c2 + p3, v3 <- v2
Read2 == K(1)!Read3 + c2
CanFrom2(p3) == ENABLED (K(p3)!Step3)
====

---- MODULE Level1 ----
EXTENDS Naturals
CONSTANT c1
VARIABLE v1
J(p2) == INSTANCE Level2 WITH c2 <- c1 * 10 + p2, v2 <- v1
JExpr(p2) == INSTANCE Level2 WITH c2 <- c1 * 10 + p2, v2 <- v1 + 1

---- MODULE NestedIn1 ----
FromParent == c1 + v1
====
N == INSTANCE NestedIn1
====

---- MODULE WithOpOuter ----
EXTENDS Naturals
CONSTANT F(_)
VARIABLE u
---- MODULE InnerOp ----
EXTENDS Naturals
CONSTANT k
VARIABLE w
Eval == k + w
Can == ENABLED (w' = k + w)
====
Inner(q) == INSTANCE InnerOp WITH k <- F(q), w <- u + 1
====

VARIABLE x, y

I(p1) == INSTANCE Level1 WITH c1 <- p1, v1 <- x
IExpr(p1) == INSTANCE Level1 WITH c1 <- p1, v1 <- x * 2
Inc(z) == z + 1
HO(G(_)) == INSTANCE WithOpOuter WITH F <- G, u <- y

Init == x = 0 /\ y = 1

Next ==
    \/ /\ x < 30
       /\ I(1)!J(2)!K(3)!Step3
       /\ y' = y
    \/ /\ x >= 30
       /\ x' = 0
       /\ y' = (y % 2) + 1

Inv ==
    \* 3-level nested parameterized instance reading CONSTANT + VARIABLE
    /\ I(1)!J(2)!K(3)!Read3 = 15 + x
    \* 2-level nested parameterized instance calling inner instance definition
    /\ I(2)!J(3)!Read2 = 47 + x
    \* Nested module inside parameterized instance inheriting parent context
    /\ I(4)!N!FromParent = 4 + x
    \* ENABLED inside 3-level nested parameterized instance (outer expr subst)
    /\ IExpr(1)!J(2)!K(3)!CanStep3
    \* ENABLED inside 3-level nested parameterized instance (middle expr subst)
    /\ I(1)!JExpr(2)!K(3)!CanStep3
    \* ENABLED in middle module wrapping inner parameterized instance action
    /\ IExpr(1)!J(2)!CanFrom2(3)
    \* Nested parameterized instance with operator-valued outer parameter
    /\ HO(Inc)!Inner(5)!Eval = 6 + (y + 1)
    /\ HO(LAMBDA z : z * 3)!Inner(4)!Eval = 12 + (y + 1)
    /\ HO(Inc)!Inner(5)!Can
====
