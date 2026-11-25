---- MODULE InstOpParam ----
\* Operator-valued INSTANCE parameters: named operators, builtins, LAMBDAs
\* (including LAMBDA with LET), cross-definition calls inside the instantiated
\* module, WITH substitutions applying operator parameters, and nested
\* operator-parameterized instances.
EXTENDS Naturals

---- MODULE UnaryMod ----
EXTENDS Naturals
CONSTANT F(_)
Helper(a) == F(a) + 1
Main(b) == Helper(b) * 2
====

---- MODULE UnaryAnyMod ----
CONSTANT F(_)
Apply(a) == F(a)
Wrap(a) == Apply(a)
====

---- MODULE BinaryMod ----
CONSTANT Op(_, _)
Apply2(a, b) == Op(a, b)
Wrap(a, b) == Apply2(a, b)
====

---- MODULE AppliedInWith ----
EXTENDS Naturals
CONSTANT c
Val == c + 10
====

---- MODULE NestedHO ----
EXTENDS Naturals
CONSTANT OuterF(_)
---- MODULE InnerHO ----
EXTENDS Naturals
CONSTANT InnerG(_)
CONSTANT base
Combine(v) == InnerG(v) + base
====
Sub(H(_)) == INSTANCE InnerHO WITH InnerG <- H, base <- OuterF(2)
====

---- MODULE StepMod ----
EXTENDS Naturals
CONSTANT StepF(_)
VARIABLE v
Step == v' = StepF(v)
====

VARIABLE x

Inc(z) == z + 1
Apply1(G(_), v) == G(v)

U(F(_)) == INSTANCE UnaryMod WITH F <- F
UA(F(_)) == INSTANCE UnaryAnyMod WITH F <- F
B(Op(_, _)) == INSTANCE BinaryMod WITH Op <- Op
W(F(_)) == INSTANCE AppliedInWith WITH c <- F(3)
N(F(_)) == INSTANCE NestedHO WITH OuterF <- F
S(F(_)) == INSTANCE StepMod WITH StepF <- F, v <- x

Init == x = 0
Next ==
    \/ /\ x < 3
       /\ S(Inc)!Step
    \/ /\ x = 3
       /\ S(LAMBDA z : z - 3)!Step

Inv ==
    \* Named operator across multiple definitions inside the instance
    /\ U(Inc)!Main(x) = (x + 2) * 2
    \* LAMBDA across multiple definitions (capturing state variable x)
    /\ U(LAMBDA z : z * 3 + x)!Main(2) = (6 + x + 1) * 2
    \* LAMBDA with LET
    /\ U(LAMBDA z : LET w == z + 1 IN w * 2)!Main(x) = ((x + 1) * 2 + 1) * 2
    \* Builtin operators: stdlib +, core /\, \/, =, \union, and unary SUBSET
    /\ B( + )!Wrap(x, 5) = x + 5
    /\ B(/\)!Wrap(TRUE, x < 10)
    /\ B(\/)!Wrap(FALSE, x >= 0)
    /\ B(=)!Wrap(x, x)
    /\ UA(SUBSET)!Wrap({x}) = {{}, {x}}
    /\ B(\union)!Wrap({x}, {9}) = {x, 9}
    \* Operator parameter applied inside a WITH substitution for a 0-ary CONSTANT
    /\ W(Inc)!Val = 14
    /\ W(LAMBDA z : z * 4)!Val = 22
    \* Nested operator-parameterized instances
    /\ N(Inc)!Sub(LAMBDA z : z * 10)!Combine(x) = x * 10 + 3
    /\ N(LAMBDA z : z * 5)!Sub(Inc)!Combine(x) = (x + 1) + 10
    \* Operator-parameterized instance called inside a LAMBDA passed to another operator / instance
    /\ Apply1(LAMBDA y : U(Inc)!Helper(y), x) = x + 2
    /\ U(LAMBDA y : U(Inc)!Helper(y))!Helper(x) = x + 3
====
