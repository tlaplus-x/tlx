---- MODULE InstOpChoose ----
\* Action-enumerating builtin (\in) passed as an operator-valued INSTANCE
\* parameter must keep its action-enumeration semantics in Next.
EXTENDS Naturals

---- MODULE M ----
CONSTANT G(_, _)
Rel(a, b) == G(a, b)
====

I(F(_, _)) == INSTANCE M WITH G <- F
VARIABLE x
Init == x = 0
Next == I(\in)!Rel(x', {0, 1})
Inv == x = 0
====
