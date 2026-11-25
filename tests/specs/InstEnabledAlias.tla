---- MODULE InstEnabledAlias ----
\* Nested ENABLED inside a nested module inheriting aliased VARIABLE
\* substitutions from its enclosing parameterized instance.
EXTENDS Naturals

---- MODULE Mid ----
CONSTANT k
VARIABLE v, w
---- MODULE Inner ----
Can == ENABLED (v' = k /\ w' = k + 1)
====
J == INSTANCE Inner
====

VARIABLE x
I(p) == INSTANCE Mid WITH k <- p, v <- x, w <- x
Init == x = 0
Next == UNCHANGED x
Inv == ~I(2)!J!Can
====
