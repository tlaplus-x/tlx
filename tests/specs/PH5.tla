---- MODULE PH5 ----
\* Combinatorics!choose: TLC's Java override reports an overflow error when
\* the binomial coefficient does not fit TLC's 32-bit integers (TLC's
\* `Math.toIntExact`), instead of evaluating the module definition through
\* `factorial` (whose own overflow is a different error).
EXTENDS Combinatorics, Naturals
VARIABLE x
Init == x = 0
Next == x' = x
Inv == choose(34, 17) = 1
====
