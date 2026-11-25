---- MODULE PH6 ----
\* SequencesExt!ReplaceAllSubSeqs: the definition's identity guards (`s = t`
\* and `r = s`) return their operand unchanged. They must not force a lazy
\* function's entries: the caller may read only some of them, and forcing the
\* others can make an unreachable entry's error observable.
EXTENDS Naturals, Sequences, SequencesExt, FiniteSets, TLC
\* A partial function whose entry 2 divides by zero; the caller reads entry 1.
F == [i \in 1..2 |-> 3 \div (2 - i)]
ASSUME Print("lazy-partial:", ReplaceAllSubSeqs(F, <<1>>, <<1>>)[1]) = 3
\* A total function over SUBSET (1..64): forcing all entries would evaluate
\* Cardinality(S) for |S| >= 31, which overflows 32 bits.
G == [S \in SUBSET (1..64) |-> Cardinality(S)]
ASSUME Print("lazy-total:", ReplaceAllSubSeqs(G, <<1>>, <<1>>)[{1, 2}]) = 2
VARIABLE x
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
====
