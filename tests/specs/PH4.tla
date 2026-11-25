---- MODULE PH4 ----
\* Combinatorics.java (`choose`) and SequencesExt.java (`ReplaceAllSubSeqs`),
\* both Java overrides in TLC: the Java `choose` computes the binomial
\* coefficient without the module definition's intermediate `factorial`
\* overflow, and the Java `ReplaceAllSubSeqs` replaces text for three strings
\* (TLC evaluates the module definition for sequences: the leftmost
\* non-overlapping matches, as many as possible).
EXTENDS Combinatorics, SequencesExt, TLC, Sequences, FiniteSets, Naturals, Integers
\* choose: no intermediate factorial overflow.
ASSUME Print("choose20_10:", choose(20, 10)) = 184756
ASSUME Print("choose30_15:", choose(30, 15)) = 155117520
ASSUME Print("choose33_16:", choose(33, 16)) = 1166803110
\* choose: the boundary cases, in the Java method's order (`k > n` is 0).
ASSUME Print("choose0_0:", choose(0, 0)) = 1
ASSUME Print("choose5_0:", choose(5, 0)) = 1
ASSUME Print("choose5_5:", choose(5, 5)) = 1
ASSUME Print("choose5_1:", choose(5, 1)) = 5
ASSUME Print("choose5_4:", choose(5, 4)) = 5
ASSUME Print("choose0_1:", choose(0, 1)) = 0
ASSUME Print("choose5_6:", choose(5, 6)) = 0
\* ReplaceAllSubSeqs of three strings: Java's StringUtils.replace (leftmost,
\* non-overlapping, the replacement is not rescanned) and the interleaving
\* for an empty search string.
ASSUME Print("str:", ReplaceAllSubSeqs("x", "a", "banana")) = "bxnxnx"
ASSUME Print("str-none:", ReplaceAllSubSeqs("x", "q", "ab")) = "ab"
ASSUME Print("str-overlap:", ReplaceAllSubSeqs("x", "aa", "aaa")) = "xa"
ASSUME Print("str-grow:", ReplaceAllSubSeqs("aa", "a", "aaa")) = "aaaaaa"
ASSUME Print("str-grow2:", ReplaceAllSubSeqs("ba", "a", "aaa")) = "bababa"
ASSUME Print("str-same:", ReplaceAllSubSeqs("x", "ab", "abab")) = "xx"
ASSUME Print("str-empty:", ReplaceAllSubSeqs("x", "", "ab")) = "xaxb"
ASSUME Print("str-empty-t:", ReplaceAllSubSeqs("x", "", "")) = "x"
ASSUME Print("str-empty-r:", ReplaceAllSubSeqs("", "", "a")) = "a"
\* ReplaceAllSubSeqs of sequences: the module definition's ordered identity
\* guards (`s = t -> r`, `r = s -> t`) precede the search.
ASSUME Print("id-s-t:", ReplaceAllSubSeqs("hit", <<1>>, <<1>>)) = "hit"
ASSUME Print("id-r-s:", ReplaceAllSubSeqs(<<"A">>, <<"A">>, <<1, 2>>)) = <<1, 2>>
\* The leftmost non-overlapping matches; overlapping windows are still
\* compared by the definition's membership test.
ASSUME Print("seq-windows:", ReplaceAllSubSeqs(<<0>>, <<1>>, <<1, 2, 1>>)) = <<0, 2, 0>>
ASSUME Print("seq:", ReplaceAllSubSeqs(<<2>>, <<1>>, <<1, 1>>)) = <<2, 2>>
ASSUME Print("seq-overlap:", ReplaceAllSubSeqs(<<2, 2>>, <<1, 1>>, <<1, 1, 1>>)) = <<2, 2, 1>>
ASSUME Print("seq-none:", ReplaceAllSubSeqs(<<1>>, <<2>>, <<3, 4>>)) = <<3, 4>>
ASSUME Print("seq-long-s:", ReplaceAllSubSeqs(<<1>>, <<1, 1>>, <<1>>)) = <<1>>
ASSUME Print("seq-same:", ReplaceAllSubSeqs(<<5>>, <<1, 2>>, <<1, 2>>)) = <<5>>
ASSUME Print("seq-empty:", ReplaceAllSubSeqs(<<2>>, <<>>, <<1, 3>>)) = <<2, 1, 2, 3>>
ASSUME Print("seq-empty-grow:", ReplaceAllSubSeqs(<<1, 2>>, <<>>, <<3, 4>>)) = <<1, 2, 3, 1, 2, 4>>
ASSUME Print("seq-empty-t:", ReplaceAllSubSeqs(<<4>>, <<>>, <<>>)) = <<4>>
\* Also as a function over an enumerated domain (TLC's toTuple view of it).
ASSUME Print("seq-fcn:", ReplaceAllSubSeqs(<<9>>, <<1>>, [i \in {1, 2} |-> i])) = <<9, 2>>
VARIABLE x
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
====
