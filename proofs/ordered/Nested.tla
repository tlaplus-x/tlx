----------------------------- MODULE Nested -----------------------------
EXTENDS Integers
CONSTANT Actors
VARIABLES frontier, serial, records
Empty == [items |-> <<[stamp |-> -1, serial |-> 0]>>, ready |-> FALSE]
Init == /\ frontier = 1 /\ serial = 100
        /\ records = [a \in Actors |-> Empty]
Reserve(a) == /\ frontier' = frontier + 1
              /\ serial' = serial + 2
              /\ records' = [records EXCEPT ![a].items[1].stamp = frontier + 1,
                     ![a].items[1].serial = IF records[a].items[1].serial = 0
                                          THEN serial + 1 ELSE records[a].items[1].serial,
                     ![a].ready = TRUE]
Copy(a,b) == /\ records[a].items[1].stamp < records[b].items[1].stamp
             /\ records' = [records EXCEPT ![a] = records[b]]
             /\ UNCHANGED <<frontier, serial>>
Reset(a) == /\ records' = [records EXCEPT ![a] = Empty]
            /\ UNCHANGED <<frontier, serial>>
Next == \E a \in Actors : Reserve(a) \/ Reset(a) \/ (\E b \in Actors : Copy(a,b))
Inv == \A a \in Actors :
       /\ records[a].items[1].stamp <= frontier
       /\ records[a].items[1].serial <= serial
       /\ records[a].ready \in BOOLEAN
=============================================================================
