---- MODULE TP4 ----
\* Reduced MisraReachability Termination shape: <>(pc = "Done") under weak
\* fairness. The probe drops the finishing action from Next, so Done is
\* unreachable and the run stutters at "Run".
EXTENDS Naturals
VARIABLE pc
Init == pc = "Init"
Step == pc = "Init" /\ pc' = "Run"
Finish == pc = "Run" /\ pc' = "Done"
Next == Step \/ Finish
Spec == Init /\ [][Next]_pc /\ WF_pc(Next)
ProbeNext == Step
ProbeSpec == Init /\ [][ProbeNext]_pc /\ WF_pc(ProbeNext)
Termination == <>(pc = "Done")
====
