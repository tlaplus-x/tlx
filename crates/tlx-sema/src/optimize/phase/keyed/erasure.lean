def before := (model sem).concrete
def intermediate := (model sem).erased.concrete
def erase := (model sem).erase
def after := (model sem).reduced
def project := (model sem).project
theorem erasure_certificate : Certificate (before sem) (intermediate sem) (erase sem) :=
(model sem).erasure_certificate
theorem certificate : Certificate (before sem) (after sem) (project sem) :=
(model sem).certificate
theorem optimization_correct :
(∀ s, Reachable (before sem) s → (before sem).safe s) ↔
(∀ a, Reachable (after sem) a → (after sem).safe a) :=
(model sem).optimization_correct
theorem specification_correct :
(∀ s, Reachable (withStuttering (before sem)) s → (before sem).safe s) ↔
(∀ a, Reachable (withStuttering (after sem)) a → (after sem).safe a) :=
(model sem).specification_correct
theorem counterexample_lifts {a} (ha : Reachable (after sem) a) (bad : ¬ (after sem).safe a) :
∃ s, Reachable (before sem) s ∧ project sem s = a ∧ ¬ (before sem).safe s :=
(model sem).counterexample_lifts ha bad
theorem deadlock_preserved (s : (model sem).Source) :
(¬ ∃ t, (before sem).next s t) ↔ (¬ ∃ a, (after sem).next (project sem s) a) :=
(model sem).deadlock_preserved s
theorem orbit_key_equivalent (s t : (model sem).Source) :
project sem s = project sem t ↔ ∃ p : GroupPerm groupSizes, rename p s.1 = t.1 :=
(model sem).orbit_key_equivalent s t
#print axioms erasure_certificate
#print axioms orbit_key_equivalent
#print axioms certificate
#print axioms optimization_correct
#print axioms specification_correct
#print axioms counterexample_lifts
#print axioms deadlock_preserved
end
end TlxOptimization.GeneratedErasedSymmetry
