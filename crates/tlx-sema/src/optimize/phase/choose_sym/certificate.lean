def rawBefore := (model sem).rawConcrete
def before := (model sem).validConcrete
def after := (model sem).reduced
def project := (model sem).project
theorem inductive_invariant (s : (model sem).RState) (hs : Reachable (rawBefore sem) s) :
(model sem).valid s :=
(model sem).inductive_invariant s hs
theorem certificate : Certificate (before sem) (after sem) (project sem) :=
(model sem).certificate
theorem optimization_correct :
(∀ s, Reachable (rawBefore sem) s → (rawBefore sem).safe s) ↔
(∀ a, Reachable (after sem) a → (after sem).safe a) :=
(model sem).optimization_correct
theorem specification_correct :
(∀ s, Reachable (withStuttering (rawBefore sem)) s → (rawBefore sem).safe s) ↔
(∀ a, Reachable (withStuttering (after sem)) a → (after sem).safe a) :=
(model sem).specification_correct
theorem counterexample_lifts {a} (ha : Reachable (after sem) a) (bad : ¬ (after sem).safe a) :
∃ s : (model sem).ValidState, Reachable (rawBefore sem) s.val ∧ project sem s = a ∧ ¬ (rawBefore sem).safe s.val :=
(model sem).counterexample_lifts ha bad
theorem deadlock_preserved (s : (model sem).ValidState) :
(¬ ∃ t, (rawBefore sem).next s.val t) ↔ (¬ ∃ a, (after sem).next (project sem s) a) :=
(model sem).deadlock_preserved s
theorem orbit_key_equivalent (s t : (model sem).ValidState) :
project sem s = project sem t ↔ (model sem).Orbit s t :=
(model sem).orbit_key_equivalent s t
#print axioms inductive_invariant
#print axioms orbit_key_equivalent
#print axioms certificate
#print axioms optimization_correct
#print axioms specification_correct
#print axioms counterexample_lifts
#print axioms deadlock_preserved
end
end TlxOptimization.GeneratedChooseSymmetry
