def before := (model sem).concrete
def intermediate := (model sem).intermediate
def thresholdProject := (model sem).thresholdProject
def symProject := (model sem).symProject
def after := (model sem).reduced
def project := (model sem).project
theorem threshold_certificate : Certificate (before sem) (intermediate sem) (thresholdProject sem) :=
  (model sem).threshold_certificate
theorem symmetry_certificate : Certificate (intermediate sem) (after sem) (symProject sem) :=
  (model sem).symmetry_certificate
theorem certificate : Certificate (before sem) (after sem) (project sem) :=
  (model sem).certificate
theorem optimization_correct :
  (∀ s, Reachable (before sem) s → (before sem).safe s) ↔
  (∀ q, Reachable (after sem) q → (after sem).safe q) :=
  (model sem).optimization_correct
theorem specification_correct :
  (∀ s, Reachable (withStuttering (before sem)) s → (before sem).safe s) ↔
  (∀ q, Reachable (withStuttering (after sem)) q → (after sem).safe q) :=
  (model sem).specification_correct
theorem counterexample_lifts {q} (hq : Reachable (after sem) q) (bad : ¬ (after sem).safe q) :
  ∃ s, Reachable (before sem) s ∧ project sem s = q ∧ ¬ (before sem).safe s :=
  (model sem).counterexample_lifts hq bad
theorem deadlock_preserved (s : (model sem).TState) :
  (¬ ∃ t, (before sem).next s t) ↔ (¬ ∃ q, (after sem).next (project sem s) q) :=
  (model sem).deadlock_preserved s
theorem orbit_key_equivalent (s t : (model sem).TState) :
  project sem s = project sem t ↔ (model sem).ThresholdOrbit (thresholdProject sem s) (thresholdProject sem t) :=
  (model sem).orbit_key_equivalent s t
#print axioms threshold_certificate
#print axioms symmetry_certificate
#print axioms orbit_key_equivalent
#print axioms certificate
#print axioms optimization_correct
#print axioms specification_correct
#print axioms counterexample_lifts
#print axioms deadlock_preserved
