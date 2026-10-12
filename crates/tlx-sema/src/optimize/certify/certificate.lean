theorem optimization_correct :
    (∀ s, Reachable rawBefore s → rawBefore.safe s) ↔
    (∀ a, Reachable rawAfter a → rawAfter.safe a) :=
  (reachableSystem_safety rawBefore).trans
    ((safety_iff certificate).trans (reachableSystem_safety rawAfter).symm)
theorem specification_correct :
    (∀ s, Reachable (withStuttering rawBefore) s → rawBefore.safe s) ↔
    (∀ a, Reachable (withStuttering rawAfter) a → rawAfter.safe a) := by
  simpa only [stuttering_reachable_iff] using optimization_correct
theorem counterexample_lifts {a} (ha : Reachable rawAfter a) (bad : ¬ rawAfter.safe a) :
    ∃ s : {s // Reachable rawBefore s}, (project s).val = a ∧ ¬ rawBefore.safe s.val := by
  obtain ⟨s, _, he⟩ := reachable_backward certificate (reachableSystem_all rawAfter ⟨a, ha⟩)
  refine ⟨s, congrArg Subtype.val he, ?_⟩
  intro good
  apply bad
  have h := (certificate.observe s).mp good
  rw [he] at h
  exact h
theorem deadlock_preserved (s : {s // Reachable rawBefore s}) :
    (¬ ∃ t, rawBefore.next s.val t) ↔ (¬ ∃ a, rawAfter.next (project s).val a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    have ar : Reachable rawAfter a := .step (project s).property ha
    obtain ⟨t, ht, _⟩ := (certificate.next s ⟨a, ar⟩).mp ha
    exact noStep ⟨t.val, ht⟩
  · intro noStep ⟨t, ht⟩
    have tr : Reachable rawBefore t := .step s.property ht
    have hn := (certificate.next s (project ⟨t, tr⟩)).mpr ⟨⟨t, tr⟩, ht, rfl⟩
    exact noStep ⟨(project ⟨t, tr⟩).val, hn⟩
#print axioms certificate
#print axioms optimization_correct
#print axioms specification_correct
#print axioms counterexample_lifts
#print axioms deadlock_preserved
end TlxOptimization.GeneratedPipeline
