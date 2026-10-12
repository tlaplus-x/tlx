/- Connected deletion of unobserved state. The emitted transfers are total:
   literals, old-state copies and frames. Retained transitions and observations
   cannot inspect hidden state. No preservation obligations are premises. -/
namespace TlxOptimization.ErasureRule
structure Model (C H W : Type) where
  initial : C → W → Prop
  seed : C → W → H
  step : C → C → W → Prop
  update : C → C → W → H → H
  observe : C → Prop

namespace Model
variable {C H W : Type} (m : Model C H W)
def concrete : System (C × H) where
  initial s := ∃ w, m.initial s.1 w ∧ s.2 = m.seed s.1 w
  next s t := ∃ w, m.step s.1 t.1 w ∧ t.2 = m.update s.1 t.1 w s.2
  safe s := m.observe s.1

def reduced : System C where
  initial c := ∃ w, m.initial c w
  next c d := ∃ w, m.step c d w
  safe c := m.observe c

def project (_m : Model C H W) (s : C × H) : C := s.1

theorem certificate : Certificate m.concrete m.reduced m.project := by
  constructor
  · intro a
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨(a, m.seed a w), ⟨w, hw, rfl⟩, rfl⟩
    · rintro ⟨s, ⟨w, hw, _⟩, rfl⟩
      exact ⟨w, hw⟩
  · intro s a
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨(a, m.update s.1 a w s.2), ⟨w, hw, rfl⟩, rfl⟩
    · rintro ⟨t, ⟨w, hw, _⟩, rfl⟩
      exact ⟨w, hw⟩
  · intro s; rfl

theorem optimization_correct :
    (∀ s, Reachable m.concrete s → m.concrete.safe s) ↔
    (∀ a, Reachable m.reduced a → m.reduced.safe a) := safety_iff m.certificate

theorem specification_correct :
    (∀ s, Reachable (withStuttering m.concrete) s → m.concrete.safe s) ↔
    (∀ a, Reachable (withStuttering m.reduced) a → m.reduced.safe a) := by
  simpa only [stuttering_reachable_iff] using m.optimization_correct

theorem counterexample_lifts {a} (ha : Reachable m.reduced a) (bad : ¬ m.reduced.safe a) :
    ∃ s, Reachable m.concrete s ∧ m.project s = a ∧ ¬ m.concrete.safe s := by
  obtain ⟨s, hs, he⟩ := reachable_backward m.certificate ha
  refine ⟨s, hs, he, ?_⟩
  intro good
  apply bad
  rw [← he]
  exact (m.certificate.observe s).mp good

theorem deadlock_preserved (s : C × H) :
    (¬ ∃ t, m.concrete.next s t) ↔ (¬ ∃ a, m.reduced.next (m.project s) a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s a).mp ha
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨m.project t, (m.certificate.next s (m.project t)).mpr ⟨t, ht, rfl⟩⟩
end Model
end TlxOptimization.ErasureRule
