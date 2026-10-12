/- Erasure and symmetry share the same branch, environment and map transfer. -/
set_option autoImplicit false
namespace TlxOptimization.ErasedKeyedRule
open TlxOptimization KeyedRule
noncomputable section

structure Model (C M K V B W H : Type) extends Operations C M K V B W where
  initial : (State C M K V × H) → Prop
  hiddenUpdate : B → State C M K V → W → Environment K → H → H

namespace Model
variable {C M K V B W H : Type} (m : Model C M K V B W H)
abbrev Source (_m : Model C M K V B W H) := State C M K V × H

def concrete : System m.Source where
  initial := m.initial
  next s t := ∃ b w keys, (m.guard b).eval (m.test b s.1.1 t.1.1 w) s.1.2 keys ∧
    t.1 = (t.1.1, update (m.test b s.1.1 t.1.1 w) (m.value b s.1.1 t.1.1 w) s.1.2 keys (m.writes b)) ∧
    t.2 = m.hiddenUpdate b s.1 w keys s.2
  safe s := ∀ keys, m.observation.eval (m.observe s.1.1) s.1.2 keys

def erased : KeyedRule.Model C M K V B W where
  toOperations := m.toOperations
  initial s := ∃ h, m.initial (s, h)

def erase (s : m.Source) : State C M K V := s.1

theorem erasure_certificate : Certificate m.concrete m.erased.concrete m.erase := by
  constructor
  · intro a
    constructor
    · rintro ⟨h, hi⟩
      exact ⟨(a, h), hi, rfl⟩
    · rintro ⟨s, hi, he⟩
      rw [← he]
      exact ⟨s.2, hi⟩
  · intro s a
    constructor
    · rintro ⟨b, w, keys, guard, next⟩
      exact ⟨(a, m.hiddenUpdate b s.1 w keys s.2), ⟨b, w, keys, guard, next, rfl⟩, rfl⟩
    · rintro ⟨t, ⟨b, w, keys, guard, next, _hidden⟩, he⟩
      rw [← he]
      exact ⟨b, w, keys, guard, next⟩
  · intro s
    rfl

noncomputable def reduced := m.erased.reduced
def project (s : m.Source) := KeyedRule.project (m.erase s)

theorem certificate : Certificate m.concrete m.reduced m.project :=
  compose (p := m.erase) (q := KeyedRule.project) m.erasure_certificate m.erased.certificate

theorem orbit_key_equivalent (s t : m.Source) :
    m.project s = m.project t ↔ ∃ p : Permutation K, rename p s.1 = t.1 :=
by
    constructor
    · exact Quotient.exact
    · intro h
      exact Quotient.sound (show (orbits C M K V).r s.1 t.1 from h)

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

theorem deadlock_preserved (s : m.Source) :
    (¬ ∃ t, m.concrete.next s t) ↔ (¬ ∃ a, m.reduced.next (m.project s) a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s a).mp ha
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨m.project t, (m.certificate.next s (m.project t)).mpr ⟨t, ht, rfl⟩⟩

end Model
end
end TlxOptimization.ErasedKeyedRule
