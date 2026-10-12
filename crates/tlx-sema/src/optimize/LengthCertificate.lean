/- Sequence contents are forgotten only when every use factors through lengths.
Transfers stay explicit; guards and value leaves receive lengths, not sequences. -/
set_option autoImplicit false
namespace TlxOptimization.LengthRule
open TlxOptimization

inductive Transfer (E : Type) where
  | keep
  | reset (values : List E)
  | append (previous : Transfer E) (event : E)

def Transfer.concrete {E : Type} (h : List E) : Transfer E → List E
  | .keep => h
  | .reset values => values
  | .append previous event => previous.concrete h ++ [event]

def Transfer.reduced {E : Type} (n : Nat) : Transfer E → Nat
  | .keep => n
  | .reset values => values.length
  | .append previous _ => previous.reduced n + 1

theorem Transfer.commutes {E : Type} (t : Transfer E) (h : List E) :
    (t.concrete h).length = t.reduced h.length := by
  induction t with
  | keep => rfl
  | reset => rfl
  | append previous event ih => simp [Transfer.concrete, Transfer.reduced, ih]

def lengths {K E : Type} (h : K → List E) : K → Nat := fun k => (h k).length

structure Model (C K E W : Type) where
  initial : C → W → Prop
  seed : C → W → K → List E
  step : C → C → W → (K → Nat) → Prop
  transfer : C → C → W → (K → Nat) → K → Transfer E
  observe : C → (K → Nat) → Prop

namespace Model
variable {C K E W : Type} (m : Model C K E W)

def project (_m : Model C K E W) (s : C × (K → List E)) : C × (K → Nat) := (s.1, lengths s.2)
def seedState (c : C) (w : W) : C × (K → List E) := (c, m.seed c w)
def seedAbstract (c : C) (w : W) : C × (K → Nat) := (c, lengths (m.seed c w))
def advanceState (s : C × (K → List E)) (d : C) (w : W) : C × (K → List E) :=
  (d, fun k => (m.transfer s.1 d w (lengths s.2) k).concrete (s.2 k))
def advanceAbstract (s : C × (K → Nat)) (d : C) (w : W) : C × (K → Nat) :=
  (d, fun k => (m.transfer s.1 d w s.2 k).reduced (s.2 k))

theorem seed_commutes (c : C) (w : W) : m.project (m.seedState c w) = m.seedAbstract c w := rfl

theorem advance_commutes (s : C × (K → List E)) (d : C) (w : W) :
    m.project (m.advanceState s d w) = m.advanceAbstract (m.project s) d w := by
  change (d, _) = (d, _)
  apply congrArg (fun hs => (d, hs))
  funext k
  exact Transfer.commutes _ _

def concrete : System (C × (K → List E)) where
  initial s := ∃ c w, m.initial c w ∧ s = m.seedState c w
  next s t := ∃ w, m.step s.1 t.1 w (lengths s.2) ∧ t = m.advanceState s t.1 w
  safe s := m.observe s.1 (lengths s.2)

def reduced : System (C × (K → Nat)) where
  initial s := ∃ c w, m.initial c w ∧ s = m.seedAbstract c w
  next s t := ∃ w, m.step s.1 t.1 w s.2 ∧ t = m.advanceAbstract s t.1 w
  safe s := m.observe s.1 s.2

theorem certificate : Certificate m.concrete m.reduced m.project := by
  constructor
  · intro a
    constructor
    · rintro ⟨c, w, hi, rfl⟩
      exact ⟨m.seedState c w, ⟨c, w, hi, rfl⟩, rfl⟩
    · rintro ⟨s, ⟨c, w, hi, rfl⟩, rfl⟩
      exact ⟨c, w, hi, rfl⟩
  · intro s a
    constructor
    · rintro ⟨w, hg, ha⟩
      refine ⟨m.advanceState s a.1 w, ⟨w, hg, rfl⟩, ?_⟩
      exact (m.advance_commutes s a.1 w).trans ha.symm
    · rintro ⟨t, ⟨w, hg, ht⟩, rfl⟩
      refine ⟨w, hg, ?_⟩
      exact (congrArg m.project ht).trans (m.advance_commutes s t.1 w)
  · intro s
    rfl

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

theorem deadlock_preserved (s : C × (K → List E)) :
    (¬ ∃ t, m.concrete.next s t) ↔ (¬ ∃ a, m.reduced.next (m.project s) a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s a).mp ha
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨m.project t, (m.certificate.next s (m.project t)).mpr ⟨t, ht, rfl⟩⟩
end Model
end TlxOptimization.LengthRule
