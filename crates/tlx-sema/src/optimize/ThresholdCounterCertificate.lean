/- Threshold-counter saturation rule semantics. Retained state C stays exact;
natural-number counters (scalar or fixed-domain map slots indexed by Fin k)
are saturated at per-slot caps `cap : Fin k → Nat` whenever every comparison
respects `Cmp.reqCap` and every transfer is monotone/resettable (`keep`,
`reset`, `add`, or quotient-observable `ite`). -/
set_option autoImplicit false
namespace TlxOptimization.ThresholdCounterRule
open TlxOptimization

inductive Cmp where
  | lt | le | eq | ne | gt | ge
  deriving DecidableEq

def Cmp.eval : Cmp → Nat → Nat → Prop
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b
  | .eq, a, b => a = b
  | .ne, a, b => a ≠ b
  | .gt, a, b => a > b
  | .ge, a, b => a ≥ b

def Cmp.reqCap : Cmp → Nat → Nat
  | .lt, t => t
  | .ge, t => t
  | .le, t => t + 1
  | .gt, t => t + 1
  | .eq, t => t + 1
  | .ne, t => t + 1

def saturate {k : Nat} (cap : Fin k → Nat) (n : Fin k → Nat) : Fin k → Nat :=
  fun i => min (n i) (cap i)

theorem Cmp.eval_commutes (op : Cmp) (n thresh cap : Nat) (h : op.reqCap thresh ≤ cap) :
    op.eval n thresh ↔ op.eval (min n cap) thresh := by
  cases op <;> simp only [Cmp.eval, Cmp.reqCap] at h ⊢ <;> omega

inductive Test {k : Nat} (cap : Fin k → Nat) where
  | pure (p : Prop)
  | cmp (key : Fin k) (op : Cmp) (thresh : Nat) (within : op.reqCap thresh ≤ cap key)
  | neg (p : Test cap)
  | conj (p q : Test cap)
  | disj (p q : Test cap)

def Test.eval {k : Nat} {cap : Fin k → Nat} (n : Fin k → Nat) : Test cap → Prop
  | .pure p => p
  | .cmp i op t _ => op.eval (n i) t
  | .neg p => ¬ p.eval n
  | .conj p q => p.eval n ∧ q.eval n
  | .disj p q => p.eval n ∨ q.eval n

theorem Test.eval_commutes {k : Nat} {cap : Fin k → Nat} (p : Test cap) (n : Fin k → Nat) :
    p.eval n ↔ p.eval (saturate cap n) := by
  induction p with
  | pure _ => rfl
  | cmp i op t within =>
    simp only [Test.eval, saturate]
    exact Cmp.eval_commutes op (n i) t (cap i) within
  | neg _ ih => simp only [Test.eval, ih]
  | conj _ _ ih₁ ih₂ => simp only [Test.eval, ih₁, ih₂]
  | disj _ _ ih₁ ih₂ => simp only [Test.eval, ih₁, ih₂]

inductive Transfer {k : Nat} (cap : Fin k → Nat) where
  | keep
  | reset (r : Nat)
  | add (d : Nat)
  | ite (cond : Test cap) (yes no : Transfer cap)

noncomputable def Transfer.evalConcrete {k : Nat} {cap : Fin k → Nat}
    (n : Fin k → Nat) (i : Fin k) : Transfer cap → Nat
  | .keep => n i
  | .reset r => r
  | .add d => n i + d
  | .ite cond yes no =>
    @_root_.ite Nat (cond.eval n) (Classical.propDecidable _)
      (yes.evalConcrete n i) (no.evalConcrete n i)

noncomputable def Transfer.evalReduced {k : Nat} {cap : Fin k → Nat}
    (a : Fin k → Nat) (i : Fin k) : Transfer cap → Nat
  | .keep => a i
  | .reset r => min r (cap i)
  | .add d => min (a i + d) (cap i)
  | .ite cond yes no =>
    @_root_.ite Nat (cond.eval a) (Classical.propDecidable _)
      (yes.evalReduced a i) (no.evalReduced a i)

theorem Transfer.eval_commutes {k : Nat} {cap : Fin k → Nat}
    (t : Transfer cap) (n : Fin k → Nat) (i : Fin k) :
    min (t.evalConcrete n i) (cap i) = t.evalReduced (saturate cap n) i := by
  induction t with
  | keep => rfl
  | reset r => rfl
  | add d =>
    simp only [Transfer.evalConcrete, Transfer.evalReduced, saturate]
    omega
  | ite cond yes no ihYes ihNo =>
    simp only [Transfer.evalConcrete, Transfer.evalReduced]
    rw [Test.eval_commutes cond n]
    split
    · exact ihYes
    · exact ihNo

structure Model (C W : Type) (k : Nat) where
  cap : Fin k → Nat
  initial : C → W → Prop
  seed : C → W → Fin k → Nat
  guard : C → C → W → Test cap
  transfer : C → C → W → Fin k → Transfer cap
  observe : C → Test cap
  initObserve : C → Test cap := fun _ => .pure True
  constraint : C → Test cap := fun _ => .pure True
  -- Action checks that retained core state determines completely.
  actionConstraint : C → C → Prop := fun _ _ => True
  actionObserve : C → C → Prop := fun _ _ => True

namespace Model
variable {C W : Type} {k : Nat} (m : Model C W k)

def project (s : C × (Fin k → Nat)) : C × (Fin k → Nat) :=
  (s.1, saturate m.cap s.2)

noncomputable def advanceState (s : C × (Fin k → Nat)) (d : C) (w : W) : C × (Fin k → Nat) :=
  (d, fun i => (m.transfer s.1 d w i).evalConcrete s.2 i)

noncomputable def advanceAbstract (a : C × (Fin k → Nat)) (d : C) (w : W) : C × (Fin k → Nat) :=
  (d, fun i => (m.transfer a.1 d w i).evalReduced a.2 i)

theorem advance_commutes (s : C × (Fin k → Nat)) (d : C) (w : W) :
    m.project (m.advanceState s d w) = m.advanceAbstract (m.project s) d w := by
  unfold project advanceState advanceAbstract
  apply congrArg (fun n => (d, n))
  funext i
  exact Transfer.eval_commutes _ s.2 i

def concrete : System (C × (Fin k → Nat)) where
  initial s := ∃ c w, m.initial c w ∧ s = (c, m.seed c w)
  next s t := ∃ w, (m.guard s.1 t.1 w).eval s.2 ∧ t = m.advanceState s t.1 w
  safe s := (m.observe s.1).eval s.2

def reduced : System (C × (Fin k → Nat)) where
  initial a := ∃ c w, m.initial c w ∧ a = (c, saturate m.cap (m.seed c w))
  next a b := ∃ w, (m.guard a.1 b.1 w).eval a.2 ∧ b = m.advanceAbstract a b.1 w
  safe a := (m.observe a.1).eval a.2

theorem certificate : Certificate m.concrete m.reduced m.project := by
  constructor
  · intro a
    constructor
    · rintro ⟨c, w, hi, rfl⟩
      exact ⟨(c, m.seed c w), ⟨c, w, hi, rfl⟩, rfl⟩
    · rintro ⟨s, ⟨c, w, hi, rfl⟩, rfl⟩
      exact ⟨c, w, hi, rfl⟩
  · intro s a
    constructor
    · rintro ⟨w, hg, ha⟩
      have hc : (m.guard s.1 a.1 w).eval s.2 := (Test.eval_commutes _ s.2).mpr hg
      refine ⟨m.advanceState s a.1 w, ⟨w, hc, rfl⟩, ?_⟩
      exact (m.advance_commutes s a.1 w).trans ha.symm
    · rintro ⟨t, ⟨w, hg, ht⟩, rfl⟩
      refine ⟨w, (Test.eval_commutes _ s.2).mp hg, ?_⟩
      exact (congrArg m.project ht).trans (m.advance_commutes s t.1 w)
  · intro s
    exact Test.eval_commutes (m.observe s.1) s.2

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

theorem deadlock_preserved (s : C × (Fin k → Nat)) :
    (¬ ∃ t, m.concrete.next s t) ↔ (¬ ∃ a, m.reduced.next (m.project s) a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s a).mp ha
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨m.project t, (m.certificate.next s (m.project t)).mpr ⟨t, ht, rfl⟩⟩

def constrainedConcrete : ConstrainedSystem (C × (Fin k → Nat)) where
  toSystem := m.concrete
  initSafe s := (m.initObserve s.1).eval s.2
  constraint s := (m.constraint s.1).eval s.2
  actionConstraint s t := m.actionConstraint s.1 t.1
  actionSafe s t := m.actionObserve s.1 t.1

def constrainedReduced : ConstrainedSystem (C × (Fin k → Nat)) where
  toSystem := m.reduced
  initSafe a := (m.initObserve a.1).eval a.2
  constraint a := (m.constraint a.1).eval a.2
  actionConstraint a b := m.actionConstraint a.1 b.1
  actionSafe a b := m.actionObserve a.1 b.1

theorem constrained_certificate :
    ConstrainedCertificate m.constrainedConcrete m.constrainedReduced m.project :=
  constrainedOfProjectedAction m.certificate
    (fun s => Test.eval_commutes (m.initObserve s.1) s.2)
    (fun s => Test.eval_commutes (m.constraint s.1) s.2)
    (fun _ _ => Iff.rfl)
    (fun _ _ => Iff.rfl)

end Model
end TlxOptimization.ThresholdCounterRule
