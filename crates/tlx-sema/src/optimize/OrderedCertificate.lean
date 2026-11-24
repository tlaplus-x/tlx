/- Connected certificate for a scalar allocation frontier with a retained
initial anchor. Other state is retained exactly. The source lowering and
runtime representation remain trusted; no preservation premise is assumed. -/
set_option autoImplicit false
namespace TlxOptimization.OrderedRule
open TlxOptimization

theorem pair_cardinality (x y : Nat) :
    [x, y].eraseDups.length = (if x = y then 1 else 2) := by
  by_cases h : x = y
  · subst y; simp [List.eraseDups_cons]
  · have hy := Ne.symm h
    simp_all [List.eraseDups_cons]

def referenceRank (seed clock value : Nat) : Nat :=
  ([seed, clock].eraseDups.filter (fun n => n < value)).length + 1

theorem anchor_rank (seed clock : Nat) (bound : seed ≤ clock) :
    referenceRank seed clock seed = 1 := by
  by_cases h : seed = clock
  · subst clock; simp [referenceRank, List.eraseDups_cons]
  · have hn : ¬ clock < seed := by omega
    simp_all [referenceRank, List.eraseDups_cons]

theorem frontier_rank (seed clock : Nat) (bound : seed ≤ clock) :
    referenceRank seed clock clock = (if clock = seed then 1 else 2) := by
  by_cases h : seed = clock
  · subst clock; simp [referenceRank, List.eraseDups_cons]
  · have hy := Ne.symm h
    have lt : seed < clock := by omega
    simp_all [referenceRank, List.eraseDups_cons]


inductive Test where
  | pure (p : Prop)
  | initial
  | pairCardinalityEq (size : Nat)
  | neg (p : Test)
  | conj (p q : Test)
  | disj (p q : Test)

def Test.concrete (seed clock : Nat) : Test → Prop
  | .pure p => p
  | .initial => clock = seed
  | .pairCardinalityEq size => [clock, seed].eraseDups.length = size
  | .neg p => ¬ p.concrete seed clock
  | .conj p q => p.concrete seed clock ∧ q.concrete seed clock
  | .disj p q => p.concrete seed clock ∨ q.concrete seed clock

def Test.reduced (initial : Bool) : Test → Prop
  | .pure p => p
  | .initial => initial = true
  | .pairCardinalityEq size => (if initial then 1 else 2) = size
  | .neg p => ¬ p.reduced initial
  | .conj p q => p.reduced initial ∧ q.reduced initial
  | .disj p q => p.reduced initial ∨ q.reduced initial

theorem Test.commutes (p : Test) (seed clock : Nat) :
    p.concrete seed clock ↔ p.reduced (decide (clock = seed)) := by
  induction p with
  | pure => rfl
  | initial => simp [Test.concrete, Test.reduced]
  | pairCardinalityEq size => simp [Test.concrete, Test.reduced, pair_cardinality]
  | neg p ih => simp only [Test.concrete, Test.reduced, ih]
  | conj p q ih₁ ih₂ => simp only [Test.concrete, Test.reduced, ih₁, ih₂]
  | disj p q ih₁ ih₂ => simp only [Test.concrete, Test.reduced, ih₁, ih₂]

def phase (seed clock : Nat) : Bool := decide (clock = seed)

theorem advance (seed clock delta : Nat) (bound : seed ≤ clock) :
    phase seed (clock + delta) = (phase seed clock && decide (delta = 0)) := by
  have h : clock + delta = seed ↔ clock = seed ∧ delta = 0 := by omega
  by_cases hc : clock = seed <;> by_cases hd : delta = 0 <;> simp [phase, h, hc, hd]

-- With live values {seed, clock}, the retained anchor always has rank one;
-- the frontier has rank one exactly in the initial phase, otherwise two.
def rank (seed clock : Nat) : Nat := if clock = seed then 1 else 2

theorem rank_eq_iff (seed x y : Nat) :
    rank seed x = rank seed y ↔ phase seed x = phase seed y := by
  by_cases hx : x = seed <;> by_cases hy : y = seed <;> simp [rank, phase, hx, hy]

abbrev State (C : Type) (seed : Nat) := {clock : Nat // seed ≤ clock} × C

structure Model (C W : Type) where
  seed : Nat
  initial : C → W → Prop
  delta : W → Nat
  guard : C → C → W → Test
  observe : C → Test
  initObserve : C → Test := fun _ => .pure True
  constraint : C → Test := fun _ => .pure True

namespace Model
variable {C W : Type} (m : Model C W)

def concrete : System (State C m.seed) where
  initial s := s.1.val = m.seed ∧ ∃ w, m.initial s.2 w
  next s t := ∃ w, (m.guard s.2 t.2 w).concrete m.seed s.1.val ∧
    t.1.val = s.1.val + m.delta w
  safe s := (m.observe s.2).concrete m.seed s.1.val

def reduced : System (Bool × C) where
  initial s := s.1 = true ∧ ∃ w, m.initial s.2 w
  next s t := ∃ w, (m.guard s.2 t.2 w).reduced s.1 ∧
    t.1 = (s.1 && decide (m.delta w = 0))
  safe s := (m.observe s.2).reduced s.1

def project (s : State C m.seed) : Bool × C := (phase m.seed s.1.val, s.2)

-- This is the runtime rank key up to tuple grouping and source variable order.
def rankKey (s : State C m.seed) : Nat × Nat × C :=
  (referenceRank m.seed s.1.val s.1.val, referenceRank m.seed s.1.val m.seed, s.2)

theorem runtime_key_equivalent (s t : State C m.seed) :
    m.rankKey s = m.rankKey t ↔ m.project s = m.project t := by
  simp only [rankKey, project, Prod.mk.injEq,
    anchor_rank _ _ s.1.property, anchor_rank _ _ t.1.property,
    frontier_rank _ _ s.1.property, frontier_rank _ _ t.1.property, true_and]
  exact and_congr (rank_eq_iff m.seed s.1.val t.1.val) Iff.rfl

theorem certificate : Certificate m.concrete m.reduced m.project := by
  constructor
  · intro a
    constructor
    · rintro ⟨ha, w, hw⟩
      refine ⟨(⟨m.seed, Nat.le_refl _⟩, a.2), ⟨rfl, w, hw⟩, ?_⟩
      apply Prod.ext
      · simpa [project, phase] using ha.symm
      · rfl
    · rintro ⟨s, ⟨hs, w, hw⟩, he⟩
      subst a
      exact ⟨by simp [project, phase, hs], w, hw⟩
  · intro s a
    constructor
    · rintro ⟨w, hg, ha⟩
      let t : State C m.seed := (⟨s.1.val + m.delta w, Nat.le_trans s.1.property (Nat.le_add_right _ _)⟩, a.2)
      refine ⟨t, ⟨w, (Test.commutes _ _ _).mpr hg, rfl⟩, ?_⟩
      apply Prod.ext
      · exact (advance m.seed s.1.val (m.delta w) s.1.property).trans ha.symm
      · rfl
    · rintro ⟨t, ⟨w, hg, ht⟩, he⟩
      subst a
      refine ⟨w, (Test.commutes _ _ _).mp hg, ?_⟩
      change phase m.seed t.1.val = _
      rw [ht]
      exact advance m.seed s.1.val (m.delta w) s.1.property
  · intro s
    exact Test.commutes _ _ _

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

theorem deadlock_preserved (s : State C m.seed) :
    (¬ ∃ t, m.concrete.next s t) ↔ (¬ ∃ a, m.reduced.next (m.project s) a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s a).mp ha
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨m.project t, (m.certificate.next s (m.project t)).mpr ⟨t, ht, rfl⟩⟩

def constrainedConcrete : ConstrainedSystem (State C m.seed) where
  toSystem := m.concrete
  initSafe s := (m.initObserve s.2).concrete m.seed s.1.val
  constraint s := (m.constraint s.2).concrete m.seed s.1.val
  actionConstraint _ _ := True
  actionSafe _ _ := True

def constrainedReduced : ConstrainedSystem (Bool × C) where
  toSystem := m.reduced
  initSafe s := (m.initObserve s.2).reduced s.1
  constraint s := (m.constraint s.2).reduced s.1
  actionConstraint _ _ := True
  actionSafe _ _ := True

theorem constrained_certificate :
    ConstrainedCertificate m.constrainedConcrete m.constrainedReduced m.project :=
  constrainedOfStatePreds m.certificate
    (fun _ => Test.commutes _ _ _)
    (fun _ => Test.commutes _ _ _)
    (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
end Model
end TlxOptimization.OrderedRule
