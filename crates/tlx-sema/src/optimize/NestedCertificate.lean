/- Explicit nested allocation transfers and their order-pattern quotient.
Source lowering, domains, totality and runtime execution remain trusted. -/
set_option autoImplicit false
namespace TlxOptimization.NestedRule
open TlxOptimization

inductive Reference (I A : Type) where
  | slot (i : I)
  | frontier
  | anchor (a : A)

structure Layout (A : Type) where
  seed : Nat
  positive : 0 < seed
  anchors : A → {n : Int // n ≤ (seed : Int)}

structure Store (I : Type) (seed : Nat) where
  clock : Nat
  bound : seed ≤ clock
  slots : I → Int
  below : ∀ i, slots i ≤ clock

def read {I A : Type} (layout : Layout A) (s : Store I layout.seed) : Reference I A → Int
  | .slot i => s.slots i
  | .frontier => (s.clock : Int)
  | .anchor a => (layout.anchors a).val

theorem read_bounded {I A : Type} (layout : Layout A) (s : Store I layout.seed) (r : Reference I A) :
    read layout s r ≤ s.clock := by
  cases r with
  | slot i => exact s.below i
  | frontier => exact Int.le_refl _
  | anchor a =>
    have h := (layout.anchors a).property
    have hs := s.bound
    simp only [read]
    omega

def Pattern {I A : Type} (layout : Layout A) (s t : Store I layout.seed) : Prop :=
  (∀ i j, read layout s i ≤ read layout s j ↔ read layout t i ≤ read layout t j) ∧
  (∀ i, sentinel (read layout s i) = sentinel (read layout t i))

inductive Token (I A : Type) (delta : Nat) where
  | old (ref : Reference I A)
  | fresh (offset : Fin (delta + 1))

def Token.eval {I A : Type} {delta : Nat} (layout : Layout A) (s : Store I layout.seed) : Token I A delta → Int
  | .old ref => read layout s ref
  | .fresh offset => ((s.clock + offset.val : Nat) : Int)

theorem Token.bounded {I A : Type} {delta : Nat} (layout : Layout A) (s : Store I layout.seed) (t : Token I A delta) :
    t.eval layout s ≤ ((s.clock + delta : Nat) : Int) := by
  cases t with
  | old ref =>
    have := read_bounded layout s ref
    simp only [Token.eval]
    omega
  | fresh offset =>
    have := offset.isLt
    simp only [Token.eval]
    omega

theorem Token.order_congr {I A : Type} {delta : Nat} (layout : Layout A) (s t : Store I layout.seed)
    (same : Pattern layout s t) (a b : Token I A delta) :
    a.eval layout s ≤ b.eval layout s ↔ a.eval layout t ≤ b.eval layout t := by
  cases a with
  | old a =>
    cases b with
    | old b => exact same.1 a b
    | fresh b =>
      have hs := read_bounded layout s a
      have ht := read_bounded layout t a
      simp only [Token.eval]
      omega
  | fresh a =>
    cases b with
    | old b =>
      have hs := read_bounded layout s b
      have ht := read_bounded layout t b
      have h := same.1 .frontier b
      simp only [Token.eval, read] at *
      omega
    | fresh b => simp only [Token.eval, Int.ofNat_le, Nat.add_le_add_iff_left]

theorem Token.sentinel_congr {I A : Type} {delta : Nat} (layout : Layout A) (s t : Store I layout.seed)
    (same : Pattern layout s t) (a : Token I A delta) :
    sentinel (a.eval layout s) = sentinel (a.eval layout t) := by
  cases a with
  | old ref => exact same.2 ref
  | fresh offset =>
    have hs := s.bound
    have ht := t.bound
    have hp := layout.positive
    have hsp : ¬ ((s.clock + offset.val : Nat) : Int) ≤ 0 := by omega
    have htp : ¬ ((t.clock + offset.val : Nat) : Int) ≤ 0 := by omega
    simp only [Token.eval, sentinel, hsp, htp, ite_false]

inductive Test (I A : Type) where
  | pure (p : Prop)
  | le (left right : Reference I A)
  | neg (p : Test I A)
  | conj (p q : Test I A)
  | disj (p q : Test I A)

def Test.eval {I A : Type} (layout : Layout A) (s : Store I layout.seed) : Test I A → Prop
  | .pure p => p
  | .le a b => read layout s a ≤ read layout s b
  | .neg p => ¬ p.eval layout s
  | .conj p q => p.eval layout s ∧ q.eval layout s
  | .disj p q => p.eval layout s ∨ q.eval layout s

theorem Test.congr {I A : Type} (layout : Layout A) (s t : Store I layout.seed)
    (same : Pattern layout s t) (p : Test I A) :
    p.eval layout s ↔ p.eval layout t := by
  induction p with
  | pure p => rfl
  | le a b => exact same.1 a b
  | neg p ih => exact not_congr ih
  | conj p q hp hq => exact and_congr hp hq
  | disj p q hp hq => exact or_congr hp hq

inductive Transfer (I A : Type) (delta : Nat) where
  | value (t : Token I A delta)
  | branch (test : Test I A) (yes no : Transfer I A delta)

noncomputable def Transfer.eval {I A : Type} {delta : Nat} (layout : Layout A)
    (s : Store I layout.seed) : Transfer I A delta → Token I A delta := by
  classical
  exact fun e => match e with
    | .value t => t
    | .branch p yes no => if p.eval layout s then yes.eval layout s else no.eval layout s

theorem Transfer.congr {I A : Type} {delta : Nat} (layout : Layout A) (s t : Store I layout.seed)
    (same : Pattern layout s t) (e : Transfer I A delta) :
    e.eval layout s = e.eval layout t := by
  induction e with
  | value v => rfl
  | branch p yes no hy hn =>
    simp only [Transfer.eval, hy, hn]
    rw [propext (p.congr layout s t same)]

noncomputable def advance {I A : Type} {delta : Nat} (layout : Layout A) (s : Store I layout.seed)
    (transfers : I → Transfer I A delta) : Store I layout.seed where
  clock := s.clock + delta
  bound := Nat.le_trans s.bound (Nat.le_add_right _ _)
  slots := fun i => ((transfers i).eval layout s).eval layout s
  below _i := Token.bounded layout s _

noncomputable def transferredReference {I A : Type} {delta : Nat} (layout : Layout A)
    (s : Store I layout.seed) (transfers : I → Transfer I A delta) : Reference I A → Token I A delta
  | .slot i => (transfers i).eval layout s
  | .frontier => .fresh ⟨delta, by omega⟩
  | .anchor a => .old (.anchor a)

theorem read_advance {I A : Type} {delta : Nat} (layout : Layout A) (s : Store I layout.seed)
    (transfers : I → Transfer I A delta) (r : Reference I A) :
    read layout (advance layout s transfers) r =
      (transferredReference layout s transfers r).eval layout s := by
  cases r <;> rfl

theorem advance_congr {I A : Type} {delta : Nat} (layout : Layout A) (s t : Store I layout.seed)
    (same : Pattern layout s t) (transfers : I → Transfer I A delta) :
    Pattern layout (advance layout s transfers) (advance layout t transfers) := by
  have ref (r : Reference I A) : transferredReference layout s transfers r = transferredReference layout t transfers r := by
    cases r with
    | slot i => exact (transfers i).congr layout s t same
    | frontier => rfl
    | anchor a => rfl
  constructor
  · intro a b
    simp only [read_advance]
    rw [← ref a, ← ref b]
    exact Token.order_congr layout s t same _ _
  · intro r
    simp only [read_advance]
    rw [← ref r]
    exact Token.sentinel_congr layout s t same _


inductive FamilyTest (F : Type) (I A : F → Type) where
  | pure (p : Prop)
  | le (f : F) (left right : Reference (I f) (A f))
  | neg (p : FamilyTest F I A)
  | conj (p q : FamilyTest F I A)
  | disj (p q : FamilyTest F I A)

abbrev Stores {F : Type} (I A : F → Type) (layout : (f : F) → Layout (A f)) :=
  (f : F) → Store (I f) (layout f).seed

def FamilyTest.eval {F : Type} {I A : F → Type} (layout : (f : F) → Layout (A f))
    (s : Stores I A layout) : FamilyTest F I A → Prop
  | .pure p => p
  | .le f a b => read (layout f) (s f) a ≤ read (layout f) (s f) b
  | .neg p => ¬ p.eval layout s
  | .conj p q => p.eval layout s ∧ q.eval layout s
  | .disj p q => p.eval layout s ∨ q.eval layout s

def Patterns {F : Type} {I A : F → Type} (layout : (f : F) → Layout (A f))
    (s t : Stores I A layout) : Prop := ∀ f, Pattern (layout f) (s f) (t f)

theorem FamilyTest.congr {F : Type} {I A : F → Type} (layout : (f : F) → Layout (A f))
    (s t : Stores I A layout) (same : Patterns layout s t) (p : FamilyTest F I A) :
    p.eval layout s ↔ p.eval layout t := by
  induction p with
  | pure p => rfl
  | le f a b => exact (same f).1 a b
  | neg p ih => exact not_congr ih
  | conj p q hp hq => exact and_congr hp hq
  | disj p q hp hq => exact or_congr hp hq

structure Model (C F W : Type) (I A : F → Type) where
  layout : (f : F) → Layout (A f)
  initial : C → W → FamilyTest F I A
  seedValues : W → (f : F) → I f → {n : Int // n ≤ ((layout f).seed : Int)}
  delta : W → F → Nat
  transfers : C → C → (w : W) → (f : F) → I f → Transfer (I f) (A f) (delta w f)
  guard : C → C → W → FamilyTest F I A
  observe : C → FamilyTest F I A
  initObserve : C → FamilyTest F I A := fun _ => .pure True
  constraint : C → FamilyTest F I A := fun _ => .pure True

namespace Model
variable {C F W : Type} {I A : F → Type} (m : Model C F W I A)

abbrev State := C × Stores I A m.layout

def seeds (w : W) : Stores I A m.layout := fun f => {
  clock := (m.layout f).seed
  bound := Nat.le_refl _
  slots := fun i => (m.seedValues w f i).val
  below := fun i => (m.seedValues w f i).property }

noncomputable def advanceState (s : m.State) (d : C) (w : W) : m.State :=
  (d, fun f => advance (m.layout f) (s.2 f) (m.transfers s.1 d w f))

def related (s t : m.State) : Prop := s.1 = t.1 ∧ Patterns m.layout s.2 t.2

def equivalence : Setoid m.State where
  r := m.related
  iseqv := {
    refl := fun _ => ⟨rfl, fun _ => ⟨fun _ _ => Iff.rfl, fun _ => rfl⟩⟩
    symm := fun h => ⟨h.1.symm, fun f => ⟨fun i j => ((h.2 f).1 i j).symm, fun i => ((h.2 f).2 i).symm⟩⟩
    trans := fun h g => ⟨h.1.trans g.1, fun f => ⟨fun i j => ((h.2 f).1 i j).trans ((g.2 f).1 i j), fun i => ((h.2 f).2 i).trans ((g.2 f).2 i)⟩⟩ }

def project (s : m.State) : Quotient m.equivalence := Quotient.mk _ s

def concrete : System m.State where
  initial s := ∃ w, (m.initial s.1 w).eval m.layout (m.seeds w) ∧ s.2 = m.seeds w
  next s t := ∃ w, (m.guard s.1 t.1 w).eval m.layout s.2 ∧ t = m.advanceState s t.1 w
  safe s := (m.observe s.1).eval m.layout s.2

theorem advance_related (s t : m.State) (same : m.related s t) (d : C) (w : W) :
    m.related (m.advanceState s d w) (m.advanceState t d w) := by
  refine ⟨rfl, ?_⟩
  intro f
  simp only [advanceState]
  rw [same.1]
  exact advance_congr (m.layout f) (s.2 f) (t.2 f) (same.2 f) _

theorem next_related (s t u : m.State) (same : m.related s t) (step : m.concrete.next s u) :
    ∃ v, m.concrete.next t v ∧ m.related u v := by
  obtain ⟨w, hg, hu⟩ := step
  refine ⟨m.advanceState t u.1 w, ⟨w, ?_, rfl⟩, ?_⟩
  · change (m.guard t.1 u.1 w).eval m.layout t.2
    rw [← same.1]
    exact ((m.guard s.1 u.1 w).congr m.layout s.2 t.2 same.2).mp hg
  · rw [hu]
    exact m.advance_related s t same u.1 w

theorem safe_related (s t : m.State) (same : m.related s t) :
    m.concrete.safe s ↔ m.concrete.safe t := by
  change (m.observe s.1).eval m.layout s.2 ↔ (m.observe t.1).eval m.layout t.2
  rw [same.1]
  exact FamilyTest.congr m.layout s.2 t.2 same.2 _

noncomputable def reduced : System (Quotient m.equivalence) where
  initial a := ∃ s, m.concrete.initial s ∧ m.project s = a
  next a b := ∃ s t, m.project s = a ∧ m.concrete.next s t ∧ m.project t = b
  safe a := Quotient.liftOn a m.concrete.safe (fun s t h => propext (m.safe_related s t h))

theorem certificate : Certificate m.concrete m.reduced m.project := by
  constructor
  · intro a
    rfl
  · intro s a
    constructor
    · rintro ⟨x, t, hx, hn, ht⟩
      have same : m.related x s := Quotient.exact hx
      obtain ⟨u, hu, related⟩ := m.next_related x s t same hn
      refine ⟨u, hu, ?_⟩
      have he : m.project t = m.project u := Quotient.sound (show m.equivalence.r t u from related)
      exact he.symm.trans ht
    · rintro ⟨t, hn, ht⟩
      exact ⟨s, t, rfl, hn, ht⟩
  · intro s
    rfl

def rankKey (refs : (f : F) → List (Reference (I f) (A f))) (s : m.State) :
    C × ((f : F) → Reference (I f) (A f) → Int) :=
  (s.1, fun f r => canonical ((refs f).map (read (m.layout f) (s.2 f))) (read (m.layout f) (s.2 f) r))

theorem runtime_key_equivalent (refs : (f : F) → List (Reference (I f) (A f)))
    (complete : ∀ f r, r ∈ refs f) (s t : m.State) :
    m.rankKey refs s = m.rankKey refs t ↔ m.project s = m.project t := by
  constructor
  · intro h
    simp only [rankKey] at h
    have parts := Prod.mk.inj h
    have core : s.1 = t.1 := parts.1
    have ranks (f : F) (r : Reference (I f) (A f)) :=
      congrFun (congrFun parts.2 f) r
    have same : m.related s t := by
      refine ⟨core, ?_⟩
      intro f
      exact (canonical_keys_equivalent (read (m.layout f) (s.2 f)) (read (m.layout f) (t.2 f)) (refs f) (complete f)).mp (ranks f)
    exact Quotient.sound (show m.equivalence.r s t from same)
  · intro h
    have same : m.related s t := Quotient.exact h
    unfold rankKey
    apply Prod.ext
    · exact same.1
    funext f r
    exact (canonical_keys_equivalent (read (m.layout f) (s.2 f)) (read (m.layout f) (t.2 f)) (refs f) (complete f)).mpr (same.2 f) r

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

theorem deadlock_preserved (s : m.State) :
    (¬ ∃ t, m.concrete.next s t) ↔ (¬ ∃ a, m.reduced.next (m.project s) a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s a).mp ha
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨m.project t, (m.certificate.next s (m.project t)).mpr ⟨t, ht, rfl⟩⟩

def constrainedConcrete : ConstrainedSystem m.State where
  toSystem := m.concrete
  initSafe s := (m.initObserve s.1).eval m.layout s.2
  constraint s := (m.constraint s.1).eval m.layout s.2
  actionConstraint _ _ := True
  actionSafe _ _ := True

theorem initSafe_related (s t : m.State) (same : m.related s t) :
    m.constrainedConcrete.initSafe s ↔ m.constrainedConcrete.initSafe t := by
  change (m.initObserve s.1).eval m.layout s.2 ↔ (m.initObserve t.1).eval m.layout t.2
  rw [same.1]
  exact FamilyTest.congr m.layout s.2 t.2 same.2 _

theorem constraint_related (s t : m.State) (same : m.related s t) :
    m.constrainedConcrete.constraint s ↔ m.constrainedConcrete.constraint t := by
  change (m.constraint s.1).eval m.layout s.2 ↔ (m.constraint t.1).eval m.layout t.2
  rw [same.1]
  exact FamilyTest.congr m.layout s.2 t.2 same.2 _

noncomputable def constrainedReduced : ConstrainedSystem (Quotient m.equivalence) where
  toSystem := m.reduced
  initSafe a := Quotient.liftOn a m.constrainedConcrete.initSafe (fun s t h => propext (m.initSafe_related s t h))
  constraint a := Quotient.liftOn a m.constrainedConcrete.constraint (fun s t h => propext (m.constraint_related s t h))
  actionConstraint _ _ := True
  actionSafe _ _ := True

theorem constrained_certificate :
    ConstrainedCertificate m.constrainedConcrete m.constrainedReduced m.project :=
  constrainedOfStatePreds m.certificate
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)

end Model
end TlxOptimization.NestedRule
