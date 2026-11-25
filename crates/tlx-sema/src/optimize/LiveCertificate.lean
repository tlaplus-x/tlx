/- Immutable tables retain only values reachable through live allocation roots. -/
set_option autoImplicit false
namespace TlxOptimization.LiveRule
open TlxOptimization NestedRule

structure Table (V : Type) where
  values : Int → Option V

def views {I A V : Type} (l : Layout A) (s : Store I l.seed) (h : Table V) :
    Reference I A → Option V := fun r => h.values (NestedRule.read l s r)

noncomputable def append {V : Type} (h : Table V) (clock : Nat) (tick : Bool) (v : V) : Table V := by
  classical
  exact { values := fun k => if tick = true ∧ k = ((clock + 1 : Nat) : Int) then some v else h.values k }

theorem append_bounded {V : Type} (h : Table V) (clock : Nat) (tick : Bool) (v : V)
    (bound : ∀ k x, h.values k = some x → 0 < k ∧ k ≤ (clock : Int)) :
    ∀ k x, (append h clock tick v).values k = some x → 0 < k ∧ k ≤ ((clock + if tick then 1 else 0 : Nat) : Int) := by
  intro k x hx
  simp only [append] at hx
  split at hx
  · rename_i hnew
    rcases hnew with ⟨ht, hk⟩
    simp only [ht, ite_true]
    omega
  · have := bound k x hx
    split <;> omega

theorem append_old {I A V : Type} (l : Layout A) (s : Store I l.seed) (h : Table V)
    (tick : Bool) (v : V) (r : Reference I A) :
    (append h s.clock tick v).values (NestedRule.read l s r) = h.values (NestedRule.read l s r) := by
  have := read_bounded l s r
  simp only [append]
  split
  · rename_i hn
    omega
  · rfl

theorem append_token {I A V : Type} (l : Layout A) (s t : Store I l.seed)
    (hs : Table V) (ht : Table V)
    (same : views l s hs = views l t ht) (tick : Bool) (v : V)
    (delta : Nat) (hd : delta = if tick then 1 else 0) (tok : Token I A delta) :
    (append hs s.clock tick v).values (tok.eval l s) = (append ht t.clock tick v).values (tok.eval l t) := by
  cases tok with
  | old r => exact (append_old l s hs tick v r).trans ((congrFun same r).trans (append_old l t ht tick v r).symm)
  | fresh offset =>
    have hoff := offset.isLt
    cases tick with
    | false =>
      have hz : offset.val = 0 := by simp only [Bool.false_eq_true, ↓reduceIte] at hd; omega
      simpa [append, Token.eval, hz, views, NestedRule.read] using congrFun same Reference.frontier
    | true =>
      have hor : offset.val = 0 ∨ offset.val = 1 := by simp only [↓reduceIte] at hd; omega
      rcases hor with hz | ho
      · have hs' := append_old l s hs true v Reference.frontier
        have ht' := append_old l t ht true v Reference.frontier
        simpa [Token.eval, hz, NestedRule.read] using hs'.trans ((congrFun same Reference.frontier).trans ht'.symm)
      · simp [append, Token.eval, ho]

structure Model (C F W V : Type) (I A : F → Type) where
  layout : (f : F) → Layout (A f)
  family : F
  initial : C → W → FamilyTest F I A
  seedValues : W → (f : F) → I f → {n : Int // n ≤ ((layout f).seed : Int)}
  seedPayload : C → W → V
  tick : W → Bool
  delta : W → F → Nat
  historyDelta : ∀ w, delta w family = if tick w then 1 else 0
  transfers : C → C → (w : W) → (Reference (I family) (A family) → Option V) →
    (f : F) → I f → Transfer (I f) (A f) (delta w f)
  guard : C → C → W → (Reference (I family) (A family) → Option V) → FamilyTest F I A
  payload : C → C → W → (Reference (I family) (A family) → Option V) → V
  observe : C → (Reference (I family) (A family) → Option V) → FamilyTest F I A
  initObserve : C → (Reference (I family) (A family) → Option V) → FamilyTest F I A := fun _ _ => .pure True
  constraint : C → (Reference (I family) (A family) → Option V) → FamilyTest F I A := fun _ _ => .pure True
  -- Action checks that the retained core state determines completely. They
  -- cannot inspect the projected rank pattern or retained payloads.
  actionConstraint : C → C → Prop := fun _ _ => True
  actionObserve : C → C → Prop := fun _ _ => True

namespace Model
variable {C F W V : Type} {I A : F → Type} (m : Model C F W V I A)

abbrev Numeric := Stores I A m.layout
abbrev Roots := Reference (I m.family) (A m.family)
structure State where
  core : C
  numbers : m.Numeric
  history : Table V
  bounded : ∀ k v, history.values k = some v → 0 < k ∧ k ≤ ((numbers m.family).clock : Int)

def roots (s : m.State) : m.Roots → Option V := views (m.layout m.family) (s.numbers m.family) s.history

def seeds (w : W) : m.Numeric := fun f => {
  clock := (m.layout f).seed
  bound := Nat.le_refl _
  slots := fun i => (m.seedValues w f i).val
  below := fun i => (m.seedValues w f i).property }

noncomputable def seedTable (c : C) (w : W) : Table V := by
  classical
  exact { values := fun k => if k = ((m.layout m.family).seed : Int) then some (m.seedPayload c w) else none }

noncomputable def advanceState (s : m.State) (d : C) (w : W) : m.State where
  core := d
  numbers := fun f => advance (m.layout f) (s.numbers f) (m.transfers s.core d w (m.roots s) f)
  history := append s.history (s.numbers m.family).clock (m.tick w) (m.payload s.core d w (m.roots s))
  bounded := by
    simpa only [advance, m.historyDelta w] using
      append_bounded s.history (s.numbers m.family).clock (m.tick w) (m.payload s.core d w (m.roots s)) s.bounded

def related (s t : m.State) : Prop :=
  s.core = t.core ∧ Patterns m.layout s.numbers t.numbers ∧ m.roots s = m.roots t

def equivalence : Setoid m.State where
  r := m.related
  iseqv := {
    refl := fun _ => ⟨rfl, (fun _ => ⟨fun _ _ => Iff.rfl, fun _ => rfl⟩), rfl⟩
    symm := fun h => ⟨h.1.symm, (fun f => ⟨fun i j => ((h.2.1 f).1 i j).symm, fun i => ((h.2.1 f).2 i).symm⟩), h.2.2.symm⟩
    trans := fun h g => ⟨h.1.trans g.1, (fun f => ⟨fun i j => ((h.2.1 f).1 i j).trans ((g.2.1 f).1 i j), fun i => ((h.2.1 f).2 i).trans ((g.2.1 f).2 i)⟩), h.2.2.trans g.2.2⟩ }

def project (s : m.State) : Quotient m.equivalence := Quotient.mk _ s

noncomputable def concrete : System m.State where
  initial s := ∃ w, (m.initial s.core w).eval m.layout (m.seeds w) ∧
    s.numbers = m.seeds w ∧ s.history.values = (m.seedTable s.core w).values
  next s t := ∃ w, (m.guard s.core t.core w (m.roots s)).eval m.layout s.numbers ∧ t = m.advanceState s t.core w
  safe s := (m.observe s.core (m.roots s)).eval m.layout s.numbers

theorem advance_roots (s : m.State) (d : C) (w : W) (r : m.Roots) :
    m.roots (m.advanceState s d w) r =
      (append s.history (s.numbers m.family).clock (m.tick w) (m.payload s.core d w (m.roots s))).values
        (NestedRule.read (m.layout m.family) (advance (m.layout m.family) (s.numbers m.family)
          (m.transfers s.core d w (m.roots s) m.family)) r) := by
  rfl

-- A transported offset retains its numeric interpretation; no freshness premise is assumed.
theorem lookup_token_congr (s t : m.State) (same : m.related s t) (w : W) (v : V)
    (token : Token (I m.family) (A m.family) (m.delta w m.family)) :
    (append s.history (s.numbers m.family).clock (m.tick w) v).values (token.eval (m.layout m.family) (s.numbers m.family)) =
      (append t.history (t.numbers m.family).clock (m.tick w) v).values (token.eval (m.layout m.family) (t.numbers m.family)) := by
  exact append_token (m.layout m.family) (s.numbers m.family) (t.numbers m.family) s.history t.history same.2.2 (m.tick w) v _ (m.historyDelta w) token

theorem advance_related (s t : m.State) (same : m.related s t) (d : C) (w : W) :
    m.related (m.advanceState s d w) (m.advanceState t d w) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro f
    simp only [advanceState]
    rw [same.1, same.2.2]
    exact advance_congr (m.layout f) (s.numbers f) (t.numbers f) (same.2.1 f) _
  · funext r
    rw [m.advance_roots, m.advance_roots, read_advance, read_advance]
    have tr : transferredReference (m.layout m.family) (s.numbers m.family)
        (m.transfers s.core d w (m.roots s) m.family) r =
      transferredReference (m.layout m.family) (t.numbers m.family)
        (m.transfers t.core d w (m.roots t) m.family) r := by
      rw [same.1, same.2.2]
      cases r with
      | slot i => exact Transfer.congr _ _ _ (same.2.1 m.family) _
      | frontier => rfl
      | anchor a => rfl
    rw [← tr, ← same.1, ← same.2.2]
    exact m.lookup_token_congr s t same w _ _

theorem next_related (s t u : m.State) (same : m.related s t) (step : m.concrete.next s u) :
    ∃ v, m.concrete.next t v ∧ m.related u v := by
  obtain ⟨w, hg, hu⟩ := step
  refine ⟨m.advanceState t u.core w, ⟨w, ?_, rfl⟩, ?_⟩
  · change (m.guard t.core u.core w (m.roots t)).eval m.layout t.numbers
    rw [← same.1, ← same.2.2]
    exact ((m.guard s.core u.core w (m.roots s)).congr m.layout s.numbers t.numbers same.2.1).mp hg
  · rw [hu]
    exact m.advance_related s t same u.core w

theorem safe_related (s t : m.State) (same : m.related s t) :
    m.concrete.safe s ↔ m.concrete.safe t := by
  change (m.observe s.core (m.roots s)).eval m.layout s.numbers ↔ (m.observe t.core (m.roots t)).eval m.layout t.numbers
  rw [same.1, same.2.2]
  exact FamilyTest.congr m.layout s.numbers t.numbers same.2.1 _

noncomputable def reduced : System (Quotient m.equivalence) where
  initial a := ∃ s, m.concrete.initial s ∧ m.project s = a
  next a b := ∃ s t, m.project s = a ∧ m.concrete.next s t ∧ m.project t = b
  safe a := Quotient.liftOn a m.concrete.safe (fun s t h => propext (m.safe_related s t h))

theorem certificate : Certificate m.concrete m.reduced m.project := by
  constructor
  · intro a; rfl
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
  · intro s; rfl

def numericKey (refs : (f : F) → List (Reference (I f) (A f))) (s : m.State) :
    (f : F) → Reference (I f) (A f) → Int :=
  fun f r => canonical ((refs f).map (NestedRule.read (m.layout f) (s.numbers f)))
    (NestedRule.read (m.layout f) (s.numbers f) r)

-- The retained finite table is represented by its graph, independent of entry order.
def retainedTable (refs : (f : F) → List (Reference (I f) (A f))) (s : m.State) (k : Int) (v : V) : Prop :=
  ∃ r, m.numericKey refs s m.family r = k ∧ m.roots s r = some v

theorem root_key_injective (refs : (f : F) → List (Reference (I f) (A f)))
    (complete : ∀ f r, r ∈ refs f) (s : m.State) (r q : m.Roots)
    (same : m.numericKey refs s m.family r = m.numericKey refs s m.family q) :
    m.roots s r = m.roots s q := by
  have mem (r : m.Roots) : NestedRule.read (m.layout m.family) (s.numbers m.family) r ∈
      (refs m.family).map (NestedRule.read (m.layout m.family) (s.numbers m.family)) :=
    List.mem_map.mpr ⟨r, complete m.family r, rfl⟩
  have h₁ := canonical_order _ _ _ (mem r) (mem q)
  have h₂ := canonical_order _ _ _ (mem q) (mem r)
  have hrq : NestedRule.read (m.layout m.family) (s.numbers m.family) r =
      NestedRule.read (m.layout m.family) (s.numbers m.family) q := by
    have le₁ := h₁.mp (Int.le_of_eq same)
    have le₂ := h₂.mp (Int.le_of_eq same.symm)
    omega
  exact congrArg s.history.values hrq

theorem table_at_root (refs : (f : F) → List (Reference (I f) (A f)))
    (complete : ∀ f r, r ∈ refs f) (s : m.State) (r : m.Roots) (v : V) :
    m.retainedTable refs s (m.numericKey refs s m.family r) v ↔ m.roots s r = some v := by
  constructor
  · rintro ⟨q, hk, hv⟩
    rw [← m.root_key_injective refs complete s q r hk]
    exact hv
  · intro h
    exact ⟨r, rfl, h⟩

def runtimeKey (refs : (f : F) → List (Reference (I f) (A f))) (s : m.State) :=
  (s.core, m.numericKey refs s, m.retainedTable refs s)

theorem runtime_key_equivalent (refs : (f : F) → List (Reference (I f) (A f)))
    (complete : ∀ f r, r ∈ refs f) (s t : m.State) :
    m.runtimeKey refs s = m.runtimeKey refs t ↔ m.project s = m.project t := by
  constructor
  · intro h
    have parts := Prod.mk.inj h
    have numbers := (Prod.mk.inj parts.2).1
    have table := (Prod.mk.inj parts.2).2
    have patterns : Patterns m.layout s.numbers t.numbers := by
      intro f
      exact (canonical_keys_equivalent (NestedRule.read (m.layout f) (s.numbers f))
        (NestedRule.read (m.layout f) (t.numbers f)) (refs f) (complete f)).mp (congrFun (congrFun numbers f))
    have payloads : m.roots s = m.roots t := by
      funext r
      have point (v : V) : m.roots s r = some v ↔ m.roots t r = some v := by
        rw [← m.table_at_root refs complete s r v, ← m.table_at_root refs complete t r v]
        rw [table, congrFun (congrFun numbers m.family) r]
      cases hs : m.roots s r with
      | none =>
        cases ht : m.roots t r with
        | none => rfl
        | some v => have := (point v).mpr ht; simp_all
      | some v => exact ((point v).mp hs).symm
    exact Quotient.sound (show m.equivalence.r s t from ⟨parts.1, patterns, payloads⟩)
  · intro h
    have same : m.related s t := Quotient.exact h
    have numbers : m.numericKey refs s = m.numericKey refs t := by
      funext f r
      exact (canonical_keys_equivalent (NestedRule.read (m.layout f) (s.numbers f))
        (NestedRule.read (m.layout f) (t.numbers f)) (refs f) (complete f)).mpr (same.2.1 f) r
    unfold runtimeKey
    rw [same.1, numbers]
    congr 2
    funext k v
    apply propext
    simp only [retainedTable, numbers, same.2.2]

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

noncomputable def constrainedConcrete : ConstrainedSystem m.State where
  toSystem := m.concrete
  initSafe s := (m.initObserve s.core (m.roots s)).eval m.layout s.numbers
  constraint s := (m.constraint s.core (m.roots s)).eval m.layout s.numbers
  actionConstraint s t := m.actionConstraint s.core t.core
  actionSafe s t := m.actionObserve s.core t.core

theorem initSafe_related (s t : m.State) (same : m.related s t) :
    m.constrainedConcrete.initSafe s ↔ m.constrainedConcrete.initSafe t := by
  change (m.initObserve s.core (m.roots s)).eval m.layout s.numbers ↔ (m.initObserve t.core (m.roots t)).eval m.layout t.numbers
  rw [same.1, same.2.2]
  exact FamilyTest.congr m.layout s.numbers t.numbers same.2.1 _

theorem constraint_related (s t : m.State) (same : m.related s t) :
    m.constrainedConcrete.constraint s ↔ m.constrainedConcrete.constraint t := by
  change (m.constraint s.core (m.roots s)).eval m.layout s.numbers ↔ (m.constraint t.core (m.roots t)).eval m.layout t.numbers
  rw [same.1, same.2.2]
  exact FamilyTest.congr m.layout s.numbers t.numbers same.2.1 _

theorem related_symm {s t : m.State} (h : m.related s t) : m.related t s :=
  ⟨h.1.symm, (fun f => ⟨fun i j => ((h.2.1 f).1 i j).symm, fun i => ((h.2.1 f).2 i).symm⟩), h.2.2.symm⟩

theorem actionConstraint_related (s t u v : m.State) (hs : m.related s t) (hu : m.related u v) :
    m.constrainedConcrete.actionConstraint s u ↔ m.constrainedConcrete.actionConstraint t v := by
  change m.actionConstraint s.core u.core ↔ m.actionConstraint t.core v.core
  rw [hs.1, hu.1]

theorem actionObserve_related (s t u v : m.State) (hs : m.related s t) (hu : m.related u v) :
    m.constrainedConcrete.actionSafe s u ↔ m.constrainedConcrete.actionSafe t v := by
  change m.actionObserve s.core u.core ↔ m.actionObserve t.core v.core
  rw [hs.1, hu.1]

noncomputable def constrainedReduced : ConstrainedSystem (Quotient m.equivalence) where
  toSystem := m.reduced
  initSafe a := Quotient.liftOn a m.constrainedConcrete.initSafe (fun s t h => propext (m.initSafe_related s t h))
  constraint a := Quotient.liftOn a m.constrainedConcrete.constraint (fun s t h => propext (m.constraint_related s t h))
  actionConstraint a b := Quotient.liftOn₂ a b m.constrainedConcrete.actionConstraint
    (fun a₁ b₁ a₂ b₂ ha hb => propext (m.actionConstraint_related a₁ a₂ b₁ b₂ ha hb))
  actionSafe a b := Quotient.liftOn₂ a b m.constrainedConcrete.actionSafe
    (fun a₁ b₁ a₂ b₂ ha hb => propext (m.actionObserve_related a₁ a₂ b₁ b₂ ha hb))

theorem initObserve_project (s : m.State) :
    m.constrainedConcrete.initSafe s ↔ m.constrainedReduced.initSafe (m.project s) := Iff.rfl

theorem constraint_project (s : m.State) :
    m.constrainedConcrete.constraint s ↔ m.constrainedReduced.constraint (m.project s) := Iff.rfl

theorem actionConstraint_project (s t : m.State) :
    m.constrainedConcrete.actionConstraint s t ↔
      m.constrainedReduced.actionConstraint (m.project s) (m.project t) := by
  change m.actionConstraint s.core t.core ↔
    Quotient.liftOn₂ (m.project s) (m.project t) m.constrainedConcrete.actionConstraint
      (fun a₁ b₁ a₂ b₂ ha hb => propext (m.actionConstraint_related a₁ a₂ b₁ b₂ ha hb))
  unfold project Quotient.liftOn₂ Quotient.lift₂ Quotient.lift
  rfl

theorem actionObserve_project (s t : m.State) :
    m.constrainedConcrete.actionSafe s t ↔
      m.constrainedReduced.actionSafe (m.project s) (m.project t) := by
  change m.actionObserve s.core t.core ↔
    Quotient.liftOn₂ (m.project s) (m.project t) m.constrainedConcrete.actionSafe
      (fun a₁ b₁ a₂ b₂ ha hb => propext (m.actionObserve_related a₁ a₂ b₁ b₂ ha hb))
  unfold project Quotient.liftOn₂ Quotient.lift₂ Quotient.lift
  rfl

theorem constrained_certificate :
    ConstrainedCertificate m.constrainedConcrete m.constrainedReduced m.project :=
  constrainedOfProjectedAction m.certificate
    m.initObserve_project m.constraint_project m.actionConstraint_project m.actionObserve_project
end Model
end TlxOptimization.LiveRule
