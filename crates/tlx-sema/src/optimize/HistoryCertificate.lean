/- Parametric semantics of the history rule IR. History-free HIR leaves
are interpreted by parameters; the lowering and their totality remain trusted.
This library constructs certificates, without assuming any certificate fields. -/
set_option autoImplicit false
namespace TlxOptimization.HistoryRule
open TlxOptimization

-- Zero-based occurrence positions correspond to TLA+'s indices minus one.
inductive At {E : Type} : History E → Nat → E → Prop
  | last (h : History E) (e : E) : At (.append h e) h.length e
  | earlier {h i e} (x : E) : At h i e → At (.append h x) i e

variable {E : Type}

theorem at_bound {h : History E} {i : Nat} {e : E} (a : At h i e) : i < h.length := by
  induction a with
  | last => simp [History.length]
  | earlier _ _ ih => simp only [History.length]; omega

theorem at_exists (h : History E) (i : Nat) (hi : i < h.length) : ∃ e, At h i e := by
  induction h with
  | empty => simp [History.length] at hi
  | append h x ih =>
    by_cases old : i < h.length
    · obtain ⟨e, he⟩ := ih old
      exact ⟨e, .earlier x he⟩
    · have eq : i = h.length := by simp only [History.length] at hi; omega
      subst i
      exact ⟨x, .last h x⟩

theorem at_unique {h : History E} {i : Nat} {e f : E} (a : At h i e) (b : At h i f) : e = f := by
  induction a with
  | last h x =>
    cases b with
    | last => rfl
    | earlier _ b => have hb := at_bound b; omega
  | earlier x a ih =>
    cases b with
    | last => have ha := at_bound a; omega
    | earlier _ b => exact ih b

theorem seen_iff_at (h : History E) (e : E) :
    h.seen e ↔ ∃ i, At h i e := by
  induction h with
  | empty =>
    constructor
    · exact False.elim
    · rintro ⟨i, a⟩; cases a
  | append h x ih =>
    constructor
    · intro hs
      cases hs with
      | inl hs => obtain ⟨i, a⟩ := ih.mp hs; exact ⟨i, .earlier x a⟩
      | inr he => subst e; exact ⟨h.length, .last h x⟩
    · rintro ⟨i, a⟩
      cases a with
      | last => exact Or.inr rfl
      | earlier _ a => exact Or.inl (ih.mpr ⟨_, a⟩)

def seenPrefix (h : History E) (i : Nat) (e : E) : Prop :=
  ∃ j, j ≤ i ∧ At h j e

theorem prefix_old (h : History E) (x : E) (i : Nat) (hi : i < h.length) :
    seenPrefix (.append h x) i = seenPrefix h i := by
  funext e
  apply propext
  constructor
  · rintro ⟨j, hj, a⟩
    cases a with
    | last => omega
    | earlier _ a => exact ⟨j, hj, a⟩
  · rintro ⟨j, hj, a⟩
    exact ⟨j, hj, .earlier x a⟩

theorem prefix_last (h : History E) (x : E) :
    seenPrefix (.append h x) h.length = History.seen (.append h x) := by
  funext e
  apply propext
  constructor
  · rintro ⟨j, _, a⟩; exact (seen_iff_at _ _).mpr ⟨j, a⟩
  · intro hs
    obtain ⟨j, a⟩ := (seen_iff_at _ _).mp hs
    have hb := at_bound a
    exact ⟨j, by simp only [History.length] at hb; omega, a⟩

def indexed (q : E → (E → Prop) → Prop) (h : History E) : Prop :=
  ∀ i e, At h i e → q e (seenPrefix h i)

-- The existential monitor is the complement of a universal monitor over ¬q.
-- Its witness belongs to its original prefix, not the final element set.
theorem exists_iff_not_indexed_not (q : E → (E → Prop) → Prop) (h : History E) :
    (∃ i e, At h i e ∧ q e (seenPrefix h i)) ↔
      ¬ indexed (fun e seen => ¬ q e seen) h := by
  classical
  simp only [indexed, not_forall, not_imp, not_not]

theorem indexed_append (q : E → (E → Prop) → Prop) (h : History E) (x : E) :
    indexed q (.append h x) ↔ indexed q h ∧ q x (History.seen (.append h x)) := by
  constructor
  · intro hp
    constructor
    · intro i e a
      have he := hp i e (.earlier x a)
      rw [prefix_old h x i (at_bound a)] at he
      exact he
    · have he := hp h.length x (.last h x)
      rw [prefix_last] at he
      exact he
  · rintro ⟨hp, hx⟩ i e a
    cases a with
    | last => simpa only [prefix_last] using hx
    | earlier _ a =>
      rw [prefix_old h x i (at_bound a)]
      exact hp i e a

theorem indexed_iff_valid (q : E → (E → Prop) → Prop) (h : History E) : indexed q h ↔ History.valid q h := by
  induction h with
  | empty =>
    constructor
    · intro _; trivial
    · intro _ i e a; cases a
  | append h x ih =>
    rw [indexed_append, History.valid, ih]


abbrev Summary (E I : Type) := (E → Prop) × (I → Prop)

def indexedSummary {I : Type} (q : I → E → (E → Prop) → Prop)
    (h : History E) : Summary E I := (h.seen, fun i => indexed (q i) h)

theorem indexedSummary_eq {I : Type} (q : I → E → (E → Prop) → Prop)
    (h : History E) : indexedSummary q h = History.summary q h := by
  apply Prod.ext
  · rfl
  · funext i; exact propext (indexed_iff_valid (q i) h)

theorem empty_iff_no_seen (h : History E) : h = .empty ↔ ¬ ∃ e, h.seen e := by
  cases h with
  | empty => simp [History.seen]
  | append h e =>
    constructor
    · intro impossible; cases impossible
    · intro noSeen; exact False.elim (noSeen ⟨e, Or.inr rfl⟩)

-- All finite resets and append chains, including branches selected by a
-- history-free condition, have the same transfer on summary-equivalent logs.
inductive Transfer (E : Type) where
  | keep
  | reset (history : History E)
  | append (previous : Transfer E) (event : E)

def Transfer.concrete : Transfer E → History E → History E
  | .keep, h => h
  | .reset h, _ => h
  | .append t e, h => .append (t.concrete h) e

def Transfer.reduced {I : Type} (q : I → E → (E → Prop) → Prop) :
    Transfer E → Summary E I → Summary E I
  | .keep, s => s
  | .reset h, _ => History.summary q h
  | .append t e, s => History.advance q (t.reduced q s) e

theorem Transfer.commutes {I : Type} (q : I → E → (E → Prop) → Prop)
    (t : Transfer E) (h : History E) :
    History.summary q (t.concrete h) = t.reduced q (History.summary q h) := by
  induction t with
  | keep => rfl
  | reset => rfl
  | append t e ih =>
    change History.advance q (History.summary q (t.concrete h)) e = _
    rw [ih]; rfl

-- W carries the branch number and its local-binding environment. C contains
-- only retained variables. No semantic parameter has access to the history.
structure Model (C E I W : Type) where
  predicate : I → E → (E → Prop) → Prop
  initial : C → W → Prop
  seed : C → W → History E
  step : C → C → W → Prop
  transfer : C → C → W → Transfer E
  observe : C → Summary E I → Prop

namespace Model
variable {C E I W : Type} (m : Model C E I W)

def concrete : System (C × History E) where
  initial s := ∃ w, m.initial s.1 w ∧ s.2 = m.seed s.1 w
  next s t := ∃ w, m.step s.1 t.1 w ∧ t.2 = (m.transfer s.1 t.1 w).concrete s.2
  safe s := m.observe s.1 (indexedSummary m.predicate s.2)

def reduced : System (C × Summary E I) where
  initial s := ∃ w, m.initial s.1 w ∧ s.2 = History.summary m.predicate (m.seed s.1 w)
  next s t := ∃ w, m.step s.1 t.1 w ∧ t.2 = (m.transfer s.1 t.1 w).reduced m.predicate s.2
  safe s := m.observe s.1 s.2

def project (s : C × History E) : C × Summary E I :=
  (s.1, History.summary m.predicate s.2)

theorem certificate : Certificate m.concrete m.reduced m.project := by
  constructor
  · intro a
    constructor
    · rintro ⟨w, hw, ha⟩
      refine ⟨(a.1, m.seed a.1 w), ⟨w, hw, rfl⟩, ?_⟩
      exact Prod.ext rfl ha.symm
    · rintro ⟨s, ⟨w, hw, hs⟩, he⟩
      subst a
      exact ⟨w, hw, congrArg (History.summary m.predicate) hs⟩
  · intro s a
    constructor
    · rintro ⟨w, hw, ha⟩
      refine ⟨(a.1, (m.transfer s.1 a.1 w).concrete s.2), ⟨w, hw, rfl⟩, ?_⟩
      apply Prod.ext
      · rfl
      · exact (Transfer.commutes _ _ _).trans ha.symm
    · rintro ⟨t, ⟨w, hw, ht⟩, he⟩
      subst a
      refine ⟨w, hw, ?_⟩
      change History.summary m.predicate t.2 = _
      rw [ht, Transfer.commutes]
      rfl
  · intro s
    change m.observe s.1 (indexedSummary m.predicate s.2) ↔ _
    rw [indexedSummary_eq]; rfl

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

theorem deadlock_preserved (s : C × History E) :
    (¬ ∃ t, m.concrete.next s t) ↔ (¬ ∃ a, m.reduced.next (m.project s) a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s a).mp ha
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨m.project t, (m.certificate.next s (m.project t)).mpr ⟨t, ht, rfl⟩⟩
end Model
end TlxOptimization.HistoryRule
