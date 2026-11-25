/-
Shared algebra for tlx state projections.

These theorems do not certify the Rust recognizer or the translation of TLA+
into HIR. In particular, the existence of a Certificate below must be proved
for a formalized model before safety_iff is a model-level preservation proof.
No such Certificate is asserted by recording a transformation in this file.
-/
namespace TlxOptimization

structure System (State : Type) where
  initial : State → Prop
  next : State → State → Prop
  safe : State → Prop

inductive Reachable {State : Type} (m : System State) : State → Prop
  | initial {s} : m.initial s → Reachable m s
  | step {s t} : Reachable m s → m.next s t → Reachable m t

structure Certificate {S A : Type}
    (before : System S) (after : System A) (project : S → A) : Prop where
  initial : ∀ a, after.initial a ↔ ∃ s, before.initial s ∧ project s = a
  next : ∀ s a, after.next (project s) a ↔
    ∃ t, before.next s t ∧ project t = a
  observe : ∀ s, before.safe s ↔ after.safe (project s)

theorem compose {S A T : Type} {b : System S} {a : System A} {t : System T}
    {p : S → A} {q : A → T} (first : Certificate b a p) (second : Certificate a t q) :
    Certificate b t (fun s => q (p s)) := by
  constructor
  · intro y
    constructor
    · intro hy
      obtain ⟨x, hx, he⟩ := (second.initial y).mp hy
      obtain ⟨s, hs, hp⟩ := (first.initial x).mp hx
      exact ⟨s, hs, (congrArg q hp).trans he⟩
    · rintro ⟨s, hs, rfl⟩
      exact (second.initial _).mpr ⟨p s, (first.initial _).mpr ⟨s, hs, rfl⟩, rfl⟩
  · intro s y
    constructor
    · intro hy
      obtain ⟨x, hx, he⟩ := (second.next (p s) y).mp hy
      obtain ⟨u, hu, hp⟩ := (first.next s x).mp hx
      exact ⟨u, hu, (congrArg q hp).trans he⟩
    · rintro ⟨u, hu, rfl⟩
      exact (second.next _ _).mpr ⟨p u, (first.next _ _).mpr ⟨u, hu, rfl⟩, rfl⟩
  · intro s
    exact (first.observe s).trans (second.observe (p s))

theorem reachable_forward {S A : Type} {b : System S} {a : System A}
    {p : S → A} (c : Certificate b a p) {s} (h : Reachable b s) :
    Reachable a (p s) := by
  induction h with
  | initial hi => exact .initial ((c.initial _).mpr ⟨_, hi, rfl⟩)
  | step _ hn ih => exact .step ih ((c.next _ _).mpr ⟨_, hn, rfl⟩)

theorem reachable_backward {S A : Type} {b : System S} {a : System A}
    {p : S → A} (c : Certificate b a p) {t} (h : Reachable a t) :
    ∃ s, Reachable b s ∧ p s = t := by
  induction h with
  | initial hi =>
    obtain ⟨s, hs, he⟩ := (c.initial _).mp hi
    exact ⟨s, .initial hs, he⟩
  | @step x y _ hn ih =>
    obtain ⟨s, hs, he⟩ := ih
    have hn' : a.next (p s) y := by rw [he]; exact hn
    obtain ⟨u, hu, he'⟩ := (c.next _ _).mp hn'
    exact ⟨u, .step hs hu, he'⟩

theorem safety_iff {S A : Type} {b : System S} {a : System A}
    {p : S → A} (c : Certificate b a p) :
    (∀ s, Reachable b s → b.safe s) ↔ (∀ t, Reachable a t → a.safe t) := by
  constructor
  · intro hb t ht
    obtain ⟨s, hs, he⟩ := reachable_backward c ht
    rw [← he]
    exact (c.observe s).mp (hb s hs)
  · intro ha s hs
    exact (c.observe s).mpr (ha (p s) (reachable_forward c hs))

-- TLA+'s [Next]_vars additionally permits unchanged-state steps. Those
-- steps do not add reachable states; deadlock checks still concern Next.
def withStuttering {S : Type} (m : System S) : System S :=
  { m with next := fun s t => m.next s t ∨ t = s }

theorem stuttering_reachable_iff {S : Type} (m : System S) (s : S) :
    Reachable (withStuttering m) s ↔ Reachable m s := by
  constructor
  · intro h
    induction h with
    | initial hi => exact .initial hi
    | step _ hn ih =>
      cases hn with
      | inl hn => exact .step ih hn
      | inr he => cases he; exact ih
  · intro h
    induction h with
    | initial hi => exact .initial hi
    | step _ hn ih => exact .step ih (Or.inl hn)

-- Append-oriented lists avoid an implicit change of history order.
inductive History (Event : Type) where
  | empty
  | append (previous : History Event) (event : Event)

namespace History
variable {E : Type}

def length : History E → Nat
  | .empty => 0
  | .append h _ => length h + 1

theorem length_append_congruent {h k : History E} (same : length h = length k)
    (x y : E) : length (.append h x) = length (.append k y) := by
  exact congrArg (fun n => n + 1) same

def seen : History E → E → Prop
  | .empty => fun _ => False
  | .append h e => fun x => seen h x ∨ x = e

-- Q sees a value and the set of values in its inclusive prefix. Neither
-- positions nor multiplicity are available to Q.
def valid (q : E → (E → Prop) → Prop) : History E → Prop
  | .empty => True
  | .append h e => valid q h ∧ q e (seen (.append h e))

def summary {I : Type} (q : I → E → (E → Prop) → Prop) (h : History E) :=
  (seen h, fun i => valid (q i) h)

def advance {I : Type} (q : I → E → (E → Prop) → Prop)
    (s : (E → Prop) × (I → Prop)) (e : E) :=
  (fun x => s.1 x ∨ x = e, fun i => s.2 i ∧ q i e (fun x => s.1 x ∨ x = e))

theorem summary_append {I : Type} (q : I → E → (E → Prop) → Prop)
    (h : History E) (e : E) :
    summary q (.append h e) = advance q (summary q h) e := rfl

theorem summary_append_congruent {I : Type} (q : I → E → (E → Prop) → Prop)
    {h k : History E} (same : summary q h = summary q k) (e : E) :
    summary q (.append h e) = summary q (.append k e) := by
  exact congrArg (fun s => advance q s e) same
end History

-- Whole-variable projection: any observation factoring through the retained
-- coordinates is constant on each projection class.
def retain {V : Type} (indices : List Nat) (s : Nat → V) : List V := indices.map s

theorem retained_observation {V O : Type} (indices : List Nat) (f : List V → O)
    {s t : Nat → V} (same : retain indices s = retain indices t) :
    f (retain indices s) = f (retain indices t) := congrArg f same

-- Phase-dependent field erasure. Transition and observation factorization
-- remain model-specific obligations; idempotence alone does not prove them.
def mask {K V : Type} (live : K → Bool) (s : K → Option V) : K → Option V :=
  fun k => if live k then s k else none

theorem mask_idempotent {K V : Type} (live : K → Bool) (s : K → Option V) :
    mask live (mask live s) = mask live s := by
  funext k
  cases h : live k <;> simp [mask, h]

/- Constrained checking algebra matching `tlx-runtime`:
   - Every `initial` state has `safe` and `initSafe` checked (even if `¬ constraint s`).
   - `AdmittedReachable` starts from `initial ∧ constraint` and advances along
     `next s t ∧ constraint t ∧ actionConstraint s t`.
   - Every `next` successor `t` of an `AdmittedReachable` state `s` has `safe t`
     and `actionSafe s t` checked (even if `¬ constraint t` or `¬ actionConstraint s t`).
   - Deadlock checks plain `next` on `AdmittedReachable` states. -/
structure ConstrainedSystem (State : Type) extends System State where
  initSafe : State → Prop
  constraint : State → Prop
  actionConstraint : State → State → Prop
  actionSafe : State → State → Prop

inductive AdmittedReachable {State : Type} (m : ConstrainedSystem State) : State → Prop
  | initial {s} : m.initial s → m.constraint s → AdmittedReachable m s
  | step {s t} : AdmittedReachable m s → m.next s t → m.constraint t → m.actionConstraint s t → AdmittedReachable m t

theorem admitted_implies_reachable {State : Type} (m : ConstrainedSystem State) {s : State}
    (h : AdmittedReachable m s) : Reachable m.toSystem s := by
  induction h with
  | initial hi _ => exact .initial hi
  | step _ hn _ _ ih => exact .step ih hn

def ConstrainedSafe {State : Type} (m : ConstrainedSystem State) : Prop :=
  (∀ s, m.initial s → m.safe s ∧ m.initSafe s) ∧
  (∀ s t, AdmittedReachable m s → m.next s t → m.safe t ∧ m.actionSafe s t)

structure ConstrainedCertificate {S A : Type}
    (before : ConstrainedSystem S) (after : ConstrainedSystem A) (project : S → A) : Prop where
  initial : ∀ a, after.initial a ↔ ∃ s, before.initial s ∧ project s = a
  next : ∀ s a, after.next (project s) a ↔
    ∃ t, before.next s t ∧ project t = a
  observe : ∀ s, before.safe s ↔ after.safe (project s)
  initObserve : ∀ s, before.initSafe s ↔ after.initSafe (project s)
  constraint : ∀ s, before.constraint s ↔ after.constraint (project s)
  admittedStep : ∀ s a,
    (after.next (project s) a ∧ after.constraint a ∧ after.actionConstraint (project s) a) ↔
    ∃ t, before.next s t ∧ before.constraint t ∧ before.actionConstraint s t ∧ project t = a
  actionObserve : ∀ s a,
    (∀ t, before.next s t → project t = a → before.actionSafe s t) ↔
    (after.next (project s) a → after.actionSafe (project s) a)

theorem ConstrainedCertificate.toCertificate {S A : Type}
    {before : ConstrainedSystem S} {after : ConstrainedSystem A} {project : S → A}
    (c : ConstrainedCertificate before after project) :
    Certificate before.toSystem after.toSystem project :=
  ⟨c.initial, c.next, c.observe⟩

theorem composeConstrained {S A T : Type}
    {b : ConstrainedSystem S} {a : ConstrainedSystem A} {t : ConstrainedSystem T}
    {p : S → A} {q : A → T}
    (first : ConstrainedCertificate b a p) (second : ConstrainedCertificate a t q) :
    ConstrainedCertificate b t (fun s => q (p s)) := by
  have base := compose first.toCertificate second.toCertificate
  refine ⟨base.initial, base.next, base.observe, ?_, ?_, ?_, ?_⟩
  · intro s
    exact (first.initObserve s).trans (second.initObserve (p s))
  · intro s
    exact (first.constraint s).trans (second.constraint (p s))
  · intro s y
    constructor
    · intro hy
      obtain ⟨x, hnx, hcx, hacx, hqx⟩ := (second.admittedStep (p s) y).mp hy
      obtain ⟨u, hnu, hcu, hacu, hpu⟩ := (first.admittedStep s x).mp ⟨hnx, hcx, hacx⟩
      exact ⟨u, hnu, hcu, hacu, (congrArg q hpu).trans hqx⟩
    · rintro ⟨u, hnu, hcu, hacu, rfl⟩
      have ha := (first.admittedStep s (p u)).mpr ⟨u, hnu, hcu, hacu, rfl⟩
      exact (second.admittedStep (p s) (q (p u))).mpr ⟨p u, ha.1, ha.2.1, ha.2.2, rfl⟩
  · intro s y
    constructor
    · intro h hty
      refine (second.actionObserve (p s) y).mp ?_ hty
      intro x hax hqx
      refine (first.actionObserve s x).mp ?_ hax
      intro u hbu hpu
      exact h u hbu ((congrArg q hpu).trans hqx)
    · intro h u hbu hqu
      have hax : a.next (p s) (p u) := (first.next s (p u)).mpr ⟨u, hbu, rfl⟩
      have hty : t.next (q (p s)) y := (second.next (p s) y).mpr ⟨p u, hax, hqu⟩
      have has := (second.actionObserve (p s) y).mpr h (p u) hax hqu
      exact (first.actionObserve s (p u)).mpr (fun _ => has) u hbu rfl

theorem constrainedOfStatePreds {S A : Type}
    {b : ConstrainedSystem S} {a : ConstrainedSystem A} {p : S → A}
    (base : Certificate b.toSystem a.toSystem p)
    (hInit : ∀ s, b.initSafe s ↔ a.initSafe (p s))
    (hCons : ∀ s, b.constraint s ↔ a.constraint (p s))
    (hbAC : ∀ s t, b.actionConstraint s t)
    (haAC : ∀ x y, a.actionConstraint x y)
    (hbAS : ∀ s t, b.actionSafe s t)
    (haAS : ∀ x y, a.actionSafe x y) :
    ConstrainedCertificate b a p := by
  refine ⟨base.initial, base.next, base.observe, hInit, hCons, ?_, ?_⟩
  · intro s y
    constructor
    · rintro ⟨hn, hc, _⟩
      obtain ⟨t, hbt, rfl⟩ := (base.next s y).mp hn
      exact ⟨t, hbt, (hCons t).mpr hc, hbAC s t, rfl⟩
    · rintro ⟨t, hbt, hct, _, rfl⟩
      exact ⟨(base.next s (p t)).mpr ⟨t, hbt, rfl⟩, (hCons t).mp hct, haAC (p s) (p t)⟩
  · intro s y
    constructor
    · intro _ _; exact haAS (p s) y
    · intro _ t _ _; exact hbAS s t

/- Projection-wide action correspondence. Once a base certificate is known,
   the constrained obligations follow from the four projection equalities: a
   reduced edge's concrete successor and its projection equality are supplied
   by `base.next`, and rewriting by that equality transfers the predicates in
   either direction. Each projection family proves its own equalities. -/
theorem constrainedOfProjectedAction {S A : Type}
    {b : ConstrainedSystem S} {a : ConstrainedSystem A} {p : S → A}
    (base : Certificate b.toSystem a.toSystem p)
    (hInit : ∀ s, b.initSafe s ↔ a.initSafe (p s))
    (hCons : ∀ s, b.constraint s ↔ a.constraint (p s))
    (hAction : ∀ s t, b.actionConstraint s t ↔ a.actionConstraint (p s) (p t))
    (hSafe : ∀ s t, b.actionSafe s t ↔ a.actionSafe (p s) (p t)) :
    ConstrainedCertificate b a p := by
  refine ⟨base.initial, base.next, base.observe, hInit, hCons, ?_, ?_⟩
  · intro s x
    constructor
    · rintro ⟨hnext, hcons, haction⟩
      obtain ⟨t, hstep, hproject⟩ := (base.next s x).mp hnext
      subst hproject
      exact ⟨t, hstep, (hCons t).mpr hcons, (hAction s t).mpr haction, rfl⟩
    · rintro ⟨t, hstep, hcons, haction, hproject⟩
      subst hproject
      exact ⟨(base.next s (p t)).mpr ⟨t, hstep, rfl⟩, (hCons t).mp hcons, (hAction s t).mp haction⟩
  · intro s x
    constructor
    · intro hall hnext
      obtain ⟨t, hstep, hproject⟩ := (base.next s x).mp hnext
      subst hproject
      exact (hSafe s t).mp (hall t hstep rfl)
    · intro hall t hstep hproject
      subst hproject
      exact (hSafe s t).mpr (hall ((base.next s (p t)).mpr ⟨t, hstep, rfl⟩))

theorem admitted_reachable_forward {S A : Type}
    {b : ConstrainedSystem S} {a : ConstrainedSystem A} {p : S → A}
    (c : ConstrainedCertificate b a p) {s} (h : AdmittedReachable b s) :
    AdmittedReachable a (p s) := by
  induction h with
  | initial hi hc =>
    exact .initial ((c.initial _).mpr ⟨_, hi, rfl⟩) ((c.constraint _).mp hc)
  | step _ hn hc hac ih =>
    have hstep := (c.admittedStep _ _).mpr ⟨_, hn, hc, hac, rfl⟩
    exact .step ih hstep.1 hstep.2.1 hstep.2.2

theorem admitted_reachable_backward {S A : Type}
    {b : ConstrainedSystem S} {a : ConstrainedSystem A} {p : S → A}
    (c : ConstrainedCertificate b a p) {y} (h : AdmittedReachable a y) :
    ∃ s, AdmittedReachable b s ∧ p s = y := by
  induction h with
  | initial hi hc =>
    obtain ⟨s, hs, rfl⟩ := (c.initial _).mp hi
    exact ⟨s, .initial hs ((c.constraint s).mpr hc), rfl⟩
  | @step x y _ hn hc hac ih =>
    obtain ⟨s, hs, rfl⟩ := ih
    obtain ⟨u, hnu, hcu, hacu, hpu⟩ := (c.admittedStep s y).mp ⟨hn, hc, hac⟩
    exact ⟨u, .step hs hnu hcu hacu, hpu⟩

theorem constrained_safety_iff {S A : Type}
    {b : ConstrainedSystem S} {a : ConstrainedSystem A} {p : S → A}
    (c : ConstrainedCertificate b a p) :
    ConstrainedSafe b ↔ ConstrainedSafe a := by
  constructor
  · rintro ⟨hbInit, hbStep⟩
    constructor
    · intro y hy
      obtain ⟨s, hs, rfl⟩ := (c.initial y).mp hy
      have h := hbInit s hs
      exact ⟨(c.observe s).mp h.1, (c.initObserve s).mp h.2⟩
    · intro x y hx hxy
      obtain ⟨s, hs, rfl⟩ := admitted_reachable_backward c hx
      constructor
      · obtain ⟨t, ht, rfl⟩ := (c.next s y).mp hxy
        exact (c.observe t).mp (hbStep s t hs ht).1
      · exact (c.actionObserve s y).mp (fun t ht _ => (hbStep s t hs ht).2) hxy
  · rintro ⟨haInit, haStep⟩
    constructor
    · intro s hs
      have h := haInit (p s) ((c.initial _).mpr ⟨s, hs, rfl⟩)
      exact ⟨(c.observe s).mpr h.1, (c.initObserve s).mpr h.2⟩
    · intro s t hs hst
      have hps := admitted_reachable_forward c hs
      have hnext := (c.next s (p t)).mpr ⟨t, hst, rfl⟩
      have h := haStep (p s) (p t) hps hnext
      exact ⟨(c.observe t).mpr h.1, (c.actionObserve s (p t)).mpr (fun _ => h.2) t hst rfl⟩

theorem constrained_init_counterexample_lifts {S A : Type}
    {b : ConstrainedSystem S} {a : ConstrainedSystem A} {p : S → A}
    (c : ConstrainedCertificate b a p) {x}
    (hx : a.initial x) (bad : ¬ (a.safe x ∧ a.initSafe x)) :
    ∃ s, b.initial s ∧ p s = x ∧ ¬ (b.safe s ∧ b.initSafe s) := by
  obtain ⟨s, hs, rfl⟩ := (c.initial x).mp hx
  refine ⟨s, hs, rfl, fun h => bad ⟨(c.observe s).mp h.1, (c.initObserve s).mp h.2⟩⟩

theorem constrained_step_counterexample_lifts {S A : Type}
    {b : ConstrainedSystem S} {a : ConstrainedSystem A} {p : S → A}
    (c : ConstrainedCertificate b a p) {x y}
    (hx : AdmittedReachable a x) (hxy : a.next x y) (bad : ¬ (a.safe y ∧ a.actionSafe x y)) :
    ∃ s t, AdmittedReachable b s ∧ b.next s t ∧ p s = x ∧ p t = y ∧ ¬ (b.safe t ∧ b.actionSafe s t) := by
  obtain ⟨s, hs, rfl⟩ := admitted_reachable_backward c hx
  by_cases hsafe : a.safe y
  · have hnotact : ¬ a.actionSafe (p s) y := fun ha => bad ⟨hsafe, ha⟩
    have hnotall : ¬ ∀ t, b.next s t → p t = y → b.actionSafe s t := fun hall =>
      hnotact ((c.actionObserve s y).mp hall hxy)
    apply Classical.byContradiction
    intro hnone
    apply hnotall
    intro t ht hpt
    apply Classical.byContradiction
    intro hbad
    exact hnone ⟨s, t, hs, ht, rfl, hpt, fun h => hbad h.2⟩
  · obtain ⟨t, ht, rfl⟩ := (c.next s y).mp hxy
    exact ⟨s, t, hs, ht, rfl, rfl, fun h => hsafe ((c.observe t).mp h.1)⟩

theorem constrained_deadlock_iff {S A : Type}
    {b : ConstrainedSystem S} {a : ConstrainedSystem A} {p : S → A}
    (c : ConstrainedCertificate b a p) :
    (∃ s, AdmittedReachable b s ∧ ¬ ∃ t, b.next s t) ↔
    (∃ x, AdmittedReachable a x ∧ ¬ ∃ y, a.next x y) := by
  constructor
  · rintro ⟨s, hs, hno⟩
    refine ⟨p s, admitted_reachable_forward c hs, fun ⟨y, hy⟩ => ?_⟩
    obtain ⟨t, ht, _⟩ := (c.next s y).mp hy
    exact hno ⟨t, ht⟩
  · rintro ⟨x, hx, hno⟩
    obtain ⟨s, hs, rfl⟩ := admitted_reachable_backward c hx
    refine ⟨s, hs, fun ⟨t, ht⟩ => ?_⟩
    exact hno ⟨p t, (c.next s (p t)).mpr ⟨t, ht, rfl⟩⟩

theorem const_subst_certificate {S A V : Type} {k : Nat}
    (sys : (Fin k → V) → System S) (after : System A) (project : S → A)
    (constVals targetVals : Fin k → V)
    (hSubst : ∀ i : Fin k, constVals i = targetVals i)
    (cert : Certificate (sys targetVals) after project) :
    Certificate (sys constVals) after project := by
  have hEq : constVals = targetVals := funext hSubst
  rw [hEq]
  exact cert

theorem const_subst_constrained_certificate {S A V : Type} {k : Nat}
    (sys : (Fin k → V) → ConstrainedSystem S) (after : ConstrainedSystem A) (project : S → A)
    (constVals targetVals : Fin k → V)
    (hSubst : ∀ i : Fin k, constVals i = targetVals i)
    (cert : ConstrainedCertificate (sys targetVals) after project) :
    ConstrainedCertificate (sys constVals) after project := by
  have hEq : constVals = targetVals := funext hSubst
  rw [hEq]
  exact cert

end TlxOptimization
