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

end TlxOptimization
