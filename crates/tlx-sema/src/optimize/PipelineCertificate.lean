/- Closed applications discharge these obligations from the emitted before/after
IR. Restriction to reachable states accommodates inductive constant propagation. -/
set_option autoImplicit false
namespace TlxOptimization.PipelineRule
open TlxOptimization

def reachableSystem {S : Type} (m : System S) : System {s // Reachable m s} where
  initial s := m.initial s.val
  next s t := m.next s.val t.val
  safe s := m.safe s.val

theorem reachableSystem_all {S : Type} (m : System S) (s : {s // Reachable m s}) :
    Reachable (reachableSystem m) s := by
  obtain ⟨s, hs⟩ := s
  induction hs with
  | initial hi => exact .initial hi
  | @step s t hs hn ih => exact .step ih hn

theorem reachableSystem_safety {S : Type} (m : System S) :
    (∀ s, Reachable m s → m.safe s) ↔
    (∀ s, Reachable (reachableSystem m) s → (reachableSystem m).safe s) := by
  constructor
  · intro h s _
    exact h s.val s.property
  · intro h s hs
    exact h ⟨s, hs⟩ (reachableSystem_all m ⟨s, hs⟩)

structure Application {S A : Type} (b : System S) (a : System A) (p : S → A) where
  valid : S → Prop
  initialValid : ∀ s, b.initial s → valid s
  closed : ∀ s t, valid s → b.next s t → valid t
  initial : ∀ y, a.initial y ↔ ∃ x, b.initial x ∧ p x = y
  forward : ∀ s t, valid s → b.next s t → a.next (p s) (p t)
  backward : ∀ s y, valid s → a.next (p s) y → ∃ t, b.next s t ∧ p t = y
  observe : ∀ s, valid s → (b.safe s ↔ a.safe (p s))

namespace Application
variable {S A : Type} {b : System S} {a : System A} {p : S → A}
variable (c : Application b a p)
include c

theorem valid_reachable {s} (hs : Reachable b s) : c.valid s := by
  induction hs with
  | initial hi => exact c.initialValid _ hi
  | step _ hn ih => exact c.closed _ _ ih hn

theorem project_reachable {s} (hs : Reachable b s) : Reachable a (p s) := by
  induction hs with
  | initial hi => exact .initial ((c.initial _).mpr ⟨_, hi, rfl⟩)
  | step hs hn ih => exact .step ih (c.forward _ _ (c.valid_reachable hs) hn)

def project (s : {s // Reachable b s}) : {s // Reachable a s} :=
  ⟨p s.val, c.project_reachable s.property⟩

theorem certificate : Certificate (reachableSystem b) (reachableSystem a) c.project := by
  constructor
  · intro y
    constructor
    · intro hy
      obtain ⟨x, hx, hp⟩ := (c.initial y.val).mp hy
      exact ⟨⟨x, .initial hx⟩, hx, Subtype.ext hp⟩
    · rintro ⟨x, hx, he⟩
      exact (c.initial y.val).mpr ⟨x.val, hx, congrArg Subtype.val he⟩
  · intro s y
    constructor
    · intro hy
      obtain ⟨t, ht, hp⟩ := c.backward s.val y.val (c.valid_reachable s.property) hy
      exact ⟨⟨t, .step s.property ht⟩, ht, Subtype.ext hp⟩
    · rintro ⟨t, ht, he⟩
      have h := c.forward s.val t.val (c.valid_reachable s.property) ht
      change a.next (p s.val) y.val
      rw [← congrArg Subtype.val he]
      exact h
  · intro s
    exact c.observe s.val (c.valid_reachable s.property)
end Application

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
end TlxOptimization.PipelineRule
