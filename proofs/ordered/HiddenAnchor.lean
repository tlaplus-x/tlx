/- Standalone disproof of the former unanchored key for HiddenAnchor.tla.
This is a manually written regression, separate from generated certificates. -/
set_option autoImplicit false
namespace HiddenAnchor

structure State where
  clock : Nat
  bad : Bool
  deriving DecidableEq

def initial : State := ⟨1, false⟩
def step (s : State) : State :=
  ⟨s.clock + 1, if [s.clock, 1].eraseDups.length = 2 then true else s.bad⟩

-- With no fixed anchor and one positive allocation value, the old rank was
-- always one. Only bad distinguished keys; the other tuple fields were fixed.
def lostKey (s : State) : Bool := s.bad

theorem first_successor_is_merged : lostKey (step initial) = lostKey initial := by decide

theorem concrete_violation : (step (step initial)).bad = true := by decide

-- No reduced relation can satisfy the required successor correspondence for
-- this key. Representatives (1, false) and (2, false) have different successors.
theorem no_successor_correspondence :
    ¬ ∃ reduced : Bool → Bool → Prop,
      ∀ s, 1 ≤ s.clock → ∀ b, reduced (lostKey s) b ↔ ∃ t, t = step s ∧ lostKey t = b := by
  rintro ⟨reduced, corresponds⟩
  have second : reduced false true :=
    (corresponds ⟨2, false⟩ (by decide) true).mpr ⟨step ⟨2, false⟩, rfl, by decide⟩
  obtain ⟨t, ht, hk⟩ := (corresponds ⟨1, false⟩ (by decide) true).mp second
  subst t
  have impossible : lostKey (step ⟨1, false⟩) ≠ true := by decide
  exact impossible hk

#print axioms first_successor_is_merged
#print axioms concrete_violation
#print axioms no_successor_correspondence
end HiddenAnchor
