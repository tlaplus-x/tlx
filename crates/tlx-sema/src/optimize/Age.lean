/- Capped ages of mathematical natural-number clocks. This algebra does not
model machine-integer overflow or certify HIR applicability/composition. -/
set_option autoImplicit false
namespace TlxOptimization.Age

def cap (limit age : Nat) : Nat := min age limit

theorem bounded (limit age : Nat) : cap limit age ≤ limit := by
  exact Nat.min_le_right age limit

theorem advance (limit age : Nat) :
    cap limit (age + 1) = cap limit (cap limit age + 1) := by
  unfold cap
  omega

theorem tick (limit now stamp : Nat) (past : stamp ≤ now) :
    cap limit ((now + 1) - stamp) = cap limit (cap limit (now - stamp) + 1) := by
  unfold cap
  omega

theorem reset (limit now : Nat) : cap limit (now - now) = 0 := by
  simp [cap]

theorem deadline (limit delay now stamp : Nat)
    (past : stamp ≤ now) (within : delay ≤ limit) :
    stamp + delay ≤ now ↔ delay ≤ cap limit (now - stamp) := by
  unfold cap
  omega

theorem exact_test (limit delay age : Nat) (within : delay < limit) :
    age = delay ↔ cap limit age = delay := by
  unfold cap
  omega

end TlxOptimization.Age
