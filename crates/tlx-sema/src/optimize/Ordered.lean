/- Shared order-projection and immutable-history algebra only. The compiler's
provenance analysis, rank construction, root discovery and runtime walker are
trusted; this file does not construct a certificate for an input model. -/
set_option autoImplicit false
namespace TlxOptimization.Ordered

def restrict {K V : Type} (keep : K → Prop) [DecidablePred keep]
    (table : K → Option V) (key : K) : Option V :=
  if keep key then table key else none

theorem retained_lookup {K V : Type} (keep : K → Prop) [DecidablePred keep]
    (table : K → Option V) (key : K) (retained : keep key) :
    restrict keep table key = table key := by
  simp [restrict, retained]

theorem order_equality (rename : Nat → Nat)
    (preserves : ∀ a b, rename a ≤ rename b ↔ a ≤ b) (a b : Nat) :
    rename a = rename b ↔ a = b := by
  constructor
  · intro h
    exact Nat.le_antisymm ((preserves a b).mp (by omega))
      ((preserves b a).mp (by omega))
  · intro h
    exact congrArg rename h

theorem fresh_above_live (frontier live offset : Nat)
    (old : live ≤ frontier) (fresh : 0 < offset) :
    live < frontier + offset := by
  omega

theorem fresh_order (frontier offset₁ offset₂ : Nat) :
    frontier + offset₁ ≤ frontier + offset₂ ↔ offset₁ ≤ offset₂ := by
  omega

end TlxOptimization.Ordered
