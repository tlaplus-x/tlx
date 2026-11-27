/- Shared orbit-quotient construction for an equivariant intermediate
`ConstrainedSystem` under `EquivRule.GroupPerm`, proving both the plain
`Certificate` and `ConstrainedCertificate` on `Quotient`. -/
set_option autoImplicit false
namespace TlxOptimization.EquivRule
open TlxOptimization
noncomputable section

/-- Shared orbit-quotient construction for an equivariant intermediate
`ConstrainedSystem` under `GroupPerm`, proving both the plain `Certificate`
and `ConstrainedCertificate` on `Quotient`. -/
structure OrbitQuotient {d : Nat} (sizes : Fin d → Nat) (S : Type) where
  system : ConstrainedSystem S
  rename : GroupPerm sizes → S → S
  rename_identity : ∀ s, rename GroupPerm.identity s = s
  rename_then : ∀ p q s, rename (p.then q) s = rename q (rename p s)
  rename_inverse : ∀ p s, rename p.inverse (rename p s) = s
  next_rename : ∀ p s t, system.toSystem.next s t → system.toSystem.next (rename p s) (rename p t)
  safe_rename : ∀ p s, system.toSystem.safe (rename p s) ↔ system.toSystem.safe s
  initSafe_rename : ∀ p s, system.initSafe (rename p s) ↔ system.initSafe s
  constraint_rename : ∀ p s, system.constraint (rename p s) ↔ system.constraint s
  actionConstraint_rename : ∀ p s t,
    system.actionConstraint (rename p s) (rename p t) ↔ system.actionConstraint s t
  actionSafe_rename : ∀ p s t,
    system.actionSafe (rename p s) (rename p t) ↔ system.actionSafe s t

namespace OrbitQuotient
variable {d : Nat} {sizes : Fin d → Nat} {S : Type} (oq : OrbitQuotient sizes S)

def Orbit (a b : S) : Prop :=
  ∃ p : GroupPerm sizes, oq.rename p a = b

def setoid : Setoid S where
  r := oq.Orbit
  iseqv := {
    refl := fun s => ⟨GroupPerm.identity, oq.rename_identity s⟩
    symm := by
      rintro s t ⟨p, rfl⟩
      exact ⟨p.inverse, oq.rename_inverse p s⟩
    trans := by
      rintro s t u ⟨p, rfl⟩ ⟨q, rfl⟩
      exact ⟨p.then q, oq.rename_then p q s⟩ }

def symProject (a : S) : Quotient oq.setoid :=
  Quotient.mk _ a

theorem symProject_rename (p : GroupPerm sizes) (a : S) :
    oq.symProject (oq.rename p a) = oq.symProject a := by
  have h : oq.symProject a = oq.symProject (oq.rename p a) :=
    Quotient.sound (show oq.Orbit a (oq.rename p a) from ⟨p, rfl⟩)
  exact h.symm

def reduced : System (Quotient oq.setoid) where
  initial q := ∃ a, oq.system.toSystem.initial a ∧ oq.symProject a = q
  next q r := ∃ a b, oq.symProject a = q ∧ oq.system.toSystem.next a b ∧ oq.symProject b = r
  safe q := Quotient.liftOn q oq.system.toSystem.safe (by
    rintro a b ⟨p, rfl⟩
    exact propext (oq.safe_rename p a).symm)

theorem symmetry_certificate : Certificate oq.system.toSystem oq.reduced oq.symProject := by
  constructor
  · intro q; rfl
  · intro a q
    constructor
    · rintro ⟨x, b, hx, hn, hb⟩
      obtain ⟨p, hp⟩ := Quotient.exact hx
      refine ⟨oq.rename p b, ?_, (oq.symProject_rename p b).trans hb⟩
      have h := oq.next_rename p x b hn
      rw [hp] at h
      exact h
    · rintro ⟨b, hn, hb⟩
      exact ⟨a, b, rfl, hn, hb⟩
  · intro a; rfl

def constrainedReduced : ConstrainedSystem (Quotient oq.setoid) where
  toSystem := oq.reduced
  initSafe q := Quotient.liftOn q oq.system.initSafe (by
    rintro a b ⟨p, rfl⟩
    exact propext (oq.initSafe_rename p a).symm)
  constraint q := Quotient.liftOn q oq.system.constraint (by
    rintro a b ⟨p, rfl⟩
    exact propext (oq.constraint_rename p a).symm)
  actionConstraint q r := ∃ a b, oq.symProject a = q ∧ oq.system.toSystem.next a b ∧
    oq.system.actionConstraint a b ∧ oq.symProject b = r
  actionSafe q r := ∀ a b, oq.symProject a = q → oq.symProject b = r → oq.system.toSystem.next a b →
    oq.system.actionSafe a b

theorem symmetry_constrained_certificate :
    ConstrainedCertificate oq.system oq.constrainedReduced oq.symProject := by
  refine ⟨oq.symmetry_certificate.initial, oq.symmetry_certificate.next, oq.symmetry_certificate.observe,
    fun _ => Iff.rfl, fun _ => Iff.rfl, ?_, ?_⟩
  · intro a q
    constructor
    · rintro ⟨_, hc, x, y, hx, hxy, hac, hy⟩
      obtain ⟨p, hp⟩ := Quotient.exact hx
      let b := oq.rename p y
      have hnext : oq.system.toSystem.next a b := by
        have h := oq.next_rename p x y hxy
        rwa [hp] at h
      have hact : oq.system.actionConstraint a b := by
        have h := (oq.actionConstraint_rename p x y).mpr hac
        rwa [hp] at h
      have hqb : oq.symProject b = q := (oq.symProject_rename p y).trans hy
      have hcb : oq.system.constraint b := by
        change oq.constrainedReduced.constraint (oq.symProject b)
        rw [hqb]
        exact hc
      exact ⟨b, hnext, hcb, hact, hqb⟩
    · rintro ⟨b, hn, hc, hac, rfl⟩
      exact ⟨⟨a, b, rfl, hn, rfl⟩, hc, ⟨a, b, rfl, hn, hac, rfl⟩⟩
  · intro a q
    constructor
    · intro h _ x y hx hy hxy
      obtain ⟨p, hp⟩ := Quotient.exact hx
      let b := oq.rename p y
      have hnext : oq.system.toSystem.next a b := by
        have hn := oq.next_rename p x y hxy
        rwa [hp] at hn
      have hqb : oq.symProject b = q := (oq.symProject_rename p y).trans hy
      have has := h b hnext hqb
      have hrew := (oq.actionSafe_rename p x y).mp
      rw [hp] at hrew
      exact hrew has
    · intro h b hab hqb
      exact h ⟨a, b, rfl, hab, hqb⟩ a b rfl hqb hab

end OrbitQuotient
end
end TlxOptimization.EquivRule
