/- Choice-irrelevant symmetry rule IR over disjoint products of full permutation groups.
Models order-dependent CHOOSE explicitly via arbitrary un-permuted ranking functions
(`keyRank`, `recRank`) with zero symmetry assumptions on the tie-breaker.
Proves inductive state invariants (`flagAtMostOne`, `msgConstVal`, `msgUniformVal`)
from the lowered initialization and transition branches before discharging
unique-witness, projected-value-agreement, and commutative-fold obligations,
preserving empty-witness (`none`) errors across both guards and observations. -/
set_option autoImplicit false
namespace TlxOptimization.ChooseSymRule
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
open TlxOptimization

private theorem if_true_of {α : Type} {P : Prop} [Decidable P] (h : P) (x y : α) :
    (if P then x else y) = x := by
  split
  · rfl
  · rename_i hn; exact absurd h hn

private theorem if_false_of {α : Type} {P : Prop} [Decidable P] (h : ¬ P) (x y : α) :
    (if P then x else y) = y := by
  split
  · rename_i hp; exact absurd hp h
  · rfl

structure Permutation (K : Type) where
  toFun : K → K
  invFun : K → K
  left : ∀ k, invFun (toFun k) = k
  right : ∀ k, toFun (invFun k) = k

def Permutation.identity {K : Type} : Permutation K where
  toFun := id
  invFun := id
  left _ := rfl
  right _ := rfl

def Permutation.inverse {K : Type} (p : Permutation K) : Permutation K where
  toFun := p.invFun
  invFun := p.toFun
  left := p.right
  right := p.left

def Permutation.then {K : Type} (p q : Permutation K) : Permutation K where
  toFun := fun k => q.toFun (p.toFun k)
  invFun := fun k => p.invFun (q.invFun k)
  left k := by simp only [p.left, q.left]
  right k := by simp only [p.right, q.right]

abbrev Key {d : Nat} (sizes : Fin d → Nat) := Sigma (fun g : Fin d => Fin (sizes g))
abbrev GroupMask (d : Nat) := Fin d → Bool
abbrev GroupPerm {d : Nat} (sizes : Fin d → Nat) := ∀ g : Fin d, Permutation (Fin (sizes g))

instance instDecidableEqKey {d : Nat} {sizes : Fin d → Nat} : DecidableEq (Key sizes)
  | ⟨g1, i1⟩, ⟨g2, i2⟩ =>
    if h : g1 = g2 then
      by
        subst h
        exact if hi : i1 = i2 then isTrue (congrArg (Sigma.mk g1) hi)
        else isFalse (fun heq => by cases heq; exact hi rfl)
    else
      isFalse (fun heq => by cases heq; exact h rfl)

def GroupPerm.identity {d : Nat} {sizes : Fin d → Nat} : GroupPerm sizes :=
  fun _ => Permutation.identity

def GroupPerm.inverse {d : Nat} {sizes : Fin d → Nat} (p : GroupPerm sizes) : GroupPerm sizes :=
  fun g => (p g).inverse

def GroupPerm.then {d : Nat} {sizes : Fin d → Nat} (p q : GroupPerm sizes) : GroupPerm sizes :=
  fun g => (p g).then (q g)

def GroupPerm.toFun {d : Nat} {sizes : Fin d → Nat} (p : GroupPerm sizes) (k : Key sizes) : Key sizes :=
  ⟨k.1, (p k.1).toFun k.2⟩

def GroupPerm.invFun {d : Nat} {sizes : Fin d → Nat} (p : GroupPerm sizes) (k : Key sizes) : Key sizes :=
  ⟨k.1, (p k.1).invFun k.2⟩

@[simp] theorem GroupPerm.toFun_fst {d : Nat} {sizes : Fin d → Nat} (p : GroupPerm sizes) (k : Key sizes) :
    (p.toFun k).1 = k.1 := rfl

@[simp] theorem GroupPerm.invFun_fst {d : Nat} {sizes : Fin d → Nat} (p : GroupPerm sizes) (k : Key sizes) :
    (p.invFun k).1 = k.1 := rfl

theorem GroupPerm.left {d : Nat} {sizes : Fin d → Nat} (p : GroupPerm sizes) (k : Key sizes) :
    p.invFun (p.toFun k) = k := by
  cases k with
  | mk g i => simp only [GroupPerm.toFun, GroupPerm.invFun, (p g).left]

theorem GroupPerm.right {d : Nat} {sizes : Fin d → Nat} (p : GroupPerm sizes) (k : Key sizes) :
    p.toFun (p.invFun k) = k := by
  cases k with
  | mk g i => simp only [GroupPerm.toFun, GroupPerm.invFun, (p g).right]

theorem GroupPerm.injective {d : Nat} {sizes : Fin d → Nat} (p : GroupPerm sizes) {x y : Key sizes} :
    p.toFun x = p.toFun y ↔ x = y := by
  constructor
  · intro h
    have := congrArg p.invFun h
    simpa only [p.left] using this
  · intro h; exact congrArg p.toFun h

theorem GroupPerm.inv_injective {d : Nat} {sizes : Fin d → Nat} (p : GroupPerm sizes) {x y : Key sizes} :
    p.invFun x = p.invFun y ↔ x = y := by
  constructor
  · intro h
    have := congrArg p.toFun h
    simpa only [p.right] using this
  · intro h; exact congrArg p.invFun h

def allKeys {d : Nat} (sizes : Fin d → Nat) : List (Key sizes) :=
  (List.finRange d).flatMap (fun g => (List.finRange (sizes g)).map (fun i => ⟨g, i⟩))

theorem mem_allKeys {d : Nat} {sizes : Fin d → Nat} (k : Key sizes) : k ∈ allKeys sizes := by
  rcases k with ⟨g, i⟩
  simp only [allKeys, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  exact ⟨g, i, rfl⟩

private theorem nodup_map_inj {α β : Type} {f : α → β} (hinj : ∀ x y, f x = f y → x = y) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    rw [List.map_cons, List.nodup_cons]
    have h1 := List.nodup_cons.mp h
    constructor
    · intro hm
      rcases List.mem_map.mp hm with ⟨x, hx, hfx⟩
      exact h1.1 (hinj x a hfx ▸ hx)
    · exact nodup_map_inj hinj h1.2

private theorem nodup_flatMap_disjoint {α β : Type} {f : α → List β} :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, (f a).Nodup) →
      (∀ a1 ∈ l, ∀ a2 ∈ l, ∀ b, b ∈ f a1 → b ∈ f a2 → a1 = a2) →
      (l.flatMap f).Nodup
  | [], _, _, _ => List.nodup_nil
  | a :: t, hnd, hfn, hdisj => by
    rw [List.flatMap_cons, List.nodup_append]
    have ⟨ha_not_t, ht_nd⟩ := List.nodup_cons.mp hnd
    refine ⟨hfn a (List.mem_cons_self ..), nodup_flatMap_disjoint ht_nd
      (fun x hx => hfn x (List.mem_cons_of_mem a hx))
      (fun x hx y hy b hbx hby => hdisj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) b hbx hby), ?_⟩
    intro b1 hba b2 hbt hb_eq
    subst hb_eq
    rcases List.mem_flatMap.mp hbt with ⟨a2, ha2, hba2⟩
    have heq := hdisj a (List.mem_cons_self ..) a2 (List.mem_cons_of_mem a ha2) b1 hba hba2
    exact ha_not_t (heq ▸ ha2)

theorem nodup_allKeys {d : Nat} (sizes : Fin d → Nat) : (allKeys sizes).Nodup := by
  unfold allKeys
  apply nodup_flatMap_disjoint (List.nodup_finRange d)
  · intro g _
    exact nodup_map_inj (fun i1 i2 h => by cases h; rfl) (List.nodup_finRange (sizes g))
  · intro g1 _ g2 _ b hb1 hb2
    rcases List.mem_map.mp hb1 with ⟨_, _, rfl⟩
    rcases List.mem_map.mp hb2 with ⟨_, _, heq⟩
    cases heq
    rfl

private theorem nodup_length_eq {α : Type} [DecidableEq α] :
    ∀ {l1 l2 : List α}, l1.Nodup → l2.Nodup → (∀ x, x ∈ l1 ↔ x ∈ l2) → l1.length = l2.length
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, heq => absurd ((heq b).mpr (by simp)) (by simp)
  | a :: t, l2, h1, h2, heq => by
    have ha_not_t : a ∉ t := (List.nodup_cons.mp h1).1
    have ht_nd : t.Nodup := (List.nodup_cons.mp h1).2
    have ha_l2 : a ∈ l2 := (heq a).mp (by simp)
    have hlen : (l2.erase a).length + 1 = l2.length := by
      rw [List.length_erase_of_mem ha_l2]
      exact Nat.sub_add_cancel (List.length_pos_of_mem ha_l2)
    have hnd_erase : (l2.erase a).Nodup := h2.erase a
    have ih := nodup_length_eq ht_nd hnd_erase (fun x => by
      constructor
      · intro hx
        have hne : x ≠ a := fun h => ha_not_t (h ▸ hx)
        exact (List.mem_erase_of_ne hne).mpr ((heq x).mp (List.mem_cons_of_mem a hx))
      · intro hx
        have hne : x ≠ a := fun h => (List.Nodup.not_mem_erase h2) (h ▸ hx)
        have hx2 : x ∈ l2 := List.mem_of_mem_erase hx
        rcases List.mem_cons.mp ((heq x).mpr hx2) with rfl | hxt
        · exact absurd rfl hne
        · exact hxt)
    simp only [List.length_cons, ih, hlen]

private theorem sum_erase_mem {α : Type} [DecidableEq α] (f : α → Int) :
    ∀ {l : List α} {a : α}, a ∈ l → f a + ((l.erase a).map f).sum = (l.map f).sum
  | [], _, h => nomatch h
  | b :: t, a, h => by
    by_cases hab : b = a
    · subst hab
      simp only [List.erase_cons_head, List.map_cons, List.sum_cons]
    · have hat : a ∈ t := by
        rcases List.mem_cons.mp h with rfl | ht
        · exact absurd rfl hab
        · exact ht
      have hne : ¬ (b == a) = true := by intro heq; exact hab (eq_of_beq heq)
      rw [List.erase_cons_tail hne, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      have ih := sum_erase_mem f hat
      omega

private theorem nodup_sum_eq {α : Type} [DecidableEq α] (f : α → Int) :
    ∀ {l1 l2 : List α}, l1.Nodup → l2.Nodup → (∀ x, x ∈ l1 ↔ x ∈ l2) → (l1.map f).sum = (l2.map f).sum
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, heq => absurd ((heq b).mpr (by simp)) (by simp)
  | a :: t, l2, h1, h2, heq => by
    have ha_not_t : a ∉ t := (List.nodup_cons.mp h1).1
    have ht_nd : t.Nodup := (List.nodup_cons.mp h1).2
    have ha_l2 : a ∈ l2 := (heq a).mp (by simp)
    have hnd_erase : (l2.erase a).Nodup := h2.erase a
    have ih := nodup_sum_eq f ht_nd hnd_erase (fun x => by
      constructor
      · intro hx
        have hne : x ≠ a := fun h => ha_not_t (h ▸ hx)
        exact (List.mem_erase_of_ne hne).mpr ((heq x).mp (List.mem_cons_of_mem a hx))
      · intro hx
        have hne : x ≠ a := fun h => (List.Nodup.not_mem_erase h2) (h ▸ hx)
        have hx2 : x ∈ l2 := List.mem_of_mem_erase hx
        rcases List.mem_cons.mp ((heq x).mpr hx2) with rfl | hxt
        · exact absurd rfl hne
        · exact hxt)
    simp only [List.map_cons, List.sum_cons, ih]
    exact sum_erase_mem f ha_l2

def countFin (n : Nat) (f : Fin n → Bool) : Nat :=
  ((List.finRange n).filter f).length

theorem countFin_rename {n : Nat} (q : Permutation (Fin n)) (f : Fin n → Bool) :
    countFin n (fun i => f (q.invFun i)) = countFin n f := by
  unfold countFin
  let l1 := (List.finRange n).filter (fun i => f (q.invFun i))
  let l2 := (List.finRange n).filter f
  have h1 : l1.Nodup := (List.nodup_finRange n).filter _
  have h2 : l2.Nodup := (List.nodup_finRange n).filter _
  have hmap : (l1.map q.invFun).Nodup :=
    nodup_map_inj (fun x y h => by have := congrArg q.toFun h; simpa only [q.right] using this) h1
  have hlen := nodup_length_eq hmap h2 (fun x => by
    simp only [l1, l2, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨q.toFun x, by simpa only [q.left] using hx, q.left x⟩)
  simpa only [List.length_map] using hlen

def countKeys {d : Nat} (sizes : Fin d → Nat) (mask : GroupMask d) (pred : Key sizes → Bool) : Nat :=
  ((List.finRange d).map (fun g => if mask g then countFin (sizes g) (fun i => pred ⟨g, i⟩) else 0)).sum

theorem countKeys_rename {d : Nat} {sizes : Fin d → Nat} (p : GroupPerm sizes)
    (mask : GroupMask d) (pred : Key sizes → Bool) :
    countKeys sizes mask (fun k => pred (p.invFun k)) = countKeys sizes mask pred := by
  unfold countKeys
  congr 1
  apply List.map_congr_left
  intro g _
  cases mask g
  · rfl
  · exact countFin_rename (p g) (fun i => pred ⟨g, i⟩)

-- Order-dependent CHOOSE over an arbitrary un-permuted ranking function.
def chooseMinBy {α : Type} (rank : α → Nat) : List α → Option α
  | [] => none
  | x :: xs =>
      match chooseMinBy rank xs with
      | none => some x
      | some y => if rank x ≤ rank y then some x else some y

theorem chooseMinBy_eq_none {α : Type} (rank : α → Nat) :
    ∀ (l : List α), chooseMinBy rank l = none ↔ l = []
  | [] => by simp [chooseMinBy]
  | x :: xs => by
    unfold chooseMinBy
    cases hm : chooseMinBy rank xs with
    | none => simp
    | some y =>
      by_cases hle : rank x ≤ rank y <;> simp [hle]

theorem chooseMinBy_mem {α : Type} (rank : α → Nat) :
    ∀ {l : List α} {z : α}, chooseMinBy rank l = some z → z ∈ l
  | [], _, h => nomatch h
  | x :: xs, z, h => by
    unfold chooseMinBy at h
    cases hm : chooseMinBy rank xs with
    | none =>
      simp only [hm] at h
      injection h with hxz
      exact hxz ▸ List.mem_cons_self ..
    | some y =>
      simp only [hm] at h
      by_cases hle : rank x ≤ rank y
      · simp only [hle, ↓reduceIte] at h
        injection h with hxz
        exact hxz ▸ List.mem_cons_self ..
      · simp only [hle, ↓reduceIte] at h
        injection h with hyz
        exact List.mem_cons_of_mem x (chooseMinBy_mem rank (hyz ▸ hm))

theorem chooseUnique_equivariant {d : Nat} {sizes : Fin d → Nat}
    (p : GroupPerm sizes) (rank : Key sizes → Nat)
    (pred pred' : Key sizes → Bool)
    (heq : ∀ k, pred' k = pred (p.invFun k))
    (huniq : ∀ k1 k2, pred k1 = true → pred k2 = true → k1 = k2) :
    chooseMinBy rank ((allKeys sizes).filter pred') =
      (chooseMinBy rank ((allKeys sizes).filter pred)).map p.toFun := by
  cases hm : chooseMinBy rank ((allKeys sizes).filter pred) with
  | none =>
    have hemp : (allKeys sizes).filter pred = [] := (chooseMinBy_eq_none rank _).mp hm
    suffices h' : (allKeys sizes).filter pred' = [] by
      simp only [Option.map_none, (chooseMinBy_eq_none rank _).mpr h']
    rw [List.filter_eq_nil_iff] at hemp ⊢
    intro k _ hp'
    rw [heq] at hp'
    exact hemp (p.invFun k) (mem_allKeys _) hp'
  | some k =>
    have hk_mem := List.mem_filter.mp (chooseMinBy_mem rank hm)
    have hpk' : pred' (p.toFun k) = true := by rw [heq, p.left]; exact hk_mem.2
    have hne' : (allKeys sizes).filter pred' ≠ [] := by
      intro hnil
      exact List.not_mem_nil (hnil ▸ List.mem_filter.mpr ⟨mem_allKeys (p.toFun k), hpk'⟩)
    cases hm' : chooseMinBy rank ((allKeys sizes).filter pred') with
    | none => exact absurd ((chooseMinBy_eq_none rank _).mp hm') hne'
    | some k' =>
      have hk'_mem := List.mem_filter.mp (chooseMinBy_mem rank hm')
      rw [heq] at hk'_mem
      have heqk : p.invFun k' = k := huniq _ _ hk'_mem.2 hk_mem.2
      have hk_eq : k' = p.toFun k := by rw [← heqk, p.right]
      simp only [Option.map_some, hk_eq]

theorem chooseKeyProj_equivariant {d : Nat} {sizes : Fin d → Nat} {V : Type}
    (p : GroupPerm sizes) (rank : Key sizes → Nat)
    (pred pred' : Key sizes → Bool) (proj proj' : Key sizes → V)
    (hpred : ∀ k, pred' k = pred (p.invFun k))
    (hproj : ∀ k, proj' k = proj (p.invFun k))
    (hagree : ∀ k1 k2, pred k1 = true → pred k2 = true → proj k1 = proj k2) :
    (chooseMinBy rank ((allKeys sizes).filter pred')).map proj' =
      (chooseMinBy rank ((allKeys sizes).filter pred)).map proj := by
  cases hm : chooseMinBy rank ((allKeys sizes).filter pred) with
  | none =>
    have hemp : (allKeys sizes).filter pred = [] := (chooseMinBy_eq_none rank _).mp hm
    have hemp' : (allKeys sizes).filter pred' = [] := by
      rw [List.filter_eq_nil_iff] at hemp ⊢
      intro k _ hp'
      rw [hpred] at hp'
      exact hemp (p.invFun k) (mem_allKeys _) hp'
    simp only [Option.map_none, (chooseMinBy_eq_none rank _).mpr hemp']
  | some k =>
    have hk_mem := List.mem_filter.mp (chooseMinBy_mem rank hm)
    have hpk' : pred' (p.toFun k) = true := by rw [hpred, p.left]; exact hk_mem.2
    have hne' : (allKeys sizes).filter pred' ≠ [] := by
      intro hnil
      exact List.not_mem_nil (hnil ▸ List.mem_filter.mpr ⟨mem_allKeys (p.toFun k), hpk'⟩)
    cases hm' : chooseMinBy rank ((allKeys sizes).filter pred') with
    | none => exact absurd ((chooseMinBy_eq_none rank _).mp hm') hne'
    | some k' =>
      have hk'_mem := List.mem_filter.mp (chooseMinBy_mem rank hm')
      rw [hpred] at hk'_mem
      simp only [Option.map_some, hproj, hagree _ _ hk'_mem.2 hk_mem.2]

-- Extensional finite sets (quotient of lists by element membership),
-- making message-set union idempotent and order-independent.
def listSetRel {α : Type} (l1 l2 : List α) : Prop :=
  ∀ x, x ∈ l1 ↔ x ∈ l2

def listSetoid (α : Type) : Setoid (List α) where
  r := listSetRel
  iseqv := {
    refl := fun _ _ => Iff.rfl
    symm := fun h x => (h x).symm
    trans := fun h1 h2 x => (h1 x).trans (h2 x)
  }

def FinSet (α : Type) : Type := Quotient (listSetoid α)

namespace FinSet

def ofList {α : Type} (l : List α) : FinSet α := Quotient.mk (listSetoid α) l

def mem {α : Type} (x : α) (s : FinSet α) : Prop :=
  Quotient.liftOn s (fun l => x ∈ l) (fun _ _ h => propext (h x))

instance {α : Type} : Membership α (FinSet α) := ⟨fun s x => FinSet.mem x s⟩

theorem mem_ofList {α : Type} {x : α} {l : List α} : x ∈ ofList l ↔ x ∈ l := Iff.rfl

theorem ext {α : Type} {s1 s2 : FinSet α} (h : ∀ x, x ∈ s1 ↔ x ∈ s2) : s1 = s2 := by
  induction s1 using Quotient.ind with
  | _ l1 =>
    induction s2 using Quotient.ind with
    | _ l2 => exact Quotient.sound h

def empty {α : Type} : FinSet α := ofList []

def singleton {α : Type} (x : α) : FinSet α := ofList [x]

def insert {α : Type} (x : α) (s : FinSet α) : FinSet α :=
  Quotient.liftOn s (fun l => ofList (x :: l)) (fun _ _ h =>
    Quotient.sound (fun y => by simp only [List.mem_cons, h y]))

theorem not_mem_empty {α : Type} {x : α} : x ∉ (empty : FinSet α) := by
  intro h; exact List.not_mem_nil h

theorem mem_singleton {α : Type} {x y : α} : x ∈ singleton y ↔ x = y := by
  simp only [singleton, mem_ofList, List.mem_singleton]

theorem mem_insert {α : Type} {x y : α} {s : FinSet α} :
    x ∈ insert y s ↔ x = y ∨ x ∈ s := by
  induction s using Quotient.ind with
  | _ l => exact List.mem_cons

theorem insert_idem {α : Type} (x : α) (s : FinSet α) :
    insert x (insert x s) = insert x s := by
  apply ext; intro y
  simp only [mem_insert]
  constructor
  · rintro (rfl | rfl | hs)
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr hs
  · intro h; exact Or.inr h

theorem insert_comm {α : Type} (x y : α) (s : FinSet α) :
    insert x (insert y s) = insert y (insert x s) := by
  apply ext; intro z
  simp only [mem_insert]
  constructor
  · rintro (rfl | rfl | hs)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr hs)
  · rintro (rfl | rfl | hs)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr hs)

def isEmpty {α : Type} (s : FinSet α) : Bool :=
  Quotient.liftOn s (fun l => l.isEmpty) (fun l1 l2 h => by
    apply Bool.eq_iff_iff.mpr
    simp only [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
    constructor
    · intro h1 x hx; exact h1 x ((h x).mpr hx)
    · intro h2 x hx; exact h2 x ((h x).mp hx))

theorem isEmpty_iff {α : Type} {s : FinSet α} :
    s.isEmpty = true ↔ s = empty := by
  induction s using Quotient.ind with
  | _ l =>
    change l.isEmpty = true ↔ Quotient.mk (listSetoid α) l = empty
    rw [List.isEmpty_iff]
    constructor
    · intro hl; subst hl; rfl
    · intro heq
      have h := Quotient.exact heq
      rw [List.eq_nil_iff_forall_not_mem]
      intro x hx
      exact List.not_mem_nil ((h x).mp hx)

def all {α : Type} (p : α → Bool) (s : FinSet α) : Bool :=
  Quotient.liftOn s (fun l => l.all p) (fun l1 l2 h => by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor
    · intro h1 x hx; exact h1 x ((h x).mpr hx)
    · intro h2 x hx; exact h2 x ((h x).mp hx))

theorem all_eq_true {α : Type} {p : α → Bool} {s : FinSet α} :
    s.all p = true ↔ ∀ x, x ∈ s → p x = true := by
  induction s using Quotient.ind with
  | _ l => exact List.all_eq_true

def any {α : Type} (p : α → Bool) (s : FinSet α) : Bool :=
  Quotient.liftOn s (fun l => l.any p) (fun l1 l2 h => by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨x, hx, hp⟩; exact ⟨x, (h x).mp hx, hp⟩
    · rintro ⟨x, hx, hp⟩; exact ⟨x, (h x).mpr hx, hp⟩)

theorem any_eq_true {α : Type} {p : α → Bool} {s : FinSet α} :
    s.any p = true ↔ ∃ x, x ∈ s ∧ p x = true := by
  induction s using Quotient.ind with
  | _ l => exact List.any_eq_true

end FinSet

private theorem exists_min_nat (Q : Nat → Prop) :
    ∀ n, Q n → ∃ m, Q m ∧ ∀ k < m, ¬ Q k := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hlt : ∃ k, k < n ∧ Q k
    · rcases hlt with ⟨k, hkn, hqk⟩
      exact ih k hkn hqk
    · exact ⟨n, hn, fun k hkn hqk => hlt ⟨k, hkn, hqk⟩⟩

-- Order-dependent CHOOSE over an extensional predicate using an arbitrary un-permuted ranking.
def chooseMinPred {α : Type} (rank : α → Nat) (P : α → Prop) : Option α := by
  classical
  exact if h : ∃ x, P x then
    let x0 := Classical.choose h
    have hmin : ∃ m, (∃ x, P x ∧ rank x = m) ∧ ∀ k < m, ¬ (∃ x, P x ∧ rank x = k) :=
      exists_min_nat (fun m => ∃ x, P x ∧ rank x = m) (rank x0) ⟨x0, Classical.choose_spec h, rfl⟩
    some (Classical.choose (Classical.choose_spec hmin).1)
  else none

theorem chooseMinPred_eq_none {α : Type} (rank : α → Nat) (P : α → Prop) :
    chooseMinPred rank P = none ↔ ∀ x, ¬ P x := by
  classical
  unfold chooseMinPred
  split
  · rename_i h
    constructor
    · intro hnone; nomatch hnone
    · intro hfa; rcases h with ⟨x, hx⟩; exact absurd hx (hfa x)
  · rename_i h
    constructor
    · intro _ x hx; exact h ⟨x, hx⟩
    · intro _; rfl

theorem chooseMinPred_mem {α : Type} (rank : α → Nat) {P : α → Prop} {z : α}
    (h : chooseMinPred rank P = some z) : P z := by
  classical
  unfold chooseMinPred at h
  split at h
  · rename_i hex
    injection h with hzeq
    subst hzeq
    let x0 := Classical.choose hex
    have hmin : ∃ m, (∃ x, P x ∧ rank x = m) ∧ ∀ k < m, ¬ (∃ x, P x ∧ rank x = k) :=
      exists_min_nat (fun m => ∃ x, P x ∧ rank x = m) (rank x0) ⟨x0, Classical.choose_spec hex, rfl⟩
    exact (Classical.choose_spec (Classical.choose_spec hmin).1).1
  · nomatch h

theorem chooseMsgProj_equivariant {d : Nat} {sizes : Fin d → Nat} {Meta V : Type}
    (p : GroupPerm sizes) (recRank : Key sizes → Meta → V → Nat)
    (store store' : Key sizes → FinSet (Meta × V))
    (filter filter' : Key sizes → Meta → V → Bool)
    (hstore : ∀ k, store' k = store (p.invFun k))
    (hfilter : ∀ k m v, filter' k m v = filter (p.invFun k) m v)
    (hagree : ∀ k1 m1 v1 k2 m2 v2,
      (m1, v1) ∈ store k1 → filter k1 m1 v1 = true →
      (m2, v2) ∈ store k2 → filter k2 m2 v2 = true → v1 = v2) :
    (chooseMinPred (fun x : Key sizes × Meta × V => recRank x.1 x.2.1 x.2.2)
        (fun x => x.2 ∈ store' x.1 ∧ filter' x.1 x.2.1 x.2.2 = true)).map (fun x => x.2.2) =
      (chooseMinPred (fun x : Key sizes × Meta × V => recRank x.1 x.2.1 x.2.2)
        (fun x => x.2 ∈ store x.1 ∧ filter x.1 x.2.1 x.2.2 = true)).map (fun x => x.2.2) := by
  let rfn := fun (x : Key sizes × Meta × V) => recRank x.1 x.2.1 x.2.2
  let P := fun (x : Key sizes × Meta × V) => x.2 ∈ store x.1 ∧ filter x.1 x.2.1 x.2.2 = true
  let P' := fun (x : Key sizes × Meta × V) => x.2 ∈ store' x.1 ∧ filter' x.1 x.2.1 x.2.2 = true
  cases hm : chooseMinPred rfn P with
  | none =>
    have hemp := (chooseMinPred_eq_none rfn P).mp hm
    have hemp' : ∀ x, ¬ P' x := by
      rintro ⟨k, m, v⟩ ⟨hs', hf'⟩
      rw [hstore] at hs'
      rw [hfilter] at hf'
      exact hemp (p.invFun k, m, v) ⟨hs', hf'⟩
    have hnone' : chooseMinPred rfn P' = none := (chooseMinPred_eq_none rfn P').mpr hemp'
    change (chooseMinPred rfn P').map (fun x => x.2.2) = none
    rw [hnone']
    rfl
  | some c =>
    rcases c with ⟨k, m, v⟩
    have ⟨hs, hf⟩ := chooseMinPred_mem rfn hm
    have hex' : P' (p.toFun k, m, v) := by
      show (m, v) ∈ store' (p.toFun k) ∧ filter' (p.toFun k) m v = true
      rw [hstore, hfilter, p.left]
      exact ⟨hs, hf⟩
    cases hm' : chooseMinPred rfn P' with
    | none => exact absurd hex' ((chooseMinPred_eq_none rfn P').mp hm' (p.toFun k, m, v))
    | some c' =>
      rcases c' with ⟨k', m', v'⟩
      have ⟨hs', hf'⟩ := chooseMinPred_mem rfn hm'
      rw [hstore] at hs'
      rw [hfilter] at hf'
      simp only [Option.map_some, hagree _ _ _ _ _ _ hs' hf' hs hf]

-- Recursive CHOOSE-based commutative sum fold along an arbitrary un-permuted key ranking.
def chooseFoldAdd {K : Type} [DecidableEq K] (rank : K → Nat) (univ : List K) :
    Nat → (K → Bool) → (K → Int) → Int
  | 0, _, _ => 0
  | fuel + 1, mem, f =>
      match chooseMinBy rank (univ.filter mem) with
      | none => 0
      | some k => f k + chooseFoldAdd rank univ fuel (fun x => mem x && !decide (x = k)) f

theorem chooseFoldAdd_eq_sum {K : Type} [DecidableEq K] (rank : K → Nat) (univ : List K)
    (hnd : univ.Nodup) :
    ∀ (fuel : Nat) (mem : K → Bool) (f : K → Int),
      (univ.filter mem).length ≤ fuel →
      chooseFoldAdd rank univ fuel mem f = ((univ.filter mem).map f).sum
  | 0, mem, f, hlen => by
    have hnil : univ.filter mem = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    simp only [chooseFoldAdd, hnil, List.map_nil, List.sum_nil]
  | fuel + 1, mem, f, hlen => by
    unfold chooseFoldAdd
    cases hm : chooseMinBy rank (univ.filter mem) with
    | none =>
      have hnil := (chooseMinBy_eq_none rank _).mp hm
      simp only [hnil, List.map_nil, List.sum_nil]
    | some k =>
      simp only []
      have hk_l : k ∈ univ.filter mem := chooseMinBy_mem rank hm
      have hl_nd : (univ.filter mem).Nodup := hnd.filter mem
      let mem' := fun x => mem x && !decide (x = k)
      have hl'_nd : (univ.filter mem').Nodup := hnd.filter mem'
      have herase_nd : ((univ.filter mem).erase k).Nodup := hl_nd.erase k
      have heqv : ∀ x, x ∈ univ.filter mem' ↔ x ∈ (univ.filter mem).erase k := by
        intro x
        constructor
        · intro hx
          have ⟨hxu, hmx'⟩ := List.mem_filter.mp hx
          simp only [mem', Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hmx'
          exact (List.mem_erase_of_ne hmx'.2).mpr (List.mem_filter.mpr ⟨hxu, hmx'.1⟩)
        · intro hx
          have hne : x ≠ k := fun heq => (List.Nodup.not_mem_erase hl_nd) (heq ▸ hx)
          have hxl : x ∈ univ.filter mem := List.mem_of_mem_erase hx
          have ⟨hxu, hmx⟩ := List.mem_filter.mp hxl
          apply List.mem_filter.mpr ⟨hxu, ?_⟩
          simp only [mem', hmx, hne, decide_false, Bool.not_false, Bool.and_self]
      have hlen_eq : (univ.filter mem').length = ((univ.filter mem).erase k).length :=
        nodup_length_eq hl'_nd herase_nd heqv
      have hlen_pos : 0 < (univ.filter mem).length := List.length_pos_of_mem hk_l
      have hlen_erase : ((univ.filter mem).erase k).length + 1 = (univ.filter mem).length := by
        rw [List.length_erase_of_mem hk_l]
        exact Nat.sub_add_cancel hlen_pos
      have hlen' : (univ.filter mem').length ≤ fuel := by omega
      have ih := chooseFoldAdd_eq_sum rank univ hnd fuel mem' f hlen'
      have hsum_eq : ((univ.filter mem').map f).sum = (((univ.filter mem).erase k).map f).sum :=
        nodup_sum_eq f hl'_nd herase_nd heqv
      change f k + chooseFoldAdd rank univ fuel mem' f = ((univ.filter mem).map f).sum
      rw [ih, hsum_eq]
      exact sum_erase_mem f hk_l

theorem chooseFoldAdd_rename {d : Nat} {sizes : Fin d → Nat}
    (p : GroupPerm sizes) (rank : Key sizes → Nat)
    (mem mem' : Key sizes → Bool) (f f' : Key sizes → Int)
    (hmem : ∀ k, mem' k = mem (p.invFun k))
    (hf : ∀ k, f' k = f (p.invFun k)) :
    chooseFoldAdd rank (allKeys sizes) (allKeys sizes).length mem' f' =
      chooseFoldAdd rank (allKeys sizes) (allKeys sizes).length mem f := by
  have hnd := nodup_allKeys sizes
  rw [chooseFoldAdd_eq_sum rank (allKeys sizes) hnd _ mem' f' (List.length_filter_le ..),
      chooseFoldAdd_eq_sum rank (allKeys sizes) hnd _ mem f (List.length_filter_le ..)]
  let l1 := (allKeys sizes).filter mem'
  let l2 := (allKeys sizes).filter mem
  have hl1_nd : l1.Nodup := hnd.filter mem'
  have hl2_nd : l2.Nodup := hnd.filter mem
  have hmap_nd : (l1.map p.invFun).Nodup :=
    nodup_map_inj (fun x y h => (p.inv_injective).mp h) hl1_nd
  have hmap_sum : (l1.map f').sum = ((l1.map p.invFun).map f).sum := by
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hf k
  rw [hmap_sum]
  apply nodup_sum_eq f hmap_nd hl2_nd
  intro x
  simp only [l1, l2, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨y, ⟨_, hmy⟩, rfl⟩
    rw [hmem] at hmy
    exact ⟨mem_allKeys _, hmy⟩
  · rintro ⟨_, hmx⟩
    refine ⟨p.toFun x, ⟨mem_allKeys _, ?_⟩, p.left x⟩
    rw [hmem, p.left]
    exact hmx

abbrev KeyVal (K A : Type) := Sum K A
abbrev Environment (K : Type) := Nat → K
abbrev Maps (M K V : Type) := M → K → V
abbrev Slots (S K A : Type) := S → KeyVal K A
abbrev Flags (F K : Type) := F → K → Bool
abbrev Msgs (MS K Meta V : Type) := MS → K → FinSet (Meta × V)

structure RawState (C M S F MS K Meta V A : Type) where
  core : C
  maps : Maps M K V
  slots : Slots S K A
  flags : Flags F K
  msgs : Msgs MS K Meta V

def push {K : Type} (keys : Environment K) (k : K) : Environment K
  | 0 => k
  | i + 1 => keys i

def renameKeys {d : Nat} {sizes : Fin d → Nat} (p : GroupPerm sizes)
    (keys : Environment (Key sizes)) : Environment (Key sizes) :=
  fun i => p.toFun (keys i)

def renameMaps {d : Nat} {sizes : Fin d → Nat} {M V : Type} (p : GroupPerm sizes)
    (r : Maps M (Key sizes) V) : Maps M (Key sizes) V :=
  fun m k => r m (p.invFun k)

def renameKeyVal {d : Nat} {sizes : Fin d → Nat} {A : Type} (p : GroupPerm sizes) :
    KeyVal (Key sizes) A → KeyVal (Key sizes) A
  | .inl k => .inl (p.toFun k)
  | .inr a => .inr a

def renameSlots {d : Nat} {sizes : Fin d → Nat} {S A : Type} (p : GroupPerm sizes)
    (u : Slots S (Key sizes) A) : Slots S (Key sizes) A :=
  fun s => renameKeyVal p (u s)

def renameFlags {d : Nat} {sizes : Fin d → Nat} {F : Type} (p : GroupPerm sizes)
    (fl : Flags F (Key sizes)) : Flags F (Key sizes) :=
  fun f k => fl f (p.invFun k)

def renameMsgs {d : Nat} {sizes : Fin d → Nat} {MS Meta V : Type} (p : GroupPerm sizes)
    (ms : Msgs MS (Key sizes) Meta V) : Msgs MS (Key sizes) Meta V :=
  fun id k => ms id (p.invFun k)

def rename {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type} (p : GroupPerm sizes)
    (st : RawState C M S F MS (Key sizes) Meta V A) : RawState C M S F MS (Key sizes) Meta V A where
  core := st.core
  maps := renameMaps p st.maps
  slots := renameSlots p st.slots
  flags := renameFlags p st.flags
  msgs := renameMsgs p st.msgs

@[simp] theorem rename_core {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (p : GroupPerm sizes) (st : RawState C M S F MS (Key sizes) Meta V A) :
    (rename p st).core = st.core := rfl

@[simp] theorem rename_maps {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (p : GroupPerm sizes) (st : RawState C M S F MS (Key sizes) Meta V A) :
    (rename p st).maps = renameMaps p st.maps := rfl

@[simp] theorem rename_slots {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (p : GroupPerm sizes) (st : RawState C M S F MS (Key sizes) Meta V A) :
    (rename p st).slots = renameSlots p st.slots := rfl

@[simp] theorem rename_flags {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (p : GroupPerm sizes) (st : RawState C M S F MS (Key sizes) Meta V A) :
    (rename p st).flags = renameFlags p st.flags := rfl

@[simp] theorem rename_msgs {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (p : GroupPerm sizes) (st : RawState C M S F MS (Key sizes) Meta V A) :
    (rename p st).msgs = renameMsgs p st.msgs := rfl

theorem renameKeys_push {d : Nat} {sizes : Fin d → Nat} (p : GroupPerm sizes)
    (keys : Environment (Key sizes)) (k : Key sizes) :
    renameKeys p (push keys k) = push (renameKeys p keys) (p.toFun k) := by
  funext i; cases i <;> rfl

theorem renameKeyVal_injective {d : Nat} {sizes : Fin d → Nat} {A : Type}
    (p : GroupPerm sizes) {x y : KeyVal (Key sizes) A} :
    renameKeyVal p x = renameKeyVal p y ↔ x = y := by
  cases x <;> cases y <;> simp only [renameKeyVal, Sum.inl.injEq, Sum.inr.injEq, p.injective, reduceCtorEq]

theorem rename_identity {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (st : RawState C M S F MS (Key sizes) Meta V A) :
    rename GroupPerm.identity st = st := by
  rcases st with ⟨c, r, u, fl, ms⟩
  simp only [rename, RawState.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext m k; cases k; rfl
  · funext s; change renameKeyVal GroupPerm.identity (u s) = u s
    cases u s with
    | inl k => cases k; rfl
    | inr a => rfl
  · funext f k; cases k; rfl
  · funext id k; cases k; rfl

theorem rename_then {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (p q : GroupPerm sizes) (st : RawState C M S F MS (Key sizes) Meta V A) :
    rename (p.then q) st = rename q (rename p st) := by
  rcases st with ⟨c, r, u, fl, ms⟩
  simp only [rename, RawState.mk.injEq, true_and]
  refine ⟨rfl, ?_, rfl, rfl⟩
  funext s
  change renameKeyVal (p.then q) (u s) = renameKeyVal q (renameKeyVal p (u s))
  cases u s <;> rfl

theorem rename_inverse {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (p : GroupPerm sizes) (st : RawState C M S F MS (Key sizes) Meta V A) :
    rename p.inverse (rename p st) = st := by
  rcases st with ⟨c, r, u, fl, ms⟩
  simp only [rename, RawState.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext m k; exact congrArg (r m) (p.left k)
  · funext s; change renameKeyVal p.inverse (renameKeyVal p (u s)) = u s
    cases u s with
    | inl k => simp only [renameKeyVal, GroupPerm.inverse, GroupPerm.toFun, Permutation.inverse, (p k.1).left]
    | inr a => rfl
  · funext f k; exact congrArg (fl f) (p.left k)
  · funext id k; exact congrArg (ms id) (p.left k)

inductive KeyRef (S : Type) where
  | bound (idx : Nat)
  | slot (slot : S)
  | fixed (id : Nat)

def evalKeyRef {d : Nat} {sizes : Fin d → Nat} {S A : Type}
    (fixedAtom : Nat → A) (u : Slots S (Key sizes) A) (keys : Environment (Key sizes)) :
    KeyRef S → KeyVal (Key sizes) A
  | .bound i => .inl (keys i)
  | .slot s => u s
  | .fixed id => .inr (fixedAtom id)

theorem evalKeyRef_rename {d : Nat} {sizes : Fin d → Nat} {S A : Type} (p : GroupPerm sizes)
    (fixedAtom : Nat → A) (u : Slots S (Key sizes) A) (keys : Environment (Key sizes))
    (ref : KeyRef S) :
    evalKeyRef fixedAtom (renameSlots p u) (renameKeys p keys) ref =
      renameKeyVal p (evalKeyRef fixedAtom u keys ref) := by
  cases ref <;> rfl

structure AuxEnv (Meta V : Type) where
  metas : List Meta := []
  vals : List V := []
  nats : List Nat := []
  ints : List Int := []

structure LeafArgs (Meta V A : Type) where
  mapVals : List V
  slotMapVals : List (Option V)
  slotFixedVals : List (Option A)
  flagVals : List Bool
  aux : AuxEnv Meta V

structure LeafSpec (M S F : Type) where
  id : Nat
  mapReads : List (M × Nat)
  slotMapReads : List (M × S)
  slotFixedReads : List S
  flagReads : List (F × KeyRef S)

def evalLeafSpec {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) (spec : LeafSpec M S F) :
    LeafArgs Meta V A where
  mapVals := spec.mapReads.map (fun item => st.maps item.1 (keys item.2))
  slotMapVals := spec.slotMapReads.map (fun item =>
    match st.slots item.2 with | .inl k => some (st.maps item.1 k) | .inr _ => none)
  slotFixedVals := spec.slotFixedReads.map (fun s =>
    match st.slots s with | .inl _ => none | .inr a => some a)
  flagVals := spec.flagReads.map (fun item =>
    match evalKeyRef fixedAtom st.slots keys item.2 with | .inl k => st.flags item.1 k | .inr _ => false)
  aux := aux

theorem evalLeafSpec_rename {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (p : GroupPerm sizes) (fixedAtom : Nat → A)
    (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) (spec : LeafSpec M S F) :
    evalLeafSpec fixedAtom (rename p st) (renameKeys p keys) aux spec =
      evalLeafSpec fixedAtom st keys aux spec := by
  simp only [evalLeafSpec, rename, LeafArgs.mk.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [renameMaps, renameKeys, p.left]
  · apply List.map_congr_left
    intro item _
    simp only [renameSlots]
    cases st.slots item.2 with
    | inl k => simp only [renameKeyVal, renameMaps, p.left]
    | inr a => rfl
  · apply List.map_congr_left
    intro s _
    simp only [renameSlots]
    cases st.slots s <;> rfl
  · apply List.map_congr_left
    intro item _
    rw [evalKeyRef_rename]
    cases evalKeyRef fixedAtom st.slots keys item.2 with
    | inl k => simp only [renameKeyVal, renameFlags, p.left]
    | inr a => rfl

inductive PureTest (d : Nat) (M S F MS : Type) where
  | truth (value : Bool)
  | leaf (spec : LeafSpec M S F)
  | equal (left right : KeyRef S)
  | inGroup (key : KeyRef S) (mask : GroupMask d)
  | flag (f : F) (key : KeyRef S)
  | msgEmpty (ms : MS)
  | msgAll (ms : MS) (body : PureTest d M S F MS)
  | msgSome (ms : MS) (body : PureTest d M S F MS)
  | conj (left right : PureTest d M S F MS)
  | disj (left right : PureTest d M S F MS)
  | neg (body : PureTest d M S F MS)
  | all (mask : GroupMask d) (body : PureTest d M S F MS)
  | some (mask : GroupMask d) (body : PureTest d M S F MS)
  | bindCount (mask : GroupMask d) (pred body : PureTest d M S F MS)

def PureTest.eval {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (leafFn : Nat → LeafArgs Meta V A → Bool)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) : PureTest d M S F MS → Bool := by
  classical
  exact fun t => match t with
    | .truth value => value
    | .leaf spec => leafFn spec.id (evalLeafSpec fixedAtom st keys aux spec)
    | .equal a b => decide (evalKeyRef fixedAtom st.slots keys a = evalKeyRef fixedAtom st.slots keys b)
    | .inGroup ref mask =>
        match evalKeyRef fixedAtom st.slots keys ref with
        | .inl k => mask k.1
        | .inr _ => false
    | .flag f ref =>
        match evalKeyRef fixedAtom st.slots keys ref with
        | .inl k => st.flags f k
        | .inr _ => false
    | .msgEmpty ms => (allKeys sizes).all (fun k => (st.msgs ms k).isEmpty)
    | .msgAll ms body =>
        (allKeys sizes).all (fun k =>
          (st.msgs ms k).all (fun mv =>
            body.eval leafFn fixedAtom st (push keys k)
              { aux with metas := mv.1 :: aux.metas, vals := mv.2 :: aux.vals }))
    | .msgSome ms body =>
        (allKeys sizes).any (fun k =>
          (st.msgs ms k).any (fun mv =>
            body.eval leafFn fixedAtom st (push keys k)
              { aux with metas := mv.1 :: aux.metas, vals := mv.2 :: aux.vals }))
    | .conj a b => a.eval leafFn fixedAtom st keys aux && b.eval leafFn fixedAtom st keys aux
    | .disj a b => a.eval leafFn fixedAtom st keys aux || b.eval leafFn fixedAtom st keys aux
    | .neg a => !(a.eval leafFn fixedAtom st keys aux)
    | .all mask body =>
        (allKeys sizes).all (fun k =>
          !(mask k.1) || body.eval leafFn fixedAtom st (push keys k) aux)
    | .some mask body =>
        (allKeys sizes).any (fun k =>
          mask k.1 && body.eval leafFn fixedAtom st (push keys k) aux)
    | .bindCount mask pred body =>
        let n := countKeys sizes mask (fun k => pred.eval leafFn fixedAtom st (push keys k) aux)
        body.eval leafFn fixedAtom st keys { aux with nats := n :: aux.nats }

private theorem allKeys_all_rename {d : Nat} {sizes : Fin d → Nat}
    (p : GroupPerm sizes) (f f' : Key sizes → Bool)
    (heq : ∀ k, f' k = f (p.invFun k)) :
    (allKeys sizes).all f' = (allKeys sizes).all f := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro h k _
    have hp := h (p.toFun k) (mem_allKeys _)
    rwa [heq, p.left] at hp
  · intro h k _
    rw [heq]
    exact h (p.invFun k) (mem_allKeys _)

private theorem allKeys_any_rename {d : Nat} {sizes : Fin d → Nat}
    (p : GroupPerm sizes) (f f' : Key sizes → Bool)
    (heq : ∀ k, f' k = f (p.invFun k)) :
    (allKeys sizes).any f' = (allKeys sizes).any f := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨k, _, hk⟩
    rw [heq] at hk
    exact ⟨p.invFun k, mem_allKeys _, hk⟩
  · rintro ⟨k, _, hk⟩
    refine ⟨p.toFun k, mem_allKeys _, ?_⟩
    rwa [heq, p.left]

theorem PureTest.equivariant {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (p : GroupPerm sizes) (leafFn : Nat → LeafArgs Meta V A → Bool)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (t : PureTest d M S F MS) (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    t.eval leafFn fixedAtom (rename p st) (renameKeys p keys) aux =
      t.eval leafFn fixedAtom st keys aux := by
  classical
  induction t generalizing keys aux with
  | truth v => rfl
  | leaf spec => simp only [PureTest.eval, evalLeafSpec_rename]
  | equal a b =>
    simp only [PureTest.eval, rename, evalKeyRef_rename]
    exact decide_eq_decide.mpr (renameKeyVal_injective p)
  | inGroup ref mask =>
    simp only [PureTest.eval, rename, evalKeyRef_rename]
    cases evalKeyRef fixedAtom st.slots keys ref <;> rfl
  | flag f ref =>
    simp only [PureTest.eval, rename, evalKeyRef_rename]
    cases evalKeyRef fixedAtom st.slots keys ref with
    | inl k => simp only [renameKeyVal, renameFlags, p.left]
    | inr a => rfl
  | msgEmpty ms =>
    simp only [PureTest.eval]
    exact allKeys_all_rename p _ _ (fun _ => rfl)
  | msgAll ms body ih =>
    simp only [PureTest.eval]
    apply allKeys_all_rename p
    intro k
    simp only [rename, renameMsgs]
    apply Bool.eq_iff_iff.mpr
    simp only [FinSet.all_eq_true]
    constructor
    · intro h mv hmv
      have hp := ih (push keys (p.invFun k)) { aux with metas := mv.1 :: aux.metas, vals := mv.2 :: aux.vals }
      rw [renameKeys_push, p.right] at hp
      exact hp ▸ h mv hmv
    · intro h mv hmv
      have hp := ih (push keys (p.invFun k)) { aux with metas := mv.1 :: aux.metas, vals := mv.2 :: aux.vals }
      rw [renameKeys_push, p.right] at hp
      exact hp.symm ▸ h mv hmv
  | msgSome ms body ih =>
    simp only [PureTest.eval]
    apply allKeys_any_rename p
    intro k
    simp only [rename, renameMsgs]
    apply Bool.eq_iff_iff.mpr
    simp only [FinSet.any_eq_true]
    constructor
    · rintro ⟨mv, hmv, hb⟩
      have hp := ih (push keys (p.invFun k)) { aux with metas := mv.1 :: aux.metas, vals := mv.2 :: aux.vals }
      rw [renameKeys_push, p.right] at hp
      exact ⟨mv, hmv, hp ▸ hb⟩
    · rintro ⟨mv, hmv, hb⟩
      have hp := ih (push keys (p.invFun k)) { aux with metas := mv.1 :: aux.metas, vals := mv.2 :: aux.vals }
      rw [renameKeys_push, p.right] at hp
      exact ⟨mv, hmv, hp.symm ▸ hb⟩
  | conj a b iha ihb => simp only [PureTest.eval, iha, ihb]
  | disj a b iha ihb => simp only [PureTest.eval, iha, ihb]
  | neg a iha => simp only [PureTest.eval, iha]
  | all mask body ih =>
    simp only [PureTest.eval]
    apply allKeys_all_rename p
    intro k
    have hp := ih (push keys (p.invFun k)) aux
    rw [renameKeys_push, p.right] at hp
    simp only [GroupPerm.invFun_fst, hp]
  | some mask body ih =>
    simp only [PureTest.eval]
    apply allKeys_any_rename p
    intro k
    have hp := ih (push keys (p.invFun k)) aux
    rw [renameKeys_push, p.right] at hp
    simp only [GroupPerm.invFun_fst, hp]
  | bindCount mask pred body ihp ihb =>
    simp only [PureTest.eval]
    have hc : countKeys sizes mask (fun k => pred.eval leafFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux) =
        countKeys sizes mask (fun k => pred.eval leafFn fixedAtom st (push keys k) aux) := by
      have hp' : (fun k => pred.eval leafFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux) =
          (fun k => pred.eval leafFn fixedAtom st (push keys (p.invFun k)) aux) := by
        funext k
        have h := ihp (push keys (p.invFun k)) aux
        rwa [renameKeys_push, p.right] at h
      rw [hp']
      exact countKeys_rename p mask (fun k => pred.eval leafFn fixedAtom st (push keys k) aux)
    rw [hc]
    exact ihb keys _

inductive PureExpr (d : Nat) (M S F MS : Type) where
  | leaf (spec : LeafSpec M S F)
  | branch (condition : PureTest d M S F MS) (yes no : PureExpr d M S F MS)
  | bindCount (mask : GroupMask d) (pred : PureTest d M S F MS) (body : PureExpr d M S F MS)

def PureExpr.eval {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A R : Type}
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → R)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) : PureExpr d M S F MS → R
  | .leaf spec => valFn spec.id (evalLeafSpec fixedAtom st keys aux spec)
  | .branch cond yes no =>
      if cond.eval testFn fixedAtom st keys aux then
        yes.eval testFn valFn fixedAtom st keys aux
      else
        no.eval testFn valFn fixedAtom st keys aux
  | .bindCount mask pred body =>
      let n := countKeys sizes mask (fun k => pred.eval testFn fixedAtom st (push keys k) aux)
      body.eval testFn valFn fixedAtom st keys { aux with nats := n :: aux.nats }

theorem PureExpr.equivariant {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A R : Type}
    (p : GroupPerm sizes) (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → R)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (e : PureExpr d M S F MS) (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    e.eval testFn valFn fixedAtom (rename p st) (renameKeys p keys) aux =
      e.eval testFn valFn fixedAtom st keys aux := by
  induction e generalizing keys aux with
  | leaf spec => simp only [PureExpr.eval, evalLeafSpec_rename]
  | branch cond yes no ihy ihn =>
    simp only [PureExpr.eval, PureTest.equivariant, ihy, ihn]
  | bindCount mask pred body ihb =>
    simp only [PureExpr.eval]
    have hc : countKeys sizes mask (fun k => pred.eval testFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux) =
        countKeys sizes mask (fun k => pred.eval testFn fixedAtom st (push keys k) aux) := by
      have hp' : (fun k => pred.eval testFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux) =
          (fun k => pred.eval testFn fixedAtom st (push keys (p.invFun k)) aux) := by
        funext k
        have h := PureTest.equivariant p testFn fixedAtom st pred (push keys (p.invFun k)) aux
        rwa [renameKeys_push, p.right] at h
      rw [hp']
      exact countKeys_rename p mask (fun k => pred.eval testFn fixedAtom st (push keys k) aux)
    rw [hc]
    exact ihb keys _

-- Explicit CHOOSE witness justifications.
inductive UniqueKind (d : Nat) (M S F MS : Type) where
  | eq (mask : GroupMask d) (target : KeyRef S) (extra : PureTest d M S F MS)
  | only (mask : GroupMask d) (q : PureTest d M S F MS)
  | atMostOneFlag (mask : GroupMask d) (flag : F) (extra : PureTest d M S F MS)

def UniqueKind.pred {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    UniqueKind d M S F MS → Key sizes → Bool := by
  classical
  exact fun uk k => match uk with
    | .eq mask target extra =>
        mask k.1 && extra.eval testFn fixedAtom st (push keys k) aux &&
          decide (evalKeyRef fixedAtom st.slots keys target = .inl k)
    | .only mask q =>
        mask k.1 && q.eval testFn fixedAtom st (push keys k) aux &&
          (allKeys sizes).all (fun y =>
            !(mask y.1 && q.eval testFn fixedAtom st (push keys y) aux) || decide (y = k))
    | .atMostOneFlag mask flag extra =>
        mask k.1 && st.flags flag k && extra.eval testFn fixedAtom st (push keys k) aux

def UniqueKind.eval {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (keyRank : Key sizes → Nat) (testFn : Nat → LeafArgs Meta V A → Bool)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) (uk : UniqueKind d M S F MS) :
    Option (Key sizes) :=
  chooseMinBy keyRank ((allKeys sizes).filter (uk.pred testFn fixedAtom st keys aux))

inductive ProjKind (d : Nat) (M S F MS : Type) where
  | keyConst (mask : GroupMask d) (filter : PureTest d M S F MS) (valExpr : PureExpr d M S F MS)
  | msgPinned (ms : MS) (filter : PureTest d M S F MS) (pinnedVal : PureExpr d M S F MS)
  | msgUniform (ms : MS) (filter : PureTest d M S F MS)

def ProjKind.eval {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    ProjKind d M S F MS → Option V := by
  classical
  exact fun pk => match pk with
    | .keyConst mask filter valExpr =>
        let v := valExpr.eval testFn valFn fixedAtom st keys aux
        (chooseMinBy keyRank ((allKeys sizes).filter (fun k =>
          mask k.1 && filter.eval testFn fixedAtom st (push keys k) aux))).map (fun _ => v)
    | .msgPinned ms filter pinnedVal =>
        let pv := pinnedVal.eval testFn valFn fixedAtom st keys aux
        let pred := fun (x : Key sizes × Meta × V) =>
          x.2 ∈ st.msgs ms x.1 ∧
            (filter.eval testFn fixedAtom st (push keys x.1)
              { aux with metas := x.2.1 :: aux.metas, vals := x.2.2 :: aux.vals } && decide (x.2.2 = pv)) = true
        (chooseMinPred (fun x => recRank x.1 x.2.1 x.2.2) pred).map (fun x => x.2.2)
    | .msgUniform ms filter =>
        let pred := fun (x : Key sizes × Meta × V) =>
          x.2 ∈ st.msgs ms x.1 ∧
            filter.eval testFn fixedAtom st (push keys x.1)
              { aux with metas := x.2.1 :: aux.metas, vals := x.2.2 :: aux.vals } = true
        (chooseMinPred (fun x => recRank x.1 x.2.1 x.2.2) pred).map (fun x => x.2.2)

-- Outer expressions propagating Option (`none` = CHOOSE empty-witness error) with TLA+ short-circuiting.
inductive ChoiceTest (d : Nat) (M S F MS : Type) where
  | pure (t : PureTest d M S F MS)
  | conj (left right : ChoiceTest d M S F MS)
  | disj (left right : ChoiceTest d M S F MS)
  | neg (body : ChoiceTest d M S F MS)
  | ite (cond yes no : ChoiceTest d M S F MS)
  | bindCount (mask : GroupMask d) (pred : PureTest d M S F MS) (body : ChoiceTest d M S F MS)
  | bindUnique (uk : UniqueKind d M S F MS) (body : ChoiceTest d M S F MS)
  | bindProj (pk : ProjKind d M S F MS) (body : ChoiceTest d M S F MS)
  | bindFold (mask : GroupMask d) (filter : PureTest d M S F MS) (term : PureExpr d M S F MS) (body : ChoiceTest d M S F MS)

def ChoiceTest.eval {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (intFn : Nat → LeafArgs Meta V A → Int)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    ChoiceTest d M S F MS → Option Bool
  | .pure t => some (t.eval testFn fixedAtom st keys aux)
  | .conj a b =>
      match a.eval keyRank recRank testFn valFn intFn fixedAtom st keys aux with
      | none => none
      | some false => some false
      | some true => b.eval keyRank recRank testFn valFn intFn fixedAtom st keys aux
  | .disj a b =>
      match a.eval keyRank recRank testFn valFn intFn fixedAtom st keys aux with
      | none => none
      | some true => some true
      | some false => b.eval keyRank recRank testFn valFn intFn fixedAtom st keys aux
  | .neg a => (a.eval keyRank recRank testFn valFn intFn fixedAtom st keys aux).map (!·)
  | .ite cond yes no =>
      match cond.eval keyRank recRank testFn valFn intFn fixedAtom st keys aux with
      | none => none
      | some true => yes.eval keyRank recRank testFn valFn intFn fixedAtom st keys aux
      | some false => no.eval keyRank recRank testFn valFn intFn fixedAtom st keys aux
  | .bindCount mask pred body =>
      let n := countKeys sizes mask (fun k => pred.eval testFn fixedAtom st (push keys k) aux)
      body.eval keyRank recRank testFn valFn intFn fixedAtom st keys { aux with nats := n :: aux.nats }
  | .bindUnique uk body =>
      match uk.eval keyRank testFn fixedAtom st keys aux with
      | none => none
      | some k => body.eval keyRank recRank testFn valFn intFn fixedAtom st (push keys k) aux
  | .bindProj pk body =>
      match pk.eval keyRank recRank testFn valFn fixedAtom st keys aux with
      | none => none
      | some v => body.eval keyRank recRank testFn valFn intFn fixedAtom st keys { aux with vals := v :: aux.vals }
  | .bindFold mask filter term body =>
      let z := chooseFoldAdd keyRank (allKeys sizes) (allKeys sizes).length
        (fun k => mask k.1 && filter.eval testFn fixedAtom st (push keys k) aux)
        (fun k => term.eval testFn intFn fixedAtom st (push keys k) aux)
      body.eval keyRank recRank testFn valFn intFn fixedAtom st keys { aux with ints := z :: aux.ints }

inductive ChoiceExpr (d : Nat) (M S F MS : Type) where
  | pure (e : PureExpr d M S F MS)
  | ite (cond : ChoiceTest d M S F MS) (yes no : ChoiceExpr d M S F MS)
  | bindCount (mask : GroupMask d) (pred : PureTest d M S F MS) (body : ChoiceExpr d M S F MS)
  | bindUnique (uk : UniqueKind d M S F MS) (body : ChoiceExpr d M S F MS)
  | bindProj (pk : ProjKind d M S F MS) (body : ChoiceExpr d M S F MS)
  | bindFold (mask : GroupMask d) (filter : PureTest d M S F MS) (term : PureExpr d M S F MS) (body : ChoiceExpr d M S F MS)

def ChoiceExpr.eval {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A R : Type}
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (intFn : Nat → LeafArgs Meta V A → Int)
    (outFn : Nat → LeafArgs Meta V A → R)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    ChoiceExpr d M S F MS → Option R
  | .pure e => some (e.eval testFn outFn fixedAtom st keys aux)
  | .ite cond yes no =>
      match cond.eval keyRank recRank testFn valFn intFn fixedAtom st keys aux with
      | none => none
      | some true => yes.eval keyRank recRank testFn valFn intFn outFn fixedAtom st keys aux
      | some false => no.eval keyRank recRank testFn valFn intFn outFn fixedAtom st keys aux
  | .bindCount mask pred body =>
      let n := countKeys sizes mask (fun k => pred.eval testFn fixedAtom st (push keys k) aux)
      body.eval keyRank recRank testFn valFn intFn outFn fixedAtom st keys { aux with nats := n :: aux.nats }
  | .bindUnique uk body =>
      match uk.eval keyRank testFn fixedAtom st keys aux with
      | none => none
      | some k => body.eval keyRank recRank testFn valFn intFn outFn fixedAtom st (push keys k) aux
  | .bindProj pk body =>
      match pk.eval keyRank recRank testFn valFn fixedAtom st keys aux with
      | none => none
      | some v => body.eval keyRank recRank testFn valFn intFn outFn fixedAtom st keys { aux with vals := v :: aux.vals }
  | .bindFold mask filter term body =>
      let z := chooseFoldAdd keyRank (allKeys sizes) (allKeys sizes).length
        (fun k => mask k.1 && filter.eval testFn fixedAtom st (push keys k) aux)
        (fun k => term.eval testFn intFn fixedAtom st (push keys k) aux)
      body.eval keyRank recRank testFn valFn intFn outFn fixedAtom st keys { aux with ints := z :: aux.ints }

inductive ChoiceSlotExpr (d : Nat) (M S F MS : Type) where
  | ref (target : KeyRef S)
  | fixedVal (e : PureExpr d M S F MS)
  | ite (cond : ChoiceTest d M S F MS) (yes no : ChoiceSlotExpr d M S F MS)
  | bindCount (mask : GroupMask d) (pred : PureTest d M S F MS) (body : ChoiceSlotExpr d M S F MS)
  | bindUnique (uk : UniqueKind d M S F MS) (body : ChoiceSlotExpr d M S F MS)
  | bindProj (pk : ProjKind d M S F MS) (body : ChoiceSlotExpr d M S F MS)
  | bindFold (mask : GroupMask d) (filter : PureTest d M S F MS) (term : PureExpr d M S F MS) (body : ChoiceSlotExpr d M S F MS)

def ChoiceSlotExpr.eval {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (intFn : Nat → LeafArgs Meta V A → Int)
    (fixedFn : Nat → LeafArgs Meta V A → A)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    ChoiceSlotExpr d M S F MS → Option (KeyVal (Key sizes) A)
  | .ref target => some (evalKeyRef fixedAtom st.slots keys target)
  | .fixedVal e => some (.inr (e.eval testFn fixedFn fixedAtom st keys aux))
  | .ite cond yes no =>
      match cond.eval keyRank recRank testFn valFn intFn fixedAtom st keys aux with
      | none => none
      | some true => yes.eval keyRank recRank testFn valFn intFn fixedFn fixedAtom st keys aux
      | some false => no.eval keyRank recRank testFn valFn intFn fixedFn fixedAtom st keys aux
  | .bindCount mask pred body =>
      let n := countKeys sizes mask (fun k => pred.eval testFn fixedAtom st (push keys k) aux)
      body.eval keyRank recRank testFn valFn intFn fixedFn fixedAtom st keys { aux with nats := n :: aux.nats }
  | .bindUnique uk body =>
      match uk.eval keyRank testFn fixedAtom st keys aux with
      | none => none
      | some k => body.eval keyRank recRank testFn valFn intFn fixedFn fixedAtom st (push keys k) aux
  | .bindProj pk body =>
      match pk.eval keyRank recRank testFn valFn fixedAtom st keys aux with
      | none => none
      | some v => body.eval keyRank recRank testFn valFn intFn fixedFn fixedAtom st keys { aux with vals := v :: aux.vals }
  | .bindFold mask filter term body =>
      let z := chooseFoldAdd keyRank (allKeys sizes) (allKeys sizes).length
        (fun k => mask k.1 && filter.eval testFn fixedAtom st (push keys k) aux)
        (fun k => term.eval testFn intFn fixedAtom st (push keys k) aux)
      body.eval keyRank recRank testFn valFn intFn fixedFn fixedAtom st keys { aux with ints := z :: aux.ints }

-- Initialization & Transition IR for Maps, Slots, Flags, and Msgs.
inductive Write (d : Nat) (M S F MS : Type) where
  | point (map : M) (target : KeyRef S) (value : ChoiceExpr d M S F MS)
  | all (map : M) (mask : GroupMask d) (value : ChoiceExpr d M S F MS)

def Write.apply {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    [DecidableEq M]
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (intFn : Nat → LeafArgs Meta V A → Int)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V)
    (current : Maps M (Key sizes) V) : Write d M S F MS → Option (Maps M (Key sizes) V)
  | .point map target val =>
      match evalKeyRef fixedAtom st.slots keys target with
      | .inl tk =>
          (val.eval keyRank recRank testFn valFn intFn valFn fixedAtom st keys aux).map
            (fun v m k => if m = map ∧ k = tk then v else current m k)
      | .inr _ => some current
  | .all map mask val =>
      let evalAt := fun k => val.eval keyRank recRank testFn valFn intFn valFn fixedAtom st (push keys k) aux
      if (allKeys sizes).all (fun k => !(mask k.1) || (evalAt k).isSome) then
        some (fun m k =>
          if m = map ∧ mask k.1 = true then
            match evalAt k with | some v => v | none => current m k
          else current m k)
      else
        none

def applyWrites {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    [DecidableEq M]
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (intFn : Nat → LeafArgs Meta V A → Int)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V)
    (writes : List (Write d M S F MS)) : Option (Maps M (Key sizes) V) :=
  writes.foldlM (fun cur w => Write.apply keyRank recRank testFn valFn intFn fixedAtom st keys aux cur w) st.maps

structure SlotWrite (d : Nat) (M S F MS : Type) where
  slot : S
  value : ChoiceSlotExpr d M S F MS

def SlotWrite.apply {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    [DecidableEq S]
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (intFn : Nat → LeafArgs Meta V A → Int)
    (fixedFn : Nat → LeafArgs Meta V A → A)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V)
    (current : Slots S (Key sizes) A) (w : SlotWrite d M S F MS) :
    Option (Slots S (Key sizes) A) :=
  (w.value.eval keyRank recRank testFn valFn intFn fixedFn fixedAtom st keys aux).map
    (fun kv s => if s = w.slot then kv else current s)

def applySlotWrites {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    [DecidableEq S]
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (intFn : Nat → LeafArgs Meta V A → Int)
    (fixedFn : Nat → LeafArgs Meta V A → A)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V)
    (writes : List (SlotWrite d M S F MS)) : Option (Slots S (Key sizes) A) :=
  writes.foldlM (fun cur w => SlotWrite.apply keyRank recRank testFn valFn intFn fixedFn fixedAtom st keys aux cur w) st.slots

inductive FlagInit (d : Nat) where
  | empty
  | singleton (mask : GroupMask d) (keyIdx : Nat)
  | all (mask : GroupMask d)
  | cardinal (mask : GroupMask d) (card : Nat)

def FlagInit.holds {d : Nat} {sizes : Fin d → Nat}
    (keys : Environment (Key sizes)) (fl : Key sizes → Bool) : FlagInit d → Prop
  | .empty => fl = fun _ => false
  | .singleton mask idx =>
      mask (keys idx).1 = true ∧ fl = fun k => decide (k = keys idx)
  | .all mask => fl = fun k => mask k.1
  | .cardinal mask card =>
      (∀ k, fl k = true → mask k.1 = true) ∧ countKeys sizes mask fl = card

inductive FlagStep (d : Nat) (M S F MS : Type) where
  | keep
  | clear
  | singleton (mask : GroupMask d) (target : KeyRef S)
  | clearPoint (target : KeyRef S)
  | setPoint (mask : GroupMask d) (target : KeyRef S)
  | generalAll (mask : GroupMask d) (pred : PureTest d M S F MS)
  | cardinal (mask : GroupMask d) (card : Nat)

def FlagStep.holds {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V)
    (f : F) (nextFl : Key sizes → Bool) : FlagStep d M S F MS → Prop := by
  classical
  exact fun step => match step with
    | .keep => nextFl = st.flags f
    | .clear => nextFl = fun _ => false
    | .singleton mask target =>
        match evalKeyRef fixedAtom st.slots keys target with
        | .inl tk => nextFl = fun k => mask tk.1 && decide (k = tk)
        | .inr _ => nextFl = fun _ => false
    | .clearPoint target =>
        nextFl = fun k =>
          if evalKeyRef fixedAtom st.slots keys target = .inl k then false else st.flags f k
    | .setPoint mask target =>
        nextFl = fun k =>
          if evalKeyRef fixedAtom st.slots keys target = .inl k ∧ mask k.1 = true then true else st.flags f k
    | .generalAll mask pred =>
        nextFl = fun k => mask k.1 && pred.eval testFn fixedAtom st (push keys k) aux
    | .cardinal mask card =>
        (∀ k, nextFl k = true → mask k.1 = true) ∧ countKeys sizes mask nextFl = card

inductive MsgInit (d : Nat) where
  | empty
  | comprehensionConst (mask : GroupMask d) (metaId : Nat) (constValId : Nat)
  | comprehensionCore (mask : GroupMask d) (metaId : Nat) (coreValId : Nat)

def MsgInit.eval {d : Nat} {sizes : Fin d → Nat} {C Meta V : Type}
    (constVal : Nat → V) (initMeta : Nat → C → Meta) (initCoreVal : Nat → C → V)
    (c : C) : MsgInit d → Key sizes → FinSet (Meta × V)
  | .empty => fun _ => FinSet.empty
  | .comprehensionConst mask metaId cid =>
      fun k => if mask k.1 then FinSet.singleton (initMeta metaId c, constVal cid) else FinSet.empty
  | .comprehensionCore mask metaId vid =>
      fun k => if mask k.1 then FinSet.singleton (initMeta metaId c, initCoreVal vid c) else FinSet.empty

inductive MsgStep (d : Nat) (M S F MS : Type) where
  | keep
  | clear
  | comprehensionAll (mask : GroupMask d) (metaExpr : PureExpr d M S F MS) (valExpr : PureExpr d M S F MS)
  | addConst (mask : GroupMask d) (target : KeyRef S) (metaExpr : PureExpr d M S F MS) (constValId : Nat)
  | addWhenEmpty (mask : GroupMask d) (target : KeyRef S) (metaExpr : PureExpr d M S F MS) (valExpr : PureExpr d M S F MS)
  | addMatchingGuard (mask : GroupMask d) (target : KeyRef S) (metaExpr : PureExpr d M S F MS) (ugIdx : Nat)
  | addGeneral (mask : GroupMask d) (target : KeyRef S) (metaExpr : PureExpr d M S F MS) (valExpr : PureExpr d M S F MS)

def MsgStep.eval {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    [DecidableEq MS]
    (constVal : Nat → V)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (metaFn : Nat → LeafArgs Meta V A → Meta)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (ugs : List (MS × PureExpr d M S F MS))
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V)
    (ms : MS) : MsgStep d M S F MS → Key sizes → FinSet (Meta × V)
  | .keep => st.msgs ms
  | .clear => fun _ => FinSet.empty
  | .comprehensionAll mask metaExpr valExpr =>
      let v := valExpr.eval testFn valFn fixedAtom st keys aux
      fun k => if mask k.1 then FinSet.singleton (metaExpr.eval testFn metaFn fixedAtom st (push keys k) aux, v) else FinSet.empty
  | .addConst mask target metaExpr cid =>
      match evalKeyRef fixedAtom st.slots keys target with
      | .inl tk =>
          let mv := (metaExpr.eval testFn metaFn fixedAtom st keys aux, constVal cid)
          fun k => if k = tk ∧ mask k.1 = true then FinSet.insert mv (st.msgs ms k) else st.msgs ms k
      | .inr _ => st.msgs ms
  | .addWhenEmpty mask target metaExpr valExpr =>
      match evalKeyRef fixedAtom st.slots keys target with
      | .inl tk =>
          let mv := (metaExpr.eval testFn metaFn fixedAtom st keys aux, valExpr.eval testFn valFn fixedAtom st keys aux)
          fun k => if k = tk ∧ mask k.1 = true then FinSet.insert mv (st.msgs ms k) else st.msgs ms k
      | .inr _ => st.msgs ms
  | .addMatchingGuard mask target metaExpr ugIdx =>
      match ugs[ugIdx]? with
      | some (ms', valExpr) =>
          if ms' = ms then
            match evalKeyRef fixedAtom st.slots keys target with
            | .inl tk =>
                let mv := (metaExpr.eval testFn metaFn fixedAtom st keys aux, valExpr.eval testFn valFn fixedAtom st keys aux)
                fun k => if k = tk ∧ mask k.1 = true then FinSet.insert mv (st.msgs ms k) else st.msgs ms k
            | .inr _ => st.msgs ms
          else st.msgs ms
      | none => st.msgs ms
  | .addGeneral mask target metaExpr valExpr =>
      match evalKeyRef fixedAtom st.slots keys target with
      | .inl tk =>
          let mv := (metaExpr.eval testFn metaFn fixedAtom st keys aux, valExpr.eval testFn valFn fixedAtom st keys aux)
          fun k => if k = tk ∧ mask k.1 = true then FinSet.insert mv (st.msgs ms k) else st.msgs ms k
      | .inr _ => st.msgs ms

inductive BranchChoice (d : Nat) (M S F MS : Type) where
  | uniqueKey (uk : UniqueKind d M S F MS)
  | projVal (pk : ProjKind d M S F MS)
  | foldInt (mask : GroupMask d) (filter : PureTest d M S F MS) (term : PureExpr d M S F MS)

def evalBranchChoices {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (intFn : Nat → LeafArgs Meta V A → Int)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    List (BranchChoice d M S F MS) → Option (Environment (Key sizes) × AuxEnv Meta V)
  | [] => some (keys, aux)
  | bc :: rest =>
      match bc with
      | .uniqueKey uk =>
          match uk.eval keyRank testFn fixedAtom st keys aux with
          | none => none
          | some k => evalBranchChoices keyRank recRank testFn valFn intFn fixedAtom st (push keys k) aux rest
      | .projVal pk =>
          match pk.eval keyRank recRank testFn valFn fixedAtom st keys aux with
          | none => none
          | some v => evalBranchChoices keyRank recRank testFn valFn intFn fixedAtom st keys { aux with vals := v :: aux.vals } rest
      | .foldInt mask filter term =>
          let z := chooseFoldAdd keyRank (allKeys sizes) (allKeys sizes).length
            (fun k => mask k.1 && filter.eval testFn fixedAtom st (push keys k) aux)
            (fun k => term.eval testFn intFn fixedAtom st (push keys k) aux)
          evalBranchChoices keyRank recRank testFn valFn intFn fixedAtom st keys { aux with ints := z :: aux.ints } rest

structure InitBranch (d : Nat) (F MS : Type) where
  flagInit : F → FlagInit d
  msgInit : MS → MsgInit d

structure StepBranch (d : Nat) (M S F MS : Type) where
  preGuard : PureTest d M S F MS
  uniformGuards : List (MS × PureExpr d M S F MS)
  choices : List (BranchChoice d M S F MS)
  postGuard : ChoiceTest d M S F MS
  writes : List (Write d M S F MS)
  slotWrites : List (SlotWrite d M S F MS)
  flagSteps : F → FlagStep d M S F MS
  msgSteps : MS → MsgStep d M S F MS

def evalUniformGuards {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V)
    (ugs : List (MS × PureExpr d M S F MS)) : Bool := by
  classical
  exact ugs.all (fun item =>
    let targetVal := item.2.eval testFn valFn fixedAtom st keys aux
    (allKeys sizes).all (fun k => (st.msgs item.1 k).all (fun mv => decide (mv.2 = targetVal))))

theorem evalUniformGuards_rename {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (p : GroupPerm sizes)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V)
    (ugs : List (MS × PureExpr d M S F MS)) :
    evalUniformGuards testFn valFn fixedAtom (rename p st) (renameKeys p keys) aux ugs =
      evalUniformGuards testFn valFn fixedAtom st keys aux ugs := by
  classical
  unfold evalUniformGuards
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, FinSet.all_eq_true]
  constructor
  · intro h item hitem k hk mv hmv
    have hp := h item hitem (p.toFun k) (mem_allKeys _) mv
    rw [PureExpr.equivariant p testFn valFn fixedAtom st item.2 keys aux] at hp
    simp only [rename_msgs, renameMsgs, p.left] at hp
    exact hp hmv
  · intro h item hitem k hk mv hmv
    rw [PureExpr.equivariant p testFn valFn fixedAtom st item.2 keys aux]
    exact h item hitem (p.invFun k) (mem_allKeys _) mv hmv

-- Inductive invariant specification and kernel-decidable structural soundness checkers.
structure InvSpec (d : Nat) (F MS : Type) where
  atMostOneFlags : List (F × GroupMask d)
  constValMsgs : List (MS × Nat)
  uniformValMsgs : List MS

def flagAtMostOne {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (f : F) (mask : GroupMask d) (st : RawState C M S F MS (Key sizes) Meta V A) : Prop :=
  (∀ k, st.flags f k = true → mask k.1 = true) ∧
  (∀ k1 k2, st.flags f k1 = true → st.flags f k2 = true → k1 = k2)

def msgConstVal {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (constVal : Nat → V) (ms : MS) (cid : Nat)
    (st : RawState C M S F MS (Key sizes) Meta V A) : Prop :=
  ∀ k mv, mv ∈ st.msgs ms k → mv.2 = constVal cid

def msgUniformVal {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (ms : MS) (st : RawState C M S F MS (Key sizes) Meta V A) : Prop :=
  ∀ k1 mv1 k2 mv2, mv1 ∈ st.msgs ms k1 → mv2 ∈ st.msgs ms k2 → mv1.2 = mv2.2

def maskImplies {d : Nat} (m1 m2 : GroupMask d) : Bool :=
  (List.finRange d).all (fun g => !(m1 g) || m2 g)

theorem maskImplies_sound {d : Nat} {m1 m2 : GroupMask d}
    (h : maskImplies m1 m2 = true) {g : Fin d} (hm : m1 g = true) : m2 g = true := by
  simp only [maskImplies, List.all_eq_true] at h
  have hg := h g (List.mem_finRange g)
  simpa [hm] using hg

def guardImpliesFlagEmpty {d : Nat} {M S F MS : Type} [DecidableEq F]
    (f : F) (mask : GroupMask d) : PureTest d M S F MS → Bool
  | .all gmask (.neg (.flag f' (.bound 0))) => decide (f' = f) && maskImplies mask gmask
  | .conj a b => guardImpliesFlagEmpty f mask a || guardImpliesFlagEmpty f mask b
  | _ => false

theorem guardImpliesFlagEmpty_sound {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    [DecidableEq F]
    (leafFn : Nat → LeafArgs Meta V A → Bool) (fixedAtom : Nat → A)
    (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V)
    (f : F) (mask : GroupMask d) (g : PureTest d M S F MS)
    (hok : guardImpliesFlagEmpty f mask g = true)
    (heval : g.eval leafFn fixedAtom st keys aux = true) :
    ∀ k : Key sizes, mask k.1 = true → st.flags f k = false := by
  induction g with
  | conj a b iha ihb =>
    simp only [guardImpliesFlagEmpty, Bool.or_eq_true] at hok
    simp only [PureTest.eval, Bool.and_eq_true] at heval
    rcases hok with ha | hb
    · exact iha ha heval.1
    · exact ihb hb heval.2
  | all gmask body _ =>
    cases body with
    | neg inner =>
      cases inner with
      | flag f' ref =>
        cases ref with
        | bound idx =>
          cases idx with
          | zero =>
            simp only [guardImpliesFlagEmpty, Bool.and_eq_true, decide_eq_true_eq] at hok
            rcases hok with ⟨rfl, hmask⟩
            intro k hmk
            have hgm : gmask k.1 = true := maskImplies_sound hmask hmk
            simp only [PureTest.eval, List.all_eq_true] at heval
            have hk := heval k (mem_allKeys k)
            simpa [hgm, evalKeyRef, push] using hk
          | succ _ => nomatch hok
        | _ => nomatch hok
      | _ => nomatch hok
    | _ => nomatch hok
  | _ => nomatch hok

def guardImpliesMsgEmpty {d : Nat} {M S F MS : Type} [DecidableEq MS]
    (ms : MS) : PureTest d M S F MS → Bool
  | .msgEmpty ms' => decide (ms' = ms)
  | .conj a b => guardImpliesMsgEmpty ms a || guardImpliesMsgEmpty ms b
  | _ => false

theorem guardImpliesMsgEmpty_sound {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    [DecidableEq MS]
    (leafFn : Nat → LeafArgs Meta V A → Bool) (fixedAtom : Nat → A)
    (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V)
    (ms : MS) (g : PureTest d M S F MS)
    (hok : guardImpliesMsgEmpty ms g = true)
    (heval : g.eval leafFn fixedAtom st keys aux = true) :
    ∀ k : Key sizes, st.msgs ms k = FinSet.empty := by
  induction g with
  | msgEmpty ms' =>
    simp only [guardImpliesMsgEmpty, decide_eq_true_eq] at hok
    subst hok
    simp only [PureTest.eval, List.all_eq_true, FinSet.isEmpty_iff] at heval
    intro k
    exact heval k (mem_allKeys k)
  | conj a b iha ihb =>
    simp only [guardImpliesMsgEmpty, Bool.or_eq_true] at hok
    simp only [PureTest.eval, Bool.and_eq_true] at heval
    rcases hok with ha | hb
    · exact iha ha heval.1
    · exact ihb hb heval.2
  | _ => nomatch hok

def checkFlagInitAtMostOne {d : Nat} (mask : GroupMask d) : FlagInit d → Bool
  | .empty => true
  | .singleton smask _ => maskImplies smask mask
  | _ => false

def checkFlagStepAtMostOne {d : Nat} {M S F MS : Type} [DecidableEq F]
    (f : F) (mask : GroupMask d) (preGuard : PureTest d M S F MS) : FlagStep d M S F MS → Bool
  | .keep => true
  | .clear => true
  | .singleton smask _ => maskImplies smask mask
  | .clearPoint _ => true
  | .setPoint smask _ => maskImplies smask mask && guardImpliesFlagEmpty f mask preGuard
  | _ => false

def checkMsgInitConst {d : Nat} (cid : Nat) : MsgInit d → Bool
  | .empty => true
  | .comprehensionConst _ _ cid' => decide (cid' = cid)
  | _ => false

def checkMsgStepConst {d : Nat} {M S F MS : Type} (cid : Nat) : MsgStep d M S F MS → Bool
  | .keep => true
  | .clear => true
  | .addConst _ _ _ cid' => decide (cid' = cid)
  | _ => false

def checkMsgInitUniform {d : Nat} : MsgInit d → Bool
  | .empty => true
  | .comprehensionConst _ _ _ => true
  | .comprehensionCore _ _ _ => true

def checkMsgStepUniform {d : Nat} {M S F MS : Type} [DecidableEq MS]
    (ms : MS) (b : StepBranch d M S F MS) : MsgStep d M S F MS → Bool
  | .keep => true
  | .clear => true
  | .comprehensionAll _ _ _ => true
  | .addWhenEmpty _ _ _ _ => guardImpliesMsgEmpty ms b.preGuard
  | .addMatchingGuard _ _ _ ugIdx =>
      b.choices.isEmpty &&
        match b.uniformGuards[ugIdx]? with
        | some (ms', _) => decide (ms' = ms)
        | none => false
  | _ => false

-- Structural check that every UniqueKind / ProjKind in an expression is backed by `InvSpec`.
def checkUniqueJustified {d : Nat} {M S F MS : Type} [DecidableEq F]
    (inv : InvSpec d F MS) : UniqueKind d M S F MS → Bool
  | .eq _ _ _ => true
  | .only _ _ => true
  | .atMostOneFlag mask flag _ =>
      inv.atMostOneFlags.any (fun item => decide (item.1 = flag) && maskImplies mask item.2)

def checkProjJustified {d : Nat} {M S F MS : Type} [DecidableEq MS]
    (inv : InvSpec d F MS) : ProjKind d M S F MS → Bool
  | .keyConst _ _ _ => true
  | .msgPinned _ _ _ => true
  | .msgUniform ms _ =>
      inv.uniformValMsgs.any (fun m => decide (m = ms)) ||
        inv.constValMsgs.any (fun item => decide (item.1 = ms))

def ChoiceTest.justified {d : Nat} {M S F MS : Type} [DecidableEq F] [DecidableEq MS]
    (inv : InvSpec d F MS) : ChoiceTest d M S F MS → Bool
  | .pure _ => true
  | .conj a b | .disj a b => a.justified inv && b.justified inv
  | .neg a => a.justified inv
  | .ite c y n => c.justified inv && y.justified inv && n.justified inv
  | .bindCount _ _ body => body.justified inv
  | .bindUnique uk body => checkUniqueJustified inv uk && body.justified inv
  | .bindProj pk body => checkProjJustified inv pk && body.justified inv
  | .bindFold _ _ _ body => body.justified inv

def ChoiceExpr.justified {d : Nat} {M S F MS : Type} [DecidableEq F] [DecidableEq MS]
    (inv : InvSpec d F MS) : ChoiceExpr d M S F MS → Bool
  | .pure _ => true
  | .ite c y n => c.justified inv && y.justified inv && n.justified inv
  | .bindCount _ _ body => body.justified inv
  | .bindUnique uk body => checkUniqueJustified inv uk && body.justified inv
  | .bindProj pk body => checkProjJustified inv pk && body.justified inv
  | .bindFold _ _ _ body => body.justified inv

def ChoiceSlotExpr.justified {d : Nat} {M S F MS : Type} [DecidableEq F] [DecidableEq MS]
    (inv : InvSpec d F MS) : ChoiceSlotExpr d M S F MS → Bool
  | .ref _ | .fixedVal _ => true
  | .ite c y n => c.justified inv && y.justified inv && n.justified inv
  | .bindCount _ _ body => body.justified inv
  | .bindUnique uk body => checkUniqueJustified inv uk && body.justified inv
  | .bindProj pk body => checkProjJustified inv pk && body.justified inv
  | .bindFold _ _ _ body => body.justified inv

def BranchChoice.justified {d : Nat} {M S F MS : Type} [DecidableEq F] [DecidableEq MS]
    (inv : InvSpec d F MS) : BranchChoice d M S F MS → Bool
  | .uniqueKey uk => checkUniqueJustified inv uk
  | .projVal pk => checkProjJustified inv pk
  | .foldInt _ _ _ => true

def Write.justified {d : Nat} {M S F MS : Type} [DecidableEq F] [DecidableEq MS]
    (inv : InvSpec d F MS) : Write d M S F MS → Bool
  | .point _ _ val | .all _ _ val => val.justified inv

def SlotWrite.justified {d : Nat} {M S F MS : Type} [DecidableEq F] [DecidableEq MS]
    (inv : InvSpec d F MS) (w : SlotWrite d M S F MS) : Bool :=
  w.value.justified inv

-- Two-state pure equivariant test IR for ACTION_CONSTRAINT and action PROPERTY ([][A]_sub).
inductive KeyRef2 (S : Type) where
  | bound (idx : Nat)
  | slot (primed : Bool) (slot : S)
  | fixed (id : Nat)

def evalKeyRef2 {d : Nat} {sizes : Fin d → Nat} {S A : Type}
    (fixedAtom : Nat → A) (u0 u1 : Slots S (Key sizes) A) (keys : Environment (Key sizes)) :
    KeyRef2 S → KeyVal (Key sizes) A
  | .bound i => .inl (keys i)
  | .slot false s => u0 s
  | .slot true s => u1 s
  | .fixed id => .inr (fixedAtom id)

theorem evalKeyRef2_rename {d : Nat} {sizes : Fin d → Nat} {S A : Type} (p : GroupPerm sizes)
    (fixedAtom : Nat → A) (u0 u1 : Slots S (Key sizes) A) (keys : Environment (Key sizes))
    (ref : KeyRef2 S) :
    evalKeyRef2 fixedAtom (renameSlots p u0) (renameSlots p u1) (renameKeys p keys) ref =
      renameKeyVal p (evalKeyRef2 fixedAtom u0 u1 keys ref) := by
  cases ref with
  | bound _ => rfl
  | slot pr _ => cases pr <;> rfl
  | fixed _ => rfl

structure LeafSpec2 (M S F : Type) where
  id : Nat
  mapReads : List (Bool × M × Nat)
  slotMapReads : List (Bool × M × Bool × S)
  slotFixedReads : List (Bool × S)
  flagReads : List (Bool × F × KeyRef2 S)

def evalLeafSpec2 {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (fixedAtom : Nat → A) (st0 st1 : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) (spec : LeafSpec2 M S F) :
    LeafArgs Meta V A where
  mapVals := spec.mapReads.map (fun item => (match item.1 with | false => st0.maps | true => st1.maps) item.2.1 (keys item.2.2))
  slotMapVals := spec.slotMapReads.map (fun item =>
    match (match item.2.2.1 with | false => st0.slots | true => st1.slots) item.2.2.2 with
    | .inl k => some ((match item.1 with | false => st0.maps | true => st1.maps) item.2.1 k)
    | .inr _ => none)
  slotFixedVals := spec.slotFixedReads.map (fun item =>
    match (match item.1 with | false => st0.slots | true => st1.slots) item.2 with
    | .inl _ => none
    | .inr a => some a)
  flagVals := spec.flagReads.map (fun item =>
    match evalKeyRef2 fixedAtom st0.slots st1.slots keys item.2.2 with
    | .inl k => (match item.1 with | false => st0.flags | true => st1.flags) item.2.1 k
    | .inr _ => false)
  aux := aux

theorem evalLeafSpec2_rename {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (p : GroupPerm sizes) (fixedAtom : Nat → A)
    (st0 st1 : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) (spec : LeafSpec2 M S F) :
    evalLeafSpec2 fixedAtom (rename p st0) (rename p st1) (renameKeys p keys) aux spec =
      evalLeafSpec2 fixedAtom st0 st1 keys aux spec := by
  simp only [evalLeafSpec2, rename, LeafArgs.mk.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply List.map_congr_left
    rintro ⟨pr, m, idx⟩ _
    cases pr <;> simp [renameMaps, renameKeys, p.left]
  · apply List.map_congr_left
    rintro ⟨prM, m, prS, s⟩ _
    cases prM <;> cases prS <;> simp only [renameSlots]
    · cases st0.slots s with | inl k => simp only [renameKeyVal, renameMaps, p.left] | inr _ => rfl
    · cases st1.slots s with | inl k => simp only [renameKeyVal, renameMaps, p.left] | inr _ => rfl
    · cases st0.slots s with | inl k => simp only [renameKeyVal, renameMaps, p.left] | inr _ => rfl
    · cases st1.slots s with | inl k => simp only [renameKeyVal, renameMaps, p.left] | inr _ => rfl
  · apply List.map_congr_left
    rintro ⟨prS, s⟩ _
    cases prS <;> simp only [renameSlots]
    · cases st0.slots s <;> rfl
    · cases st1.slots s <;> rfl
  · apply List.map_congr_left
    rintro ⟨prF, f, ref⟩ _
    rw [evalKeyRef2_rename]
    cases evalKeyRef2 fixedAtom st0.slots st1.slots keys ref with
    | inl k => cases prF <;> simp only [renameKeyVal, renameFlags, p.left]
    | inr _ => rfl

inductive ActionPureTest (d : Nat) (M S F MS : Type) where
  | truth (value : Bool)
  | leaf (spec : LeafSpec2 M S F)
  | equal (left right : KeyRef2 S)
  | inGroup (key : KeyRef2 S) (mask : GroupMask d)
  | flag (primed : Bool) (f : F) (key : KeyRef2 S)
  | msgEq (ms : MS) (key : KeyRef2 S)
  | conj (left right : ActionPureTest d M S F MS)
  | disj (left right : ActionPureTest d M S F MS)
  | neg (body : ActionPureTest d M S F MS)
  | all (mask : GroupMask d) (body : ActionPureTest d M S F MS)
  | some (mask : GroupMask d) (body : ActionPureTest d M S F MS)

def ActionPureTest.eval {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (fixedAtom : Nat → A) (st0 st1 : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) : ActionPureTest d M S F MS → Bool := by
  classical
  exact fun t => match t with
    | .truth b => b
    | .leaf spec => testFn spec.id (evalLeafSpec2 fixedAtom st0 st1 keys aux spec)
    | .equal a b => decide (evalKeyRef2 fixedAtom st0.slots st1.slots keys a = evalKeyRef2 fixedAtom st0.slots st1.slots keys b)
    | .inGroup ref mask =>
        match evalKeyRef2 fixedAtom st0.slots st1.slots keys ref with
        | .inl k => mask k.1
        | .inr _ => false
    | .flag pr f ref =>
        match evalKeyRef2 fixedAtom st0.slots st1.slots keys ref with
        | .inl k => (match pr with | false => st0.flags | true => st1.flags) f k
        | .inr _ => false
    | .msgEq ms ref =>
        match evalKeyRef2 fixedAtom st0.slots st1.slots keys ref with
        | .inl k => decide (st1.msgs ms k = st0.msgs ms k)
        | .inr _ => true
    | .conj a b => a.eval testFn fixedAtom st0 st1 keys aux && b.eval testFn fixedAtom st0 st1 keys aux
    | .disj a b => a.eval testFn fixedAtom st0 st1 keys aux || b.eval testFn fixedAtom st0 st1 keys aux
    | .neg a => !(a.eval testFn fixedAtom st0 st1 keys aux)
    | .all mask a => (allKeys sizes).all (fun k => !mask k.1 || a.eval testFn fixedAtom st0 st1 (push keys k) aux)
    | .some mask a => (allKeys sizes).any (fun k => mask k.1 && a.eval testFn fixedAtom st0 st1 (push keys k) aux)

theorem ActionPureTest.equivariant {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
    (p : GroupPerm sizes) (testFn : Nat → LeafArgs Meta V A → Bool)
    (fixedAtom : Nat → A) (st0 st1 : RawState C M S F MS (Key sizes) Meta V A)
    (t : ActionPureTest d M S F MS) (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    t.eval testFn fixedAtom (rename p st0) (rename p st1) (renameKeys p keys) aux =
      t.eval testFn fixedAtom st0 st1 keys aux := by
  classical
  induction t generalizing keys aux with
  | truth _ => rfl
  | leaf spec =>
    simp only [ActionPureTest.eval, evalLeafSpec2_rename]
  | equal a b =>
    simp only [ActionPureTest.eval, rename_slots, evalKeyRef2_rename]
    exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq, renameKeyVal_injective])
  | inGroup ref mask =>
    simp only [ActionPureTest.eval, rename_slots, evalKeyRef2_rename]
    cases evalKeyRef2 fixedAtom st0.slots st1.slots keys ref <;> rfl
  | flag pr f ref =>
    simp only [ActionPureTest.eval, rename_slots, evalKeyRef2_rename]
    cases evalKeyRef2 fixedAtom st0.slots st1.slots keys ref with
    | inl k => cases pr <;> simp only [renameKeyVal, rename_flags, renameFlags, p.left]
    | inr _ => rfl
  | msgEq ms ref =>
    simp only [ActionPureTest.eval, rename_slots, evalKeyRef2_rename]
    cases evalKeyRef2 fixedAtom st0.slots st1.slots keys ref with
    | inl k => simp only [renameKeyVal, rename_msgs, renameMsgs, p.left]
    | inr _ => rfl
  | conj a b ha hb => simp only [ActionPureTest.eval, ha, hb]
  | disj a b ha hb => simp only [ActionPureTest.eval, ha, hb]
  | neg a ha => simp only [ActionPureTest.eval, ha]
  | all mask a ha =>
    simp only [ActionPureTest.eval]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    constructor
    · intro h k _
      have hk := h (p.toFun k) (mem_allKeys _)
      simp only [GroupPerm.toFun_fst] at hk
      have ha' := ha (push keys k) aux
      rw [renameKeys_push] at ha'
      rwa [ha'] at hk
    · intro h k _
      have hk := h (p.invFun k) (mem_allKeys _)
      simp only [GroupPerm.invFun_fst] at hk
      have ha' := ha (push keys (p.invFun k)) aux
      rw [renameKeys_push, p.right] at ha'
      rwa [ha']
  | some mask a ha =>
    simp only [ActionPureTest.eval]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨k, _, hm, hb⟩
      refine ⟨p.invFun k, mem_allKeys _, hm, ?_⟩
      have ha' := ha (push keys (p.invFun k)) aux
      rw [renameKeys_push, p.right] at ha'
      rwa [ha'] at hb
    · rintro ⟨k, _, hm, hb⟩
      refine ⟨p.toFun k, mem_allKeys _, hm, ?_⟩
      have ha' := ha (push keys k) aux
      rw [renameKeys_push] at ha'
      rwa [ha']

-- Full Operations & Model bundle (Semantics has ZERO propositional premises!).
structure Operations (d : Nat) (M S F MS IB B : Type) where
  inv : InvSpec d F MS
  initBranch : IB → InitBranch d F MS
  stepBranch : B → StepBranch d M S F MS
  observation : ChoiceTest d M S F MS
  initObservation : ChoiceTest d M S F MS := .pure (.truth true)
  constraintTest : ChoiceTest d M S F MS := .pure (.truth true)
  actionConstraintTest : ActionPureTest d M S F MS := .truth true
  actionObservation : ActionPureTest d M S F MS := .truth true

def checkOperationsValid {d : Nat} {M S F MS IB B : Type}
    [DecidableEq F] [DecidableEq MS]
    (allIB : List IB) (allB : List B) (ops : Operations d M S F MS IB B) : Bool :=
  ops.inv.atMostOneFlags.all (fun fm =>
    allIB.all (fun ib => checkFlagInitAtMostOne fm.2 ((ops.initBranch ib).flagInit fm.1)) &&
    allB.all (fun b =>
      let sb := ops.stepBranch b
      checkFlagStepAtMostOne fm.1 fm.2 sb.preGuard (sb.flagSteps fm.1))) &&
  ops.inv.constValMsgs.all (fun mc =>
    allIB.all (fun ib => checkMsgInitConst mc.2 ((ops.initBranch ib).msgInit mc.1)) &&
    allB.all (fun b => checkMsgStepConst mc.2 ((ops.stepBranch b).msgSteps mc.1))) &&
  ops.inv.uniformValMsgs.all (fun ms =>
    allIB.all (fun ib => checkMsgInitUniform ((ops.initBranch ib).msgInit ms)) &&
    allB.all (fun b =>
      let sb := ops.stepBranch b
      checkMsgStepUniform ms sb (sb.msgSteps ms))) &&
  allB.all (fun b =>
    let sb := ops.stepBranch b
    sb.choices.all (BranchChoice.justified ops.inv) &&
    sb.postGuard.justified ops.inv &&
    sb.writes.all (Write.justified ops.inv) &&
    sb.slotWrites.all (SlotWrite.justified ops.inv)) &&
  ops.observation.justified ops.inv &&
  ops.initObservation.justified ops.inv &&
  ops.constraintTest.justified ops.inv

structure Semantics (d : Nat) (sizes : Fin d → Nat) (C M S Meta V A IB B W : Type) where
  keyRank : Key sizes → Nat
  recRank : Key sizes → Meta → V → Nat
  fixedAtom : Nat → A
  constVal : Nat → V
  initMeta : Nat → C → Meta
  initCoreVal : Nat → C → V
  initSetup : IB → C → Maps M (Key sizes) V → Slots S (Key sizes) A → Environment (Key sizes) → W → Prop
  stepTest : B → C → C → W → Nat → LeafArgs Meta V A → Bool
  stepVal : B → C → C → W → Nat → LeafArgs Meta V A → V
  stepMeta : B → C → C → W → Nat → LeafArgs Meta V A → Meta
  stepInt : B → C → C → W → Nat → LeafArgs Meta V A → Int
  stepFixed : B → C → C → W → Nat → LeafArgs Meta V A → A
  obsTest : C → Nat → LeafArgs Meta V A → Bool
  obsVal : C → Nat → LeafArgs Meta V A → V
  obsInt : C → Nat → LeafArgs Meta V A → Int
  actionTest : C → C → Nat → LeafArgs Meta V A → Bool := fun _ _ _ _ => true

-- Equivariance of justified CHOOSE expressions on invariant-satisfying states.
section Equivariance
variable {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A : Type}
  [DecidableEq M] [DecidableEq S] [DecidableEq F] [DecidableEq MS]

def invHolds (constVal : Nat → V) (inv : InvSpec d F MS)
    (st : RawState C M S F MS (Key sizes) Meta V A) : Prop :=
  (∀ fm ∈ inv.atMostOneFlags, flagAtMostOne fm.1 fm.2 st) ∧
  (∀ mc ∈ inv.constValMsgs, msgConstVal constVal mc.1 mc.2 st) ∧
  (∀ ms ∈ inv.uniformValMsgs, msgUniformVal ms st)

theorem UniqueKind.equivariant
    (p : GroupPerm sizes) (constVal : Nat → V) (inv : InvSpec d F MS)
    (keyRank : Key sizes → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (hinv : invHolds constVal inv st)
    (uk : UniqueKind d M S F MS) (hjust : checkUniqueJustified inv uk = true)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    uk.eval keyRank testFn fixedAtom (rename p st) (renameKeys p keys) aux =
      (uk.eval keyRank testFn fixedAtom st keys aux).map p.toFun := by
  classical
  apply chooseUnique_equivariant p keyRank
  · intro k
    cases uk with
    | eq mask target extra =>
      unfold UniqueKind.pred
      have he := PureTest.equivariant p testFn fixedAtom st extra (push keys (p.invFun k)) aux
      rw [renameKeys_push, p.right] at he
      have hdec : decide (evalKeyRef fixedAtom (rename p st).slots (renameKeys p keys) target = .inl k) =
          decide (evalKeyRef fixedAtom st.slots keys target = .inl (p.invFun k)) := by
        rw [rename_slots, evalKeyRef_rename]
        apply decide_eq_decide.mpr
        cases evalKeyRef fixedAtom st.slots keys target with
        | inl tk =>
          simp only [renameKeyVal, Sum.inl.injEq]
          constructor
          · intro h; rw [← h, p.left]
          · intro h; rw [h, p.right]
        | inr a => simp [renameKeyVal]
      simp only [GroupPerm.invFun_fst, he, hdec]
    | only mask q =>
      unfold UniqueKind.pred
      have hq := PureTest.equivariant p testFn fixedAtom st q (push keys (p.invFun k)) aux
      rw [renameKeys_push, p.right] at hq
      simp only [GroupPerm.invFun_fst, hq]
      congr 1
      apply allKeys_all_rename p
      intro y
      have hqy := PureTest.equivariant p testFn fixedAtom st q (push keys (p.invFun y)) aux
      rw [renameKeys_push, p.right] at hqy
      simp only [GroupPerm.invFun_fst, hqy]
      exact congrArg _ (decide_eq_decide.mpr (p.inv_injective).symm)
    | atMostOneFlag mask flag extra =>
      unfold UniqueKind.pred
      have he := PureTest.equivariant p testFn fixedAtom st extra (push keys (p.invFun k)) aux
      rw [renameKeys_push, p.right] at he
      simp only [GroupPerm.invFun_fst, rename_flags, renameFlags, he]
  · intro k1 k2 h1 h2
    cases uk with
    | eq mask target extra =>
      simp only [UniqueKind.pred, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
      have h12 := h1.2.symm.trans h2.2
      injection h12
    | only mask q =>
      simp only [UniqueKind.pred, Bool.and_eq_true, List.all_eq_true] at h1 h2
      have hk2 := h1.2 k2 (mem_allKeys k2)
      simp only [h2.1.1, h2.1.2, Bool.and_self, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hk2
      exact Eq.symm hk2
    | atMostOneFlag mask flag extra =>
      have h_amo : ∃ x ∈ inv.atMostOneFlags, x.1 = flag ∧ maskImplies mask x.2 = true := by
        simpa only [checkUniqueJustified, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] using hjust
      rcases h_amo with ⟨⟨f', m'⟩, hmem, hf_eq, _⟩
      subst hf_eq
      have hamo := hinv.1 (f', m') hmem
      simp only [UniqueKind.pred, Bool.and_eq_true] at h1 h2
      exact hamo.2 k1 k2 h1.1.2 h2.1.2

theorem ProjKind.equivariant
    (p : GroupPerm sizes) (constVal : Nat → V) (inv : InvSpec d F MS)
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (hinv : invHolds constVal inv st)
    (pk : ProjKind d M S F MS) (hjust : checkProjJustified inv pk = true)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    pk.eval keyRank recRank testFn valFn fixedAtom (rename p st) (renameKeys p keys) aux =
      pk.eval keyRank recRank testFn valFn fixedAtom st keys aux := by
  classical
  cases pk with
  | keyConst mask filter valExpr =>
    simp only [ProjKind.eval]
    rw [PureExpr.equivariant p testFn valFn fixedAtom st valExpr keys aux]
    apply chooseKeyProj_equivariant p keyRank
    · intro k
      have hf := PureTest.equivariant p testFn fixedAtom st filter (push keys (p.invFun k)) aux
      rw [renameKeys_push, p.right] at hf
      simp only [GroupPerm.invFun_fst, hf]
    · intro _; rfl
    · intro _ _ _ _; rfl
  | msgPinned ms filter pinnedVal =>
    simp only [ProjKind.eval]
    rw [PureExpr.equivariant p testFn valFn fixedAtom st pinnedVal keys aux]
    let pv := pinnedVal.eval testFn valFn fixedAtom st keys aux
    exact chooseMsgProj_equivariant p recRank (st.msgs ms) ((rename p st).msgs ms)
      (fun k m v => filter.eval testFn fixedAtom st (push keys k)
        { aux with metas := m :: aux.metas, vals := v :: aux.vals } && decide (v = pv))
      (fun k m v => filter.eval testFn fixedAtom (rename p st) (push (renameKeys p keys) k)
        { aux with metas := m :: aux.metas, vals := v :: aux.vals } && decide (v = pv))
      (fun _ => rfl)
      (fun k m v => by
        have hf := PureTest.equivariant p testFn fixedAtom st filter (push keys (p.invFun k))
          { aux with metas := m :: aux.metas, vals := v :: aux.vals }
        rw [renameKeys_push, p.right] at hf
        simp only [hf])
      (fun k1 m1 v1 k2 m2 v2 _ hf1 _ hf2 => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hf1 hf2
        exact hf1.2.trans hf2.2.symm)
  | msgUniform ms filter =>
    simp only [ProjKind.eval]
    exact chooseMsgProj_equivariant p recRank (st.msgs ms) ((rename p st).msgs ms)
      (fun k m v => filter.eval testFn fixedAtom st (push keys k)
        { aux with metas := m :: aux.metas, vals := v :: aux.vals })
      (fun k m v => filter.eval testFn fixedAtom (rename p st) (push (renameKeys p keys) k)
        { aux with metas := m :: aux.metas, vals := v :: aux.vals })
      (fun _ => rfl)
      (fun k m v => by
        have hf := PureTest.equivariant p testFn fixedAtom st filter (push keys (p.invFun k))
          { aux with metas := m :: aux.metas, vals := v :: aux.vals }
        rw [renameKeys_push, p.right] at hf
        simp only [hf])
      (fun k1 m1 v1 k2 m2 v2 hs1 _ hs2 _ => by
        have h_unif : (∃ ms' ∈ inv.uniformValMsgs, ms' = ms) ∨ (∃ x ∈ inv.constValMsgs, x.1 = ms) := by
          simpa only [checkProjJustified, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] using hjust
        rcases h_unif with ⟨ms', hmem, hms_eq⟩ | ⟨⟨ms', cid⟩, hmem, hms_eq⟩
        · subst hms_eq
          exact hinv.2.2 ms' hmem k1 (m1, v1) k2 (m2, v2) hs1 hs2
        · subst hms_eq
          have hc := hinv.2.1 (ms', cid) hmem
          exact (hc k1 (m1, v1) hs1).trans (hc k2 (m2, v2) hs2).symm)

theorem ChoiceTest.equivariant
    (p : GroupPerm sizes) (constVal : Nat → V) (inv : InvSpec d F MS)
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (intFn : Nat → LeafArgs Meta V A → Int)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (hinv : invHolds constVal inv st)
    (t : ChoiceTest d M S F MS) (hjust : t.justified inv = true)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    t.eval keyRank recRank testFn valFn intFn fixedAtom (rename p st) (renameKeys p keys) aux =
      t.eval keyRank recRank testFn valFn intFn fixedAtom st keys aux := by
  induction t generalizing keys aux with
  | pure pt => simp only [ChoiceTest.eval, PureTest.equivariant]
  | conj a b iha ihb =>
    simp only [ChoiceTest.justified, Bool.and_eq_true] at hjust
    simp only [ChoiceTest.eval, iha hjust.1 keys aux]
    cases a.eval keyRank recRank testFn valFn intFn fixedAtom st keys aux with
    | none => rfl
    | some bv => cases bv <;> simp only [ihb hjust.2 keys aux]
  | disj a b iha ihb =>
    simp only [ChoiceTest.justified, Bool.and_eq_true] at hjust
    simp only [ChoiceTest.eval, iha hjust.1 keys aux]
    cases a.eval keyRank recRank testFn valFn intFn fixedAtom st keys aux with
    | none => rfl
    | some bv => cases bv <;> simp only [ihb hjust.2 keys aux]
  | neg a iha =>
    simp only [ChoiceTest.justified] at hjust
    simp only [ChoiceTest.eval, iha hjust keys aux]
  | ite c y n ihc ihy ihn =>
    simp only [ChoiceTest.justified, Bool.and_eq_true] at hjust
    simp only [ChoiceTest.eval, ihc hjust.1.1 keys aux]
    cases c.eval keyRank recRank testFn valFn intFn fixedAtom st keys aux with
    | none => rfl
    | some bv => cases bv <;> simp only [ihy hjust.1.2 keys aux, ihn hjust.2 keys aux]
  | bindCount mask pred body ihb =>
    simp only [ChoiceTest.justified] at hjust
    simp only [ChoiceTest.eval]
    have hc : countKeys sizes mask (fun k => pred.eval testFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux) =
        countKeys sizes mask (fun k => pred.eval testFn fixedAtom st (push keys k) aux) := by
      have hp' : (fun k => pred.eval testFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux) =
          (fun k => pred.eval testFn fixedAtom st (push keys (p.invFun k)) aux) := by
        funext k
        have h := PureTest.equivariant p testFn fixedAtom st pred (push keys (p.invFun k)) aux
        rwa [renameKeys_push, p.right] at h
      rw [hp']
      exact countKeys_rename p mask (fun k => pred.eval testFn fixedAtom st (push keys k) aux)
    rw [hc]
    exact ihb hjust keys _
  | bindUnique uk body ihb =>
    simp only [ChoiceTest.justified, Bool.and_eq_true] at hjust
    simp only [ChoiceTest.eval, UniqueKind.equivariant p constVal inv keyRank testFn fixedAtom st hinv uk hjust.1 keys aux]
    cases uk.eval keyRank testFn fixedAtom st keys aux with
    | none => rfl
    | some k =>
      simp only [Option.map_some, ← renameKeys_push]
      exact ihb hjust.2 (push keys k) aux
  | bindProj pk body ihb =>
    simp only [ChoiceTest.justified, Bool.and_eq_true] at hjust
    simp only [ChoiceTest.eval, ProjKind.equivariant p constVal inv keyRank recRank testFn valFn fixedAtom st hinv pk hjust.1 keys aux]
    cases pk.eval keyRank recRank testFn valFn fixedAtom st keys aux with
    | none => rfl
    | some v => exact ihb hjust.2 keys { aux with vals := v :: aux.vals }
  | bindFold mask filter term body ihb =>
    simp only [ChoiceTest.justified] at hjust
    simp only [ChoiceTest.eval]
    have hf : chooseFoldAdd keyRank (allKeys sizes) (allKeys sizes).length
        (fun k => mask k.1 && filter.eval testFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux)
        (fun k => term.eval testFn intFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux) =
      chooseFoldAdd keyRank (allKeys sizes) (allKeys sizes).length
        (fun k => mask k.1 && filter.eval testFn fixedAtom st (push keys k) aux)
        (fun k => term.eval testFn intFn fixedAtom st (push keys k) aux) := by
      apply chooseFoldAdd_rename p keyRank
      · intro k
        have h := PureTest.equivariant p testFn fixedAtom st filter (push keys (p.invFun k)) aux
        rw [renameKeys_push, p.right] at h
        simp only [GroupPerm.invFun_fst, h]
      · intro k
        have h := PureExpr.equivariant p testFn intFn fixedAtom st term (push keys (p.invFun k)) aux
        rwa [renameKeys_push, p.right] at h
    rw [hf]
    exact ihb hjust keys _

theorem ChoiceExpr.equivariant {R : Type}
    (p : GroupPerm sizes) (constVal : Nat → V) (inv : InvSpec d F MS)
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (intFn : Nat → LeafArgs Meta V A → Int)
    (outFn : Nat → LeafArgs Meta V A → R)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (hinv : invHolds constVal inv st)
    (e : ChoiceExpr d M S F MS) (hjust : e.justified inv = true)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    e.eval keyRank recRank testFn valFn intFn outFn fixedAtom (rename p st) (renameKeys p keys) aux =
      e.eval keyRank recRank testFn valFn intFn outFn fixedAtom st keys aux := by
  induction e generalizing keys aux with
  | pure pe => simp only [ChoiceExpr.eval, PureExpr.equivariant]
  | ite c y n ihy ihn =>
    simp only [ChoiceExpr.justified, Bool.and_eq_true] at hjust
    simp only [ChoiceExpr.eval, ChoiceTest.equivariant p constVal inv keyRank recRank testFn valFn intFn fixedAtom st hinv c hjust.1.1 keys aux]
    cases c.eval keyRank recRank testFn valFn intFn fixedAtom st keys aux with
    | none => rfl
    | some bv => cases bv <;> simp only [ihy hjust.1.2 keys aux, ihn hjust.2 keys aux]
  | bindCount mask pred body ihb =>
    simp only [ChoiceExpr.justified] at hjust
    simp only [ChoiceExpr.eval]
    have hc : countKeys sizes mask (fun k => pred.eval testFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux) =
        countKeys sizes mask (fun k => pred.eval testFn fixedAtom st (push keys k) aux) := by
      have hp' : (fun k => pred.eval testFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux) =
          (fun k => pred.eval testFn fixedAtom st (push keys (p.invFun k)) aux) := by
        funext k
        have h := PureTest.equivariant p testFn fixedAtom st pred (push keys (p.invFun k)) aux
        rwa [renameKeys_push, p.right] at h
      rw [hp']
      exact countKeys_rename p mask (fun k => pred.eval testFn fixedAtom st (push keys k) aux)
    rw [hc]
    exact ihb hjust keys _
  | bindUnique uk body ihb =>
    simp only [ChoiceExpr.justified, Bool.and_eq_true] at hjust
    simp only [ChoiceExpr.eval, UniqueKind.equivariant p constVal inv keyRank testFn fixedAtom st hinv uk hjust.1 keys aux]
    cases uk.eval keyRank testFn fixedAtom st keys aux with
    | none => rfl
    | some k =>
      simp only [Option.map_some, ← renameKeys_push]
      exact ihb hjust.2 (push keys k) aux
  | bindProj pk body ihb =>
    simp only [ChoiceExpr.justified, Bool.and_eq_true] at hjust
    simp only [ChoiceExpr.eval, ProjKind.equivariant p constVal inv keyRank recRank testFn valFn fixedAtom st hinv pk hjust.1 keys aux]
    cases pk.eval keyRank recRank testFn valFn fixedAtom st keys aux with
    | none => rfl
    | some v => exact ihb hjust.2 keys { aux with vals := v :: aux.vals }
  | bindFold mask filter term body ihb =>
    simp only [ChoiceExpr.justified] at hjust
    simp only [ChoiceExpr.eval]
    have hf : chooseFoldAdd keyRank (allKeys sizes) (allKeys sizes).length
        (fun k => mask k.1 && filter.eval testFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux)
        (fun k => term.eval testFn intFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux) =
      chooseFoldAdd keyRank (allKeys sizes) (allKeys sizes).length
        (fun k => mask k.1 && filter.eval testFn fixedAtom st (push keys k) aux)
        (fun k => term.eval testFn intFn fixedAtom st (push keys k) aux) := by
      apply chooseFoldAdd_rename p keyRank
      · intro k
        have h := PureTest.equivariant p testFn fixedAtom st filter (push keys (p.invFun k)) aux
        rw [renameKeys_push, p.right] at h
        simp only [GroupPerm.invFun_fst, h]
      · intro k
        have h := PureExpr.equivariant p testFn intFn fixedAtom st term (push keys (p.invFun k)) aux
        rwa [renameKeys_push, p.right] at h
    rw [hf]
    exact ihb hjust keys _

theorem ChoiceSlotExpr.equivariant
    (p : GroupPerm sizes) (constVal : Nat → V) (inv : InvSpec d F MS)
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (intFn : Nat → LeafArgs Meta V A → Int)
    (fixedFn : Nat → LeafArgs Meta V A → A)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (hinv : invHolds constVal inv st)
    (e : ChoiceSlotExpr d M S F MS) (hjust : e.justified inv = true)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    e.eval keyRank recRank testFn valFn intFn fixedFn fixedAtom (rename p st) (renameKeys p keys) aux =
      (e.eval keyRank recRank testFn valFn intFn fixedFn fixedAtom st keys aux).map (renameKeyVal p) := by
  induction e generalizing keys aux with
  | ref target =>
    simp only [ChoiceSlotExpr.eval, rename, evalKeyRef_rename, Option.map_some]
  | fixedVal pe =>
    simp only [ChoiceSlotExpr.eval, PureExpr.equivariant, Option.map_some, renameKeyVal]
  | ite c y n ihy ihn =>
    simp only [ChoiceSlotExpr.justified, Bool.and_eq_true] at hjust
    simp only [ChoiceSlotExpr.eval, ChoiceTest.equivariant p constVal inv keyRank recRank testFn valFn intFn fixedAtom st hinv c hjust.1.1 keys aux]
    cases c.eval keyRank recRank testFn valFn intFn fixedAtom st keys aux with
    | none => rfl
    | some bv => cases bv <;> simp only [ihy hjust.1.2 keys aux, ihn hjust.2 keys aux]
  | bindCount mask pred body ihb =>
    simp only [ChoiceSlotExpr.justified] at hjust
    simp only [ChoiceSlotExpr.eval]
    have hc : countKeys sizes mask (fun k => pred.eval testFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux) =
        countKeys sizes mask (fun k => pred.eval testFn fixedAtom st (push keys k) aux) := by
      have hp' : (fun k => pred.eval testFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux) =
          (fun k => pred.eval testFn fixedAtom st (push keys (p.invFun k)) aux) := by
        funext k
        have h := PureTest.equivariant p testFn fixedAtom st pred (push keys (p.invFun k)) aux
        rwa [renameKeys_push, p.right] at h
      rw [hp']
      exact countKeys_rename p mask (fun k => pred.eval testFn fixedAtom st (push keys k) aux)
    rw [hc]
    exact ihb hjust keys _
  | bindUnique uk body ihb =>
    simp only [ChoiceSlotExpr.justified, Bool.and_eq_true] at hjust
    simp only [ChoiceSlotExpr.eval, UniqueKind.equivariant p constVal inv keyRank testFn fixedAtom st hinv uk hjust.1 keys aux]
    cases uk.eval keyRank testFn fixedAtom st keys aux with
    | none => rfl
    | some k =>
      simp only [Option.map_some, ← renameKeys_push]
      exact ihb hjust.2 (push keys k) aux
  | bindProj pk body ihb =>
    simp only [ChoiceSlotExpr.justified, Bool.and_eq_true] at hjust
    simp only [ChoiceSlotExpr.eval, ProjKind.equivariant p constVal inv keyRank recRank testFn valFn fixedAtom st hinv pk hjust.1 keys aux]
    cases pk.eval keyRank recRank testFn valFn fixedAtom st keys aux with
    | none => rfl
    | some v => exact ihb hjust.2 keys { aux with vals := v :: aux.vals }
  | bindFold mask filter term body ihb =>
    simp only [ChoiceSlotExpr.justified] at hjust
    simp only [ChoiceSlotExpr.eval]
    have hf : chooseFoldAdd keyRank (allKeys sizes) (allKeys sizes).length
        (fun k => mask k.1 && filter.eval testFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux)
        (fun k => term.eval testFn intFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux) =
      chooseFoldAdd keyRank (allKeys sizes) (allKeys sizes).length
        (fun k => mask k.1 && filter.eval testFn fixedAtom st (push keys k) aux)
        (fun k => term.eval testFn intFn fixedAtom st (push keys k) aux) := by
      apply chooseFoldAdd_rename p keyRank
      · intro k
        have h := PureTest.equivariant p testFn fixedAtom st filter (push keys (p.invFun k)) aux
        rw [renameKeys_push, p.right] at h
        simp only [GroupPerm.invFun_fst, h]
      · intro k
        have h := PureExpr.equivariant p testFn intFn fixedAtom st term (push keys (p.invFun k)) aux
        rwa [renameKeys_push, p.right] at h
    rw [hf]
    exact ihb hjust keys _

theorem evalBranchChoices_equivariant
    (p : GroupPerm sizes) (constVal : Nat → V) (inv : InvSpec d F MS)
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (intFn : Nat → LeafArgs Meta V A → Int)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (hinv : invHolds constVal inv st)
    (choices : List (BranchChoice d M S F MS))
    (hjust : choices.all (BranchChoice.justified inv) = true)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    evalBranchChoices keyRank recRank testFn valFn intFn fixedAtom (rename p st) (renameKeys p keys) aux choices =
      (evalBranchChoices keyRank recRank testFn valFn intFn fixedAtom st keys aux choices).map
        (fun ka => (renameKeys p ka.1, ka.2)) := by
  induction choices generalizing keys aux with
  | nil => rfl
  | cons bc rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hjust
    cases bc with
    | uniqueKey uk =>
      simp only [BranchChoice.justified] at hjust
      simp only [evalBranchChoices, UniqueKind.equivariant p constVal inv keyRank testFn fixedAtom st hinv uk hjust.1 keys aux]
      cases uk.eval keyRank testFn fixedAtom st keys aux with
      | none => rfl
      | some k =>
        simp only [Option.map_some, ← renameKeys_push]
        exact ih hjust.2 (push keys k) aux
    | projVal pk =>
      simp only [BranchChoice.justified] at hjust
      simp only [evalBranchChoices, ProjKind.equivariant p constVal inv keyRank recRank testFn valFn fixedAtom st hinv pk hjust.1 keys aux]
      cases pk.eval keyRank recRank testFn valFn fixedAtom st keys aux with
      | none => rfl
      | some v => exact ih hjust.2 keys { aux with vals := v :: aux.vals }
    | foldInt mask filter term =>
      simp only [evalBranchChoices]
      have hf : chooseFoldAdd keyRank (allKeys sizes) (allKeys sizes).length
          (fun k => mask k.1 && filter.eval testFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux)
          (fun k => term.eval testFn intFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux) =
        chooseFoldAdd keyRank (allKeys sizes) (allKeys sizes).length
          (fun k => mask k.1 && filter.eval testFn fixedAtom st (push keys k) aux)
          (fun k => term.eval testFn intFn fixedAtom st (push keys k) aux) := by
        apply chooseFoldAdd_rename p keyRank
        · intro k
          have h := PureTest.equivariant p testFn fixedAtom st filter (push keys (p.invFun k)) aux
          rw [renameKeys_push, p.right] at h
          simp only [GroupPerm.invFun_fst, h]
        · intro k
          have h := PureExpr.equivariant p testFn intFn fixedAtom st term (push keys (p.invFun k)) aux
          rwa [renameKeys_push, p.right] at h
      rw [hf]
      exact ih hjust.2 keys _

theorem Write.equivariant
    (p : GroupPerm sizes) (constVal : Nat → V) (inv : InvSpec d F MS)
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (intFn : Nat → LeafArgs Meta V A → Int)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (hinv : invHolds constVal inv st)
    (w : Write d M S F MS) (hjust : w.justified inv = true)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V)
    (current : Maps M (Key sizes) V) :
    w.apply keyRank recRank testFn valFn intFn fixedAtom (rename p st) (renameKeys p keys) aux (renameMaps p current) =
      (w.apply keyRank recRank testFn valFn intFn fixedAtom st keys aux current).map (renameMaps p) := by
  cases w with
  | point map target val =>
    simp only [Write.justified] at hjust
    simp only [Write.apply, rename_slots, evalKeyRef_rename,
      ChoiceExpr.equivariant p constVal inv keyRank recRank testFn valFn intFn valFn fixedAtom st hinv val hjust keys aux]
    cases evalKeyRef fixedAtom st.slots keys target with
    | inl tk =>
      simp only [renameKeyVal]
      cases val.eval keyRank recRank testFn valFn intFn valFn fixedAtom st keys aux with
      | none => rfl
      | some v =>
        simp only [Option.map_some]
        congr 1
        funext m k
        have heq : (k = p.toFun tk) ↔ (p.invFun k = tk) := by
          constructor
          · intro h; rw [h, p.left]
          · intro h; rw [← h, p.right]
        by_cases hc : m = map ∧ p.invFun k = tk
        · have hc' : m = map ∧ k = p.toFun tk := ⟨hc.1, heq.mpr hc.2⟩
          dsimp only [renameMaps]
          rw [if_true_of hc', if_true_of hc]
        · have hc' : ¬ (m = map ∧ k = p.toFun tk) := fun h => hc ⟨h.1, heq.mp h.2⟩
          dsimp only [renameMaps]
          rw [if_false_of hc', if_false_of hc]
    | inr a => rfl
  | all map mask val =>
    simp only [Write.justified] at hjust
    simp only [Write.apply]
    have heval : ∀ k, val.eval keyRank recRank testFn valFn intFn valFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux =
        val.eval keyRank recRank testFn valFn intFn valFn fixedAtom st (push keys (p.invFun k)) aux := by
      intro k
      have h := ChoiceExpr.equivariant p constVal inv keyRank recRank testFn valFn intFn valFn fixedAtom st hinv val hjust (push keys (p.invFun k)) aux
      rwa [renameKeys_push, p.right] at h
    have hall : (allKeys sizes).all (fun k => !(mask k.1) || (val.eval keyRank recRank testFn valFn intFn valFn fixedAtom (rename p st) (push (renameKeys p keys) k) aux).isSome) =
        (allKeys sizes).all (fun k => !(mask k.1) || (val.eval keyRank recRank testFn valFn intFn valFn fixedAtom st (push keys k) aux).isSome) := by
      apply allKeys_all_rename p
      intro k
      simp only [heval k, GroupPerm.invFun_fst]
    rw [hall]
    split
    · simp only [Option.map_some]
      congr 1
      funext m k
      by_cases hc : m = map ∧ mask k.1 = true
      · have hc' : m = map ∧ mask (p.invFun k).1 = true := hc
        simp only [renameMaps, heval k, hc, hc', ↓reduceIte]
      · have hc' : ¬ (m = map ∧ mask (p.invFun k).1 = true) := hc
        simp only [renameMaps, heval k, hc, hc', ↓reduceIte]
    · rfl

theorem applyWrites_equivariant
    (p : GroupPerm sizes) (constVal : Nat → V) (inv : InvSpec d F MS)
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (intFn : Nat → LeafArgs Meta V A → Int)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (hinv : invHolds constVal inv st)
    (writes : List (Write d M S F MS))
    (hjust : writes.all (Write.justified inv) = true)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    applyWrites keyRank recRank testFn valFn intFn fixedAtom (rename p st) (renameKeys p keys) aux writes =
      (applyWrites keyRank recRank testFn valFn intFn fixedAtom st keys aux writes).map (renameMaps p) := by
  have fold (ws : List (Write d M S F MS)) (hw : ws.all (Write.justified inv) = true) (cur : Maps M (Key sizes) V) :
      ws.foldlM (fun c w => Write.apply keyRank recRank testFn valFn intFn fixedAtom (rename p st) (renameKeys p keys) aux c w) (renameMaps p cur) =
      (ws.foldlM (fun c w => Write.apply keyRank recRank testFn valFn intFn fixedAtom st keys aux c w) cur).map (renameMaps p) := by
    induction ws generalizing cur with
    | nil => rfl
    | cons w rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hw
      simp only [List.foldlM_cons, Write.equivariant p constVal inv keyRank recRank testFn valFn intFn fixedAtom st hinv w hw.1 keys aux cur]
      cases Write.apply keyRank recRank testFn valFn intFn fixedAtom st keys aux cur w with
      | none => rfl
      | some nextCur => exact ih hw.2 nextCur
  exact fold writes hjust st.maps

theorem SlotWrite.equivariant
    (p : GroupPerm sizes) (constVal : Nat → V) (inv : InvSpec d F MS)
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (intFn : Nat → LeafArgs Meta V A → Int)
    (fixedFn : Nat → LeafArgs Meta V A → A)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (hinv : invHolds constVal inv st)
    (w : SlotWrite d M S F MS) (hjust : w.justified inv = true)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V)
    (current : Slots S (Key sizes) A) :
    w.apply keyRank recRank testFn valFn intFn fixedFn fixedAtom (rename p st) (renameKeys p keys) aux (renameSlots p current) =
      (w.apply keyRank recRank testFn valFn intFn fixedFn fixedAtom st keys aux current).map (renameSlots p) := by
  simp only [SlotWrite.justified] at hjust
  simp only [SlotWrite.apply, ChoiceSlotExpr.equivariant p constVal inv keyRank recRank testFn valFn intFn fixedFn fixedAtom st hinv w.value hjust keys aux]
  cases w.value.eval keyRank recRank testFn valFn intFn fixedFn fixedAtom st keys aux with
  | none => rfl
  | some kv =>
    simp only [Option.map_some]
    congr 1
    funext s
    simp only [renameSlots]
    split <;> rfl

theorem applySlotWrites_equivariant
    (p : GroupPerm sizes) (constVal : Nat → V) (inv : InvSpec d F MS)
    (keyRank : Key sizes → Nat) (recRank : Key sizes → Meta → V → Nat)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (intFn : Nat → LeafArgs Meta V A → Int)
    (fixedFn : Nat → LeafArgs Meta V A → A)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (hinv : invHolds constVal inv st)
    (writes : List (SlotWrite d M S F MS))
    (hjust : writes.all (SlotWrite.justified inv) = true)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V) :
    applySlotWrites keyRank recRank testFn valFn intFn fixedFn fixedAtom (rename p st) (renameKeys p keys) aux writes =
      (applySlotWrites keyRank recRank testFn valFn intFn fixedFn fixedAtom st keys aux writes).map (renameSlots p) := by
  have fold (ws : List (SlotWrite d M S F MS)) (hw : ws.all (SlotWrite.justified inv) = true) (cur : Slots S (Key sizes) A) :
      ws.foldlM (fun c w => SlotWrite.apply keyRank recRank testFn valFn intFn fixedFn fixedAtom (rename p st) (renameKeys p keys) aux c w) (renameSlots p cur) =
      (ws.foldlM (fun c w => SlotWrite.apply keyRank recRank testFn valFn intFn fixedFn fixedAtom st keys aux c w) cur).map (renameSlots p) := by
    induction ws generalizing cur with
    | nil => rfl
    | cons w rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hw
      simp only [List.foldlM_cons, SlotWrite.equivariant p constVal inv keyRank recRank testFn valFn intFn fixedFn fixedAtom st hinv w hw.1 keys aux cur]
      cases SlotWrite.apply keyRank recRank testFn valFn intFn fixedFn fixedAtom st keys aux cur w with
      | none => rfl
      | some nextCur => exact ih hw.2 nextCur
  exact fold writes hjust st.slots

theorem FlagStep.equivariant
    (p : GroupPerm sizes)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V)
    (f : F) (nextFl : Key sizes → Bool) (step : FlagStep d M S F MS)
    (h : step.holds testFn fixedAtom st keys aux f nextFl) :
    step.holds testFn fixedAtom (rename p st) (renameKeys p keys) aux f (fun k => nextFl (p.invFun k)) := by
  classical
  cases step with
  | keep =>
    unfold FlagStep.holds at h ⊢
    rw [h]
    rfl
  | clear =>
    unfold FlagStep.holds at h ⊢
    rw [h]
  | singleton mask target =>
    unfold FlagStep.holds at h ⊢
    dsimp only [] at h ⊢
    rw [rename_slots, evalKeyRef_rename]
    cases htarget : evalKeyRef fixedAtom st.slots keys target with
    | inl tk =>
      rw [htarget] at h
      dsimp only [renameKeyVal] at h ⊢
      rw [h]
      funext k
      have heq : decide (p.invFun k = tk) = decide (k = p.toFun tk) := by
        apply decide_eq_decide.mpr
        constructor
        · intro hk; rw [← hk, p.right]
        · intro hk; rw [hk, p.left]
      simp only [GroupPerm.toFun_fst, heq]
    | inr a =>
      rw [htarget] at h
      dsimp only [renameKeyVal] at h ⊢
      rw [h]
  | clearPoint target =>
    unfold FlagStep.holds at h ⊢
    dsimp only [] at h ⊢
    rw [rename_slots, evalKeyRef_rename, rename_flags, h]
    funext k
    have heq : (renameKeyVal p (evalKeyRef fixedAtom st.slots keys target) = .inl k) ↔
        (evalKeyRef fixedAtom st.slots keys target = .inl (p.invFun k)) := by
      cases evalKeyRef fixedAtom st.slots keys target with
      | inl tk =>
        simp only [renameKeyVal, Sum.inl.injEq]
        constructor
        · intro hk; rw [← hk, p.left]
        · intro hk; rw [hk, p.right]
      | inr a => simp [renameKeyVal]
    simp only [renameFlags, heq]
  | setPoint mask target =>
    unfold FlagStep.holds at h ⊢
    dsimp only [] at h ⊢
    rw [rename_slots, evalKeyRef_rename, rename_flags, h]
    funext k
    have heq : (renameKeyVal p (evalKeyRef fixedAtom st.slots keys target) = .inl k) ↔
        (evalKeyRef fixedAtom st.slots keys target = .inl (p.invFun k)) := by
      cases evalKeyRef fixedAtom st.slots keys target with
      | inl tk =>
        simp only [renameKeyVal, Sum.inl.injEq]
        constructor
        · intro hk; rw [← hk, p.left]
        · intro hk; rw [hk, p.right]
      | inr a => simp [renameKeyVal]
    by_cases hc : evalKeyRef fixedAtom st.slots keys target = .inl (p.invFun k) ∧ mask k.1 = true
    · have hc' : renameKeyVal p (evalKeyRef fixedAtom st.slots keys target) = .inl k ∧ mask k.1 = true := ⟨heq.mpr hc.1, hc.2⟩
      have hc'' : evalKeyRef fixedAtom st.slots keys target = .inl (p.invFun k) ∧ mask (p.invFun k).1 = true := hc
      dsimp only [renameFlags]
      rw [if_true_of hc', if_true_of hc'']
    · have hc' : ¬ (renameKeyVal p (evalKeyRef fixedAtom st.slots keys target) = .inl k ∧ mask k.1 = true) := fun hh => hc ⟨heq.mp hh.1, hh.2⟩
      have hc'' : ¬ (evalKeyRef fixedAtom st.slots keys target = .inl (p.invFun k) ∧ mask (p.invFun k).1 = true) := hc
      dsimp only [renameFlags]
      rw [if_false_of hc', if_false_of hc'']
  | generalAll mask pred =>
    unfold FlagStep.holds at h ⊢
    dsimp only [] at h ⊢
    rw [h]
    funext k
    have hp := PureTest.equivariant p testFn fixedAtom st pred (push keys (p.invFun k)) aux
    rw [renameKeys_push, p.right] at hp
    simp only [GroupPerm.invFun_fst, hp]
  | cardinal mask card =>
    unfold FlagStep.holds at h ⊢
    dsimp only [] at h ⊢
    refine ⟨fun k hk => h.1 (p.invFun k) hk, ?_⟩
    rw [countKeys_rename p mask nextFl]
    exact h.2

theorem MsgStep.equivariant
    (p : GroupPerm sizes) (constVal : Nat → V)
    (testFn : Nat → LeafArgs Meta V A → Bool)
    (valFn : Nat → LeafArgs Meta V A → V)
    (metaFn : Nat → LeafArgs Meta V A → Meta)
    (fixedAtom : Nat → A) (st : RawState C M S F MS (Key sizes) Meta V A)
    (ugs : List (MS × PureExpr d M S F MS))
    (keys : Environment (Key sizes)) (aux : AuxEnv Meta V)
    (ms : MS) (step : MsgStep d M S F MS) :
    step.eval constVal testFn valFn metaFn fixedAtom (rename p st) ugs (renameKeys p keys) aux ms =
      fun k => step.eval constVal testFn valFn metaFn fixedAtom st ugs keys aux ms (p.invFun k) := by
  have addCase (mask : GroupMask d) (target : KeyRef S) (metaExpr : PureExpr d M S F MS) (v : V) :
      (match evalKeyRef fixedAtom (rename p st).slots (renameKeys p keys) target with
       | .inl tk => fun k => if k = tk ∧ mask k.1 = true then FinSet.insert (metaExpr.eval testFn metaFn fixedAtom (rename p st) (renameKeys p keys) aux, v) ((rename p st).msgs ms k) else (rename p st).msgs ms k
       | .inr _ => (rename p st).msgs ms) =
      fun k =>
        (match evalKeyRef fixedAtom st.slots keys target with
         | .inl tk => fun k' => if k' = tk ∧ mask k'.1 = true then FinSet.insert (metaExpr.eval testFn metaFn fixedAtom st keys aux, v) (st.msgs ms k') else st.msgs ms k'
         | .inr _ => st.msgs ms) (p.invFun k) := by
    rw [rename_slots, evalKeyRef_rename, PureExpr.equivariant p testFn metaFn fixedAtom st metaExpr keys aux, rename_msgs]
    cases evalKeyRef fixedAtom st.slots keys target with
    | inl tk =>
      simp only [renameKeyVal]
      funext k
      have heq : (k = p.toFun tk) ↔ (p.invFun k = tk) := by
        constructor
        · intro hk; rw [hk, p.left]
        · intro hk; rw [← hk, p.right]
      by_cases hc : p.invFun k = tk ∧ mask k.1 = true
      · have hc1 : k = p.toFun tk ∧ mask k.1 = true := ⟨heq.mpr hc.1, hc.2⟩
        have hc2 : p.invFun k = tk ∧ mask (p.invFun k).1 = true := hc
        dsimp only [renameMsgs]
        rw [if_true_of hc1, if_true_of hc2]
      · have hc1 : ¬ (k = p.toFun tk ∧ mask k.1 = true) := fun hh => hc ⟨heq.mp hh.1, hh.2⟩
        have hc2 : ¬ (p.invFun k = tk ∧ mask (p.invFun k).1 = true) := hc
        dsimp only [renameMsgs]
        rw [if_false_of hc1, if_false_of hc2]
    | inr a => rfl
  cases step with
  | keep => rfl
  | clear => rfl
  | comprehensionAll mask metaExpr valExpr =>
    simp only [MsgStep.eval, PureExpr.equivariant p testFn valFn fixedAtom st valExpr keys aux]
    funext k
    have hm := PureExpr.equivariant p testFn metaFn fixedAtom st metaExpr (push keys (p.invFun k)) aux
    rw [renameKeys_push, p.right] at hm
    cases hc : mask k.1
    · have hc' : mask (p.invFun k).1 = false := hc
      simp only [hc, hc', Bool.false_eq_true, ↓reduceIte]
    · have hc' : mask (p.invFun k).1 = true := hc
      simp only [hc, hc', ↓reduceIte, hm]
  | addConst mask target metaExpr cid =>
    simpa only [MsgStep.eval] using addCase mask target metaExpr (constVal cid)
  | addWhenEmpty mask target metaExpr valExpr =>
    simp only [MsgStep.eval, PureExpr.equivariant p testFn valFn fixedAtom st valExpr keys aux]
    exact addCase mask target metaExpr (valExpr.eval testFn valFn fixedAtom st keys aux)
  | addMatchingGuard mask target metaExpr ugIdx =>
    simp only [MsgStep.eval]
    cases ugs[ugIdx]? with
    | none => rfl
    | some item =>
      rcases item with ⟨ms', valExpr⟩
      by_cases hms_eq : ms' = ms
      · simp only [hms_eq, ↓reduceIte, PureExpr.equivariant p testFn valFn fixedAtom st valExpr keys aux]
        exact addCase mask target metaExpr (valExpr.eval testFn valFn fixedAtom st keys aux)
      · simp only [hms_eq, ↓reduceIte]
        rfl
  | addGeneral mask target metaExpr valExpr =>
    simp only [MsgStep.eval, PureExpr.equivariant p testFn valFn fixedAtom st valExpr keys aux]
    exact addCase mask target metaExpr (valExpr.eval testFn valFn fixedAtom st keys aux)

end Equivariance

structure Model (d : Nat) (sizes : Fin d → Nat) (C M S F MS Meta V A IB B W : Type)
    [DecidableEq M] [DecidableEq S] [DecidableEq F] [DecidableEq MS] where
  ops : Operations d M S F MS IB B
  sem : Semantics d sizes C M S Meta V A IB B W
  allIB : List IB
  completeIB : ∀ ib : IB, ib ∈ allIB
  allB : List B
  completeB : ∀ b : B, b ∈ allB
  opsValid : checkOperationsValid allIB allB ops = true

namespace Model
variable {d : Nat} {sizes : Fin d → Nat} {C M S F MS Meta V A IB B W : Type}
  [DecidableEq M] [DecidableEq S] [DecidableEq F] [DecidableEq MS]
  (m : Model d sizes C M S F MS Meta V A IB B W)

abbrev RState (_m : Model d sizes C M S F MS Meta V A IB B W) :=
  RawState C M S F MS (Key sizes) Meta V A

def valid (st : m.RState) : Prop :=
  invHolds m.sem.constVal m.ops.inv st

def branchHasError (b : B) (st : m.RState) : Prop :=
  let sb := m.ops.stepBranch b
  ∃ dcore w keys,
    sb.preGuard.eval (m.sem.stepTest b st.core dcore w) m.sem.fixedAtom st keys {} = true ∧
    evalUniformGuards (m.sem.stepTest b st.core dcore w) (m.sem.stepVal b st.core dcore w)
      m.sem.fixedAtom st keys {} sb.uniformGuards = true ∧
    match evalBranchChoices m.sem.keyRank m.sem.recRank
        (m.sem.stepTest b st.core dcore w) (m.sem.stepVal b st.core dcore w)
        (m.sem.stepInt b st.core dcore w) m.sem.fixedAtom st keys {} sb.choices with
    | none => True
    | some (keys', aux') =>
        match sb.postGuard.eval m.sem.keyRank m.sem.recRank
            (m.sem.stepTest b st.core dcore w) (m.sem.stepVal b st.core dcore w)
            (m.sem.stepInt b st.core dcore w) m.sem.fixedAtom st keys' aux' with
        | none => True
        | some false => False
        | some true =>
            applyWrites m.sem.keyRank m.sem.recRank
              (m.sem.stepTest b st.core dcore w) (m.sem.stepVal b st.core dcore w)
              (m.sem.stepInt b st.core dcore w) m.sem.fixedAtom st keys' aux' sb.writes = none ∨
            applySlotWrites m.sem.keyRank m.sem.recRank
              (m.sem.stepTest b st.core dcore w) (m.sem.stepVal b st.core dcore w)
              (m.sem.stepInt b st.core dcore w) (m.sem.stepFixed b st.core dcore w)
              m.sem.fixedAtom st keys' aux' sb.slotWrites = none

def rawConcrete : System m.RState where
  initial st := ∃ ib w keys,
    m.sem.initSetup ib st.core st.maps st.slots keys w ∧
    (∀ f : F, ((m.ops.initBranch ib).flagInit f).holds keys (st.flags f)) ∧
    (∀ ms : MS, st.msgs ms =
      ((m.ops.initBranch ib).msgInit ms).eval m.sem.constVal m.sem.initMeta m.sem.initCoreVal st.core)
  next st t := ∃ b w keys,
    let sb := m.ops.stepBranch b
    sb.preGuard.eval (m.sem.stepTest b st.core t.core w) m.sem.fixedAtom st keys {} = true ∧
    evalUniformGuards (m.sem.stepTest b st.core t.core w) (m.sem.stepVal b st.core t.core w)
      m.sem.fixedAtom st keys {} sb.uniformGuards = true ∧
    ∃ keys' aux',
      evalBranchChoices m.sem.keyRank m.sem.recRank
        (m.sem.stepTest b st.core t.core w) (m.sem.stepVal b st.core t.core w)
        (m.sem.stepInt b st.core t.core w) m.sem.fixedAtom st keys {} sb.choices = some (keys', aux') ∧
      sb.postGuard.eval m.sem.keyRank m.sem.recRank
        (m.sem.stepTest b st.core t.core w) (m.sem.stepVal b st.core t.core w)
        (m.sem.stepInt b st.core t.core w) m.sem.fixedAtom st keys' aux' = some true ∧
      applyWrites m.sem.keyRank m.sem.recRank
        (m.sem.stepTest b st.core t.core w) (m.sem.stepVal b st.core t.core w)
        (m.sem.stepInt b st.core t.core w) m.sem.fixedAtom st keys' aux' sb.writes = some t.maps ∧
      applySlotWrites m.sem.keyRank m.sem.recRank
        (m.sem.stepTest b st.core t.core w) (m.sem.stepVal b st.core t.core w)
        (m.sem.stepInt b st.core t.core w) (m.sem.stepFixed b st.core t.core w)
        m.sem.fixedAtom st keys' aux' sb.slotWrites = some t.slots ∧
      (∀ f : F, (sb.flagSteps f).holds (m.sem.stepTest b st.core t.core w)
        m.sem.fixedAtom st keys' aux' f (t.flags f)) ∧
      (∀ ms : MS, t.msgs ms = (sb.msgSteps ms).eval m.sem.constVal
        (m.sem.stepTest b st.core t.core w) (m.sem.stepVal b st.core t.core w)
        (m.sem.stepMeta b st.core t.core w) m.sem.fixedAtom st sb.uniformGuards keys' aux' ms)
  safe st :=
    (∀ keys, m.ops.observation.eval m.sem.keyRank m.sem.recRank
      (m.sem.obsTest st.core) (m.sem.obsVal st.core) (m.sem.obsInt st.core)
      m.sem.fixedAtom st keys {} = some true) ∧
    (∀ b, ¬ m.branchHasError b st)

private theorem opsValid_parts :
    m.ops.inv.atMostOneFlags.all (fun fm =>
      m.allIB.all (fun ib => checkFlagInitAtMostOne fm.2 ((m.ops.initBranch ib).flagInit fm.1)) &&
      m.allB.all (fun b =>
        let sb := m.ops.stepBranch b
        checkFlagStepAtMostOne fm.1 fm.2 sb.preGuard (sb.flagSteps fm.1))) = true ∧
    m.ops.inv.constValMsgs.all (fun mc =>
      m.allIB.all (fun ib => checkMsgInitConst mc.2 ((m.ops.initBranch ib).msgInit mc.1)) &&
      m.allB.all (fun b => checkMsgStepConst mc.2 ((m.ops.stepBranch b).msgSteps mc.1))) = true ∧
    m.ops.inv.uniformValMsgs.all (fun ms =>
      m.allIB.all (fun ib => checkMsgInitUniform ((m.ops.initBranch ib).msgInit ms)) &&
      m.allB.all (fun b =>
        let sb := m.ops.stepBranch b
        checkMsgStepUniform ms sb (sb.msgSteps ms))) = true ∧
    m.allB.all (fun b =>
      let sb := m.ops.stepBranch b
      sb.choices.all (BranchChoice.justified m.ops.inv) &&
      sb.postGuard.justified m.ops.inv &&
      sb.writes.all (Write.justified m.ops.inv) &&
      sb.slotWrites.all (SlotWrite.justified m.ops.inv)) = true ∧
    m.ops.observation.justified m.ops.inv = true := by
  have h := m.opsValid
  simp only [checkOperationsValid, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩

private theorem opsValid_constrained_parts :
    m.ops.initObservation.justified m.ops.inv = true ∧
    m.ops.constraintTest.justified m.ops.inv = true := by
  have h := m.opsValid
  simp only [checkOperationsValid, Bool.and_eq_true] at h
  exact ⟨h.1.2, h.2⟩

theorem initial_valid (st : m.RState) (hi : m.rawConcrete.initial st) : m.valid st := by
  rcases hi with ⟨ib, w, keys, _, hflags, hmsgs⟩
  have parts := m.opsValid_parts
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨f, mask⟩ hfm
    have hchk := (List.all_eq_true.mp parts.1) (f, mask) hfm
    simp only [Bool.and_eq_true] at hchk
    have hib := (List.all_eq_true.mp hchk.1) ib (m.completeIB ib)
    have hf := hflags f
    cases hfi : (m.ops.initBranch ib).flagInit f <;> rw [hfi] at hib hf
    · simp only [FlagInit.holds] at hf
      exact ⟨fun k hk => by simp [hf] at hk, fun k1 k2 h1 _ => by simp [hf] at h1⟩
    · rename_i smask idx
      simp only [checkFlagInitAtMostOne] at hib
      simp only [FlagInit.holds] at hf
      refine ⟨fun k hk => ?_, fun k1 k2 h1 h2 => ?_⟩
      · rw [hf.2] at hk
        simp only [decide_eq_true_eq] at hk
        subst hk
        exact maskImplies_sound hib hf.1
      · rw [hf.2] at h1 h2
        simp only [decide_eq_true_eq] at h1 h2
        exact h1.trans h2.symm
    · nomatch hib
    · nomatch hib
  · intro ⟨ms, cid⟩ hmc
    have hchk := (List.all_eq_true.mp parts.2.1) (ms, cid) hmc
    simp only [Bool.and_eq_true] at hchk
    have hib := (List.all_eq_true.mp hchk.1) ib (m.completeIB ib)
    have hm := hmsgs ms
    cases hmi : (m.ops.initBranch ib).msgInit ms <;> rw [hmi] at hib hm
    · intro k mv hmv
      rw [hm] at hmv
      exact absurd hmv FinSet.not_mem_empty
    · rename_i mask metaId cid'
      simp only [checkMsgInitConst, decide_eq_true_eq] at hib
      subst hib
      intro k mv hmv
      rw [hm] at hmv
      simp only [MsgInit.eval] at hmv
      by_cases hmk : mask k.1 = true
      · simp only [hmk, ↓reduceIte, FinSet.mem_singleton] at hmv
        rw [hmv]
      · simp only [hmk, ↓reduceIte] at hmv
        exact absurd hmv FinSet.not_mem_empty
    · nomatch hib
  · intro ms hms
    have hm := hmsgs ms
    cases hmi : (m.ops.initBranch ib).msgInit ms <;> rw [hmi] at hm
    · intro k1 mv1 k2 mv2 h1 _
      rw [hm] at h1
      exact absurd h1 FinSet.not_mem_empty
    · rename_i mask metaId cid
      intro k1 mv1 k2 mv2 h1 h2
      rw [hm] at h1 h2
      simp only [MsgInit.eval] at h1 h2
      by_cases hm1 : mask k1.1 = true
      · by_cases hm2 : mask k2.1 = true
        · simp only [hm1, hm2, ↓reduceIte, FinSet.mem_singleton] at h1 h2
          rw [h1, h2]
        · simp only [hm2, ↓reduceIte] at h2; exact absurd h2 FinSet.not_mem_empty
      · simp only [hm1, ↓reduceIte] at h1; exact absurd h1 FinSet.not_mem_empty
    · rename_i mask metaId vid
      intro k1 mv1 k2 mv2 h1 h2
      rw [hm] at h1 h2
      simp only [MsgInit.eval] at h1 h2
      by_cases hm1 : mask k1.1 = true
      · by_cases hm2 : mask k2.1 = true
        · simp only [hm1, hm2, ↓reduceIte, FinSet.mem_singleton] at h1 h2
          rw [h1, h2]
        · simp only [hm2, ↓reduceIte] at h2; exact absurd h2 FinSet.not_mem_empty
      · simp only [hm1, ↓reduceIte] at h1; exact absurd h1 FinSet.not_mem_empty

theorem next_valid (st t : m.RState) (hv : m.valid st) (hn : m.rawConcrete.next st t) : m.valid t := by
  classical
  rcases hn with ⟨b, w, keys, hpre, hug, keys', aux', hchoices, _, _, _, hflags, hmsgs⟩
  have parts := m.opsValid_parts
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨f, mask⟩ hfm
    have hchk := (List.all_eq_true.mp parts.1) (f, mask) hfm
    simp only [Bool.and_eq_true] at hchk
    have hb := (List.all_eq_true.mp hchk.2) b (m.completeB b)
    have hprev := hv.1 (f, mask) hfm
    have hf := hflags f
    dsimp only [] at hb hf hprev ⊢
    cases hfs : (m.ops.stepBranch b).flagSteps f <;> rw [hfs] at hb hf
    · unfold FlagStep.holds at hf
      dsimp only [] at hf
      exact ⟨fun k hk => hprev.1 k (hf ▸ hk), fun k1 k2 h1 h2 => hprev.2 k1 k2 (hf ▸ h1) (hf ▸ h2)⟩
    · unfold FlagStep.holds at hf
      dsimp only [] at hf
      exact ⟨fun k hk => by simp [hf] at hk, fun k1 k2 h1 _ => by simp [hf] at h1⟩
    · rename_i smask target
      simp only [checkFlagStepAtMostOne] at hb
      unfold FlagStep.holds at hf
      dsimp only [] at hf
      cases htarget : evalKeyRef m.sem.fixedAtom st.slots keys' target with
      | inl tk =>
        rw [htarget] at hf
        dsimp only [] at hf
        refine ⟨fun k hk => ?_, fun k1 k2 h1 h2 => ?_⟩
        · rw [hf] at hk
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
          rw [hk.2]
          exact maskImplies_sound hb hk.1
        · rw [hf] at h1 h2
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2
          exact h1.2.trans h2.2.symm
      | inr a =>
        rw [htarget] at hf
        dsimp only [] at hf
        exact ⟨fun k hk => by simp [hf] at hk, fun k1 k2 h1 _ => by simp [hf] at h1⟩
    · rename_i target
      unfold FlagStep.holds at hf
      dsimp only [] at hf
      have sub (k : Key sizes) (hk : t.flags f k = true) : st.flags f k = true := by
        have hfk := congrFun hf k
        rw [hfk] at hk
        by_cases heq : evalKeyRef m.sem.fixedAtom st.slots keys' target = .inl k
        · simp only [heq, ↓reduceIte] at hk; nomatch hk
        · simpa only [heq, ↓reduceIte] using hk
      exact ⟨fun k hk => hprev.1 k (sub k hk), fun k1 k2 h1 h2 => hprev.2 k1 k2 (sub k1 h1) (sub k2 h2)⟩
    · rename_i smask target
      simp only [checkFlagStepAtMostOne, Bool.and_eq_true] at hb
      unfold FlagStep.holds at hf
      dsimp only [] at hf
      have hemp := guardImpliesFlagEmpty_sound (m.sem.stepTest b st.core t.core w) m.sem.fixedAtom st keys {} f mask (m.ops.stepBranch b).preGuard hb.2 hpre
      have old_false (k : Key sizes) : st.flags f k = false := by
        cases hfk : st.flags f k with
        | false => rfl
        | true =>
          have hm := hprev.1 k hfk
          rw [hemp k hm] at hfk
          nomatch hfk
      have hit_of_true (k : Key sizes) (hk : t.flags f k = true) :
          evalKeyRef m.sem.fixedAtom st.slots keys' target = .inl k ∧ smask k.1 = true := by
        have hfk := congrFun hf k
        rw [hfk] at hk
        by_cases hc : evalKeyRef m.sem.fixedAtom st.slots keys' target = .inl k ∧ smask k.1 = true
        · exact hc
        · simp only [hc, ↓reduceIte, old_false k] at hk; nomatch hk
      refine ⟨fun k hk => maskImplies_sound hb.1 (hit_of_true k hk).2, fun k1 k2 h1 h2 => ?_⟩
      have heq := (hit_of_true k1 h1).1.symm.trans (hit_of_true k2 h2).1
      injection heq
    · nomatch hb
    · nomatch hb
  · intro ⟨ms, cid⟩ hmc
    have hchk := (List.all_eq_true.mp parts.2.1) (ms, cid) hmc
    simp only [Bool.and_eq_true] at hchk
    have hb := (List.all_eq_true.mp hchk.2) b (m.completeB b)
    have hprev := hv.2.1 (ms, cid) hmc
    have hm := hmsgs ms
    dsimp only [] at hb hm hprev ⊢
    cases hms_step : (m.ops.stepBranch b).msgSteps ms <;> rw [hms_step] at hb hm
    · intro k mv hmv
      rw [hm] at hmv
      exact hprev k mv hmv
    · intro k mv hmv
      rw [hm] at hmv
      exact absurd hmv FinSet.not_mem_empty
    · nomatch hb
    · rename_i mask target metaExpr cid'
      simp only [checkMsgStepConst, decide_eq_true_eq] at hb
      subst hb
      intro k mv hmv
      rw [hm] at hmv
      simp only [MsgStep.eval] at hmv
      cases htarget : evalKeyRef m.sem.fixedAtom st.slots keys' target <;> simp only [htarget] at hmv
      · rename_i tk
        by_cases hc : k = tk ∧ mask k.1 = true
        · rw [if_true_of hc] at hmv
          rcases FinSet.mem_insert.mp hmv with rfl | hold
          · rfl
          · exact hprev k mv hold
        · rw [if_false_of hc] at hmv
          exact hprev k mv hmv
      · exact hprev k mv hmv
    · nomatch hb
    · nomatch hb
    · nomatch hb
  · intro ms hms
    have hchk := (List.all_eq_true.mp parts.2.2.1) ms hms
    simp only [Bool.and_eq_true] at hchk
    have hb := (List.all_eq_true.mp hchk.2) b (m.completeB b)
    have hprev := hv.2.2 ms hms
    have hm := hmsgs ms
    cases hms_step : (m.ops.stepBranch b).msgSteps ms <;> rw [hms_step] at hb hm
    · intro k1 mv1 k2 mv2 h1 h2
      rw [hm] at h1 h2
      exact hprev k1 mv1 k2 mv2 h1 h2
    · intro k1 mv1 k2 mv2 h1 _
      rw [hm] at h1
      exact absurd h1 FinSet.not_mem_empty
    · rename_i mask metaExpr valExpr
      intro k1 mv1 k2 mv2 h1 h2
      rw [hm] at h1 h2
      simp only [MsgStep.eval] at h1 h2
      by_cases hm1 : mask k1.1 = true
      · by_cases hm2 : mask k2.1 = true
        · simp only [hm1, hm2, ↓reduceIte, FinSet.mem_singleton] at h1 h2
          rw [h1, h2]
        · simp only [hm2, ↓reduceIte] at h2; exact absurd h2 FinSet.not_mem_empty
      · simp only [hm1, ↓reduceIte] at h1; exact absurd h1 FinSet.not_mem_empty
    · nomatch hb
    · rename_i mask target metaExpr valExpr
      simp only [checkMsgStepUniform] at hb
      have hemp := guardImpliesMsgEmpty_sound (m.sem.stepTest b st.core t.core w) m.sem.fixedAtom st keys {} ms (m.ops.stepBranch b).preGuard hb hpre
      let vtarget := valExpr.eval (m.sem.stepTest b st.core t.core w) (m.sem.stepVal b st.core t.core w) m.sem.fixedAtom st keys' aux'
      have hnew_eq (k : Key sizes) (mv : Meta × V) (hmv : mv ∈ t.msgs ms k) : mv.2 = vtarget := by
        rw [hm] at hmv
        simp only [MsgStep.eval] at hmv
        cases htarget : evalKeyRef m.sem.fixedAtom st.slots keys' target <;> simp only [htarget] at hmv
        · rename_i tk
          by_cases hc : k = tk ∧ mask k.1 = true
          · rw [if_true_of hc, hemp k] at hmv
            rcases FinSet.mem_insert.mp hmv with rfl | hbot
            · rfl
            · exact absurd hbot FinSet.not_mem_empty
          · rw [if_false_of hc, hemp k] at hmv; exact absurd hmv FinSet.not_mem_empty
        · rw [hemp k] at hmv; exact absurd hmv FinSet.not_mem_empty
      intro k1 mv1 k2 mv2 h1 h2
      exact (hnew_eq k1 mv1 h1).trans (hnew_eq k2 mv2 h2).symm
    · rename_i mask target metaExpr ugIdx
      simp only [checkMsgStepUniform, Bool.and_eq_true, List.isEmpty_iff] at hb
      rcases hb with ⟨hno_choices, hug_match⟩
      rw [hno_choices] at hchoices
      simp only [evalBranchChoices, Option.some.injEq, Prod.mk.injEq] at hchoices
      rcases hchoices with ⟨rfl, rfl⟩
      cases hug_get : (m.ops.stepBranch b).uniformGuards[ugIdx]? with
      | none => rw [hug_get] at hug_match; nomatch hug_match
      | some item =>
        rcases item with ⟨ms', valExpr⟩
        rw [hug_get] at hug_match
        simp only [decide_eq_true_eq] at hug_match
        subst hug_match
        have hmem_ug : (ms', valExpr) ∈ (m.ops.stepBranch b).uniformGuards := List.mem_of_getElem? hug_get
        simp only [evalUniformGuards, List.all_eq_true, FinSet.all_eq_true, decide_eq_true_eq] at hug
        let vtarget := valExpr.eval (m.sem.stepTest b st.core t.core w) (m.sem.stepVal b st.core t.core w) m.sem.fixedAtom st keys {}
        have hold_eq (k : Key sizes) (mv : Meta × V) (hmv : mv ∈ st.msgs ms' k) : mv.2 = vtarget :=
          hug (ms', valExpr) hmem_ug k (mem_allKeys k) mv hmv
        have hnew_eq (k : Key sizes) (mv : Meta × V) (hmv : mv ∈ t.msgs ms' k) : mv.2 = vtarget := by
          rw [hm] at hmv
          simp only [MsgStep.eval, hug_get, ↓reduceIte] at hmv
          cases htarget : evalKeyRef m.sem.fixedAtom st.slots keys target <;> simp only [htarget] at hmv
          · rename_i tk
            by_cases hc : k = tk ∧ mask k.1 = true
            · rw [if_true_of hc] at hmv
              rcases FinSet.mem_insert.mp hmv with rfl | hold
              · rfl
              · exact hold_eq k mv hold
            · rw [if_false_of hc] at hmv
              exact hold_eq k mv hmv
          · exact hold_eq k mv hmv
        intro k1 mv1 k2 mv2 h1 h2
        exact (hnew_eq k1 mv1 h1).trans (hnew_eq k2 mv2 h2).symm
    · nomatch hb

theorem valid_rename (p : GroupPerm sizes) (st : m.RState) (hv : m.valid st) : m.valid (rename p st) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨f, mask⟩ hfm
    have hprev := hv.1 (f, mask) hfm
    refine ⟨fun k hk => hprev.1 (p.invFun k) hk, fun k1 k2 h1 h2 => ?_⟩
    have heq := hprev.2 (p.invFun k1) (p.invFun k2) h1 h2
    exact (p.inv_injective).mp heq
  · intro ⟨ms, cid⟩ hmc k mv hmv
    exact hv.2.1 (ms, cid) hmc (p.invFun k) mv hmv
  · intro ms hms k1 mv1 k2 mv2 h1 h2
    exact hv.2.2 ms hms (p.invFun k1) mv1 (p.invFun k2) mv2 h1 h2

theorem next_rename (p : GroupPerm sizes) (st t : m.RState)
    (hv : m.valid st) (hn : m.rawConcrete.next st t) :
    m.rawConcrete.next (rename p st) (rename p t) := by
  rcases hn with ⟨b, w, keys, hpre, hug, keys', aux', hchoices, hpost, hw, hsw, hflags, hmsgs⟩
  have hb_just := (List.all_eq_true.mp m.opsValid_parts.2.2.2.1) b (m.completeB b)
  simp only [Bool.and_eq_true] at hb_just
  let sb := m.ops.stepBranch b
  refine ⟨b, w, renameKeys p keys, ?_, ?_, renameKeys p keys', aux', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [rename_core, PureTest.equivariant]; exact hpre
  · simp only [rename_core, evalUniformGuards_rename]; exact hug
  · simp only [rename_core]
    rw [evalBranchChoices_equivariant p m.sem.constVal m.ops.inv m.sem.keyRank m.sem.recRank
      (m.sem.stepTest b st.core t.core w) (m.sem.stepVal b st.core t.core w)
      (m.sem.stepInt b st.core t.core w) m.sem.fixedAtom st hv sb.choices hb_just.1.1.1 keys {}]
    change (evalBranchChoices m.sem.keyRank m.sem.recRank
      (m.sem.stepTest b st.core t.core w) (m.sem.stepVal b st.core t.core w)
      (m.sem.stepInt b st.core t.core w) m.sem.fixedAtom st keys {} sb.choices).map
      (fun ka => (renameKeys p ka.1, ka.2)) = some (renameKeys p keys', aux')
    rw [hchoices]
    rfl
  · simp only [rename_core]
    rw [ChoiceTest.equivariant p m.sem.constVal m.ops.inv m.sem.keyRank m.sem.recRank
      (m.sem.stepTest b st.core t.core w) (m.sem.stepVal b st.core t.core w)
      (m.sem.stepInt b st.core t.core w) m.sem.fixedAtom st hv sb.postGuard hb_just.1.1.2 keys' aux']
    exact hpost
  · simp only [rename_core, rename_maps]
    rw [applyWrites_equivariant p m.sem.constVal m.ops.inv m.sem.keyRank m.sem.recRank
      (m.sem.stepTest b st.core t.core w) (m.sem.stepVal b st.core t.core w)
      (m.sem.stepInt b st.core t.core w) m.sem.fixedAtom st hv sb.writes hb_just.1.2 keys' aux']
    change (applyWrites m.sem.keyRank m.sem.recRank
      (m.sem.stepTest b st.core t.core w) (m.sem.stepVal b st.core t.core w)
      (m.sem.stepInt b st.core t.core w) m.sem.fixedAtom st keys' aux' sb.writes).map (renameMaps p) =
      some (renameMaps p t.maps)
    rw [hw]
    rfl
  · simp only [rename_core, rename_slots]
    rw [applySlotWrites_equivariant p m.sem.constVal m.ops.inv m.sem.keyRank m.sem.recRank
      (m.sem.stepTest b st.core t.core w) (m.sem.stepVal b st.core t.core w)
      (m.sem.stepInt b st.core t.core w) (m.sem.stepFixed b st.core t.core w)
      m.sem.fixedAtom st hv sb.slotWrites hb_just.2 keys' aux']
    change (applySlotWrites m.sem.keyRank m.sem.recRank
      (m.sem.stepTest b st.core t.core w) (m.sem.stepVal b st.core t.core w)
      (m.sem.stepInt b st.core t.core w) (m.sem.stepFixed b st.core t.core w)
      m.sem.fixedAtom st keys' aux' sb.slotWrites).map (renameSlots p) =
      some (renameSlots p t.slots)
    rw [hsw]
    rfl
  · intro f
    simp only [rename_core, rename_flags]
    exact FlagStep.equivariant p (m.sem.stepTest b st.core t.core w) m.sem.fixedAtom st keys' aux' f (t.flags f) (sb.flagSteps f) (hflags f)
  · intro ms
    simp only [rename_core, rename_msgs]
    rw [MsgStep.equivariant p m.sem.constVal (m.sem.stepTest b st.core t.core w)
      (m.sem.stepVal b st.core t.core w) (m.sem.stepMeta b st.core t.core w)
      m.sem.fixedAtom st sb.uniformGuards keys' aux' ms (sb.msgSteps ms)]
    change (renameMsgs p t.msgs) ms = _
    unfold renameMsgs
    rw [hmsgs ms]

theorem branchHasError_rename_imp (p : GroupPerm sizes) (b : B) (st : m.RState)
    (hv : m.valid st) (herr : m.branchHasError b st) :
    m.branchHasError b (rename p st) := by
  rcases herr with ⟨dcore, w, keys, hpre, hug, hrest⟩
  have hb_just := (List.all_eq_true.mp m.opsValid_parts.2.2.2.1) b (m.completeB b)
  simp only [Bool.and_eq_true] at hb_just
  let sb := m.ops.stepBranch b
  refine ⟨dcore, w, renameKeys p keys, ?_, ?_, ?_⟩
  · simp only [rename_core, PureTest.equivariant]; exact hpre
  · simp only [rename_core, evalUniformGuards_rename]; exact hug
  · simp only [rename_core]
    rw [evalBranchChoices_equivariant p m.sem.constVal m.ops.inv m.sem.keyRank m.sem.recRank
      (m.sem.stepTest b st.core dcore w) (m.sem.stepVal b st.core dcore w)
      (m.sem.stepInt b st.core dcore w) m.sem.fixedAtom st hv sb.choices hb_just.1.1.1 keys {}]
    cases hc : evalBranchChoices m.sem.keyRank m.sem.recRank
        (m.sem.stepTest b st.core dcore w) (m.sem.stepVal b st.core dcore w)
        (m.sem.stepInt b st.core dcore w) m.sem.fixedAtom st keys {} sb.choices with
    | none => trivial
    | some ka =>
      rcases ka with ⟨keys', aux'⟩
      rw [hc] at hrest
      dsimp only [Option.map_some, sb] at hrest ⊢
      rw [ChoiceTest.equivariant p m.sem.constVal m.ops.inv m.sem.keyRank m.sem.recRank
            (m.sem.stepTest b st.core dcore w) (m.sem.stepVal b st.core dcore w)
            (m.sem.stepInt b st.core dcore w) m.sem.fixedAtom st hv (m.ops.stepBranch b).postGuard hb_just.1.1.2 keys' aux']
      cases hp : (m.ops.stepBranch b).postGuard.eval m.sem.keyRank m.sem.recRank
          (m.sem.stepTest b st.core dcore w) (m.sem.stepVal b st.core dcore w)
          (m.sem.stepInt b st.core dcore w) m.sem.fixedAtom st keys' aux' with
      | none => trivial
      | some bv =>
        cases bv with
        | false =>
          rw [hp] at hrest
          exact hrest
        | true =>
          rw [hp] at hrest
          dsimp only [] at hrest ⊢
          rw [applyWrites_equivariant p m.sem.constVal m.ops.inv m.sem.keyRank m.sem.recRank
                (m.sem.stepTest b st.core dcore w) (m.sem.stepVal b st.core dcore w)
                (m.sem.stepInt b st.core dcore w) m.sem.fixedAtom st hv (m.ops.stepBranch b).writes hb_just.1.2 keys' aux',
              applySlotWrites_equivariant p m.sem.constVal m.ops.inv m.sem.keyRank m.sem.recRank
                (m.sem.stepTest b st.core dcore w) (m.sem.stepVal b st.core dcore w)
                (m.sem.stepInt b st.core dcore w) (m.sem.stepFixed b st.core dcore w)
                m.sem.fixedAtom st hv (m.ops.stepBranch b).slotWrites hb_just.2 keys' aux']
          simp only [Option.map_eq_none_iff]
          exact hrest

theorem safe_rename (p : GroupPerm sizes) (st : m.RState) (hv : m.valid st) :
    m.rawConcrete.safe (rename p st) ↔ m.rawConcrete.safe st := by
  have hobs_just := m.opsValid_parts.2.2.2.2
  constructor
  · rintro ⟨hobs, hnoerr⟩
    refine ⟨fun keys => ?_, fun b herr => hnoerr b (m.branchHasError_rename_imp p b st hv herr)⟩
    have hp := hobs (renameKeys p keys)
    simp only [rename_core] at hp
    rwa [ChoiceTest.equivariant p m.sem.constVal m.ops.inv m.sem.keyRank m.sem.recRank
      (m.sem.obsTest st.core) (m.sem.obsVal st.core) (m.sem.obsInt st.core)
      m.sem.fixedAtom st hv m.ops.observation hobs_just keys {}] at hp
  · rintro ⟨hobs, hnoerr⟩
    refine ⟨fun keys => ?_, fun b herr => ?_⟩
    · have hk : renameKeys p (renameKeys p.inverse keys) = keys := by
        funext i; exact p.right (keys i)
      simp only [rename_core]
      rw [← hk, ChoiceTest.equivariant p m.sem.constVal m.ops.inv m.sem.keyRank m.sem.recRank
        (m.sem.obsTest st.core) (m.sem.obsVal st.core) (m.sem.obsInt st.core)
        m.sem.fixedAtom st hv m.ops.observation hobs_just (renameKeys p.inverse keys) {}]
      exact hobs _
    · have hv' := m.valid_rename p st hv
      have herr' := m.branchHasError_rename_imp p.inverse b (rename p st) hv' herr
      rw [rename_inverse] at herr'
      exact hnoerr b herr'

-- Validated concrete system, orbit quotient, and connection back to unrestricted `rawConcrete`.
abbrev ValidState := { st : m.RState // m.valid st }

def renameValid (p : GroupPerm sizes) (s : m.ValidState) : m.ValidState :=
  ⟨rename p s.val, m.valid_rename p s.val s.property⟩

def Orbit (s t : m.ValidState) : Prop :=
  ∃ p : GroupPerm sizes, rename p s.val = t.val

def orbits : Setoid m.ValidState where
  r := m.Orbit
  iseqv := {
    refl := fun s => ⟨GroupPerm.identity, rename_identity s.val⟩
    symm := by
      rintro s t ⟨p, hp⟩
      exact ⟨p.inverse, by rw [← hp, rename_inverse]⟩
    trans := by
      rintro s t u ⟨p, hp⟩ ⟨q, hq⟩
      exact ⟨p.then q, by rw [rename_then, hp, hq]⟩ }

def project (s : m.ValidState) : Quotient m.orbits := Quotient.mk m.orbits s

theorem project_rename (p : GroupPerm sizes) (s : m.ValidState) :
    m.project (m.renameValid p s) = m.project s :=
  (Quotient.sound (show m.orbits.r s (m.renameValid p s) from ⟨p, rfl⟩)).symm

def validConcrete : System m.ValidState where
  initial s := m.rawConcrete.initial s.val
  next s t := m.rawConcrete.next s.val t.val
  safe s := m.rawConcrete.safe s.val

def reduced : System (Quotient m.orbits) where
  initial a := ∃ s, m.validConcrete.initial s ∧ m.project s = a
  next a b := ∃ s t, m.project s = a ∧ m.validConcrete.next s t ∧ m.project t = b
  safe a := Quotient.liftOn a m.validConcrete.safe (by
    rintro s t ⟨p, hp⟩
    have hts : t = m.renameValid p s := Subtype.ext hp.symm
    subst hts
    exact propext (m.safe_rename p s.val s.property).symm)

theorem certificate : Certificate m.validConcrete m.reduced m.project := by
  constructor
  · intro a; rfl
  · intro s a
    constructor
    · rintro ⟨x, t, hx, hn, ht⟩
      obtain ⟨p, hp⟩ := Quotient.exact hx
      have hsx : s = m.renameValid p x := Subtype.ext hp.symm
      subst hsx
      refine ⟨m.renameValid p t, m.next_rename p x.val t.val x.property hn, (m.project_rename p t).trans ht⟩
    · rintro ⟨t, hn, ht⟩
      exact ⟨s, t, rfl, hn, ht⟩
  · intro s; rfl

theorem inductive_invariant (st : m.RState) (hr : Reachable m.rawConcrete st) : m.valid st := by
  induction hr with
  | initial hi => exact m.initial_valid _ hi
  | step _ hn ih => exact m.next_valid _ _ ih hn

theorem reachable_validConcrete_iff (s : m.ValidState) :
    Reachable m.validConcrete s ↔ Reachable m.rawConcrete s.val := by
  constructor
  · intro hr
    induction hr with
    | initial hi => exact .initial hi
    | step _ hn ih => exact .step ih hn
  · intro hr
    have lift : ∀ {st : m.RState}, Reachable m.rawConcrete st → ∀ (hv : m.valid st), Reachable m.validConcrete ⟨st, hv⟩ := by
      intro st hst
      induction hst with
      | initial hi => intro hv; exact .initial hi
      | @step x y hx hn ih =>
        intro hvy
        have hvx := m.inductive_invariant x hx
        exact .step (ih hvx) hn
    exact lift hr s.property

theorem raw_safety_iff :
    (∀ st : m.RState, Reachable m.rawConcrete st → m.rawConcrete.safe st) ↔
    (∀ s : m.ValidState, Reachable m.validConcrete s → m.validConcrete.safe s) := by
  constructor
  · intro h s hs
    exact h s.val ((m.reachable_validConcrete_iff s).mp hs)
  · intro h st hst
    have hv := m.inductive_invariant st hst
    exact h ⟨st, hv⟩ ((m.reachable_validConcrete_iff ⟨st, hv⟩).mpr hst)

theorem optimization_correct :
    (∀ st : m.RState, Reachable m.rawConcrete st → m.rawConcrete.safe st) ↔
    (∀ a, Reachable m.reduced a → m.reduced.safe a) :=
  m.raw_safety_iff.trans (safety_iff m.certificate)

theorem specification_correct :
    (∀ st : m.RState, Reachable (withStuttering m.rawConcrete) st → m.rawConcrete.safe st) ↔
    (∀ a, Reachable (withStuttering m.reduced) a → m.reduced.safe a) := by
  simpa only [stuttering_reachable_iff] using m.optimization_correct

theorem counterexample_lifts {a} (ha : Reachable m.reduced a) (bad : ¬ m.reduced.safe a) :
    ∃ s : m.ValidState, Reachable m.rawConcrete s.val ∧ m.project s = a ∧ ¬ m.rawConcrete.safe s.val := by
  obtain ⟨s, hs, he⟩ := reachable_backward m.certificate ha
  refine ⟨s, (m.reachable_validConcrete_iff s).mp hs, he, ?_⟩
  intro good
  apply bad
  rw [← he]
  exact (m.certificate.observe s).mp good

theorem deadlock_preserved (s : m.ValidState) :
    (¬ ∃ t : m.RState, m.rawConcrete.next s.val t) ↔ (¬ ∃ a, m.reduced.next (m.project s) a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s a).mp ha
    exact noStep ⟨t.val, ht⟩
  · intro noStep ⟨t, ht⟩
    have hvt := m.next_valid s.val t s.property ht
    exact noStep ⟨m.project ⟨t, hvt⟩, (m.certificate.next s (m.project ⟨t, hvt⟩)).mpr ⟨⟨t, hvt⟩, ht, rfl⟩⟩

theorem orbit_key_equivalent (s t : m.ValidState) :
    m.project s = m.project t ↔ m.Orbit s t := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound (show m.orbits.r s t from h)

def rawConstrained : ConstrainedSystem m.RState where
  toSystem := m.rawConcrete
  initSafe st := ∀ keys, m.ops.initObservation.eval m.sem.keyRank m.sem.recRank
    (m.sem.obsTest st.core) (m.sem.obsVal st.core) (m.sem.obsInt st.core)
    m.sem.fixedAtom st keys {} = some true
  constraint st := ∀ keys, m.ops.constraintTest.eval m.sem.keyRank m.sem.recRank
    (m.sem.obsTest st.core) (m.sem.obsVal st.core) (m.sem.obsInt st.core)
    m.sem.fixedAtom st keys {} = some true
  actionConstraint st t := ∀ keys, m.ops.actionConstraintTest.eval
    (m.sem.actionTest st.core t.core) m.sem.fixedAtom st t keys {} = true
  actionSafe st t := ∀ keys, m.ops.actionObservation.eval
    (m.sem.actionTest st.core t.core) m.sem.fixedAtom st t keys {} = true

theorem initSafe_rename (p : GroupPerm sizes) (st : m.RState) (hv : m.valid st) :
    m.rawConstrained.initSafe (rename p st) ↔ m.rawConstrained.initSafe st := by
  have hjust := m.opsValid_constrained_parts.1
  constructor
  · intro h keys
    have hp := h (renameKeys p keys)
    simp only [rename_core] at hp
    rwa [ChoiceTest.equivariant p m.sem.constVal m.ops.inv m.sem.keyRank m.sem.recRank
      (m.sem.obsTest st.core) (m.sem.obsVal st.core) (m.sem.obsInt st.core)
      m.sem.fixedAtom st hv m.ops.initObservation hjust keys {}] at hp
  · intro h keys
    have hk : renameKeys p (renameKeys p.inverse keys) = keys := by funext i; exact p.right (keys i)
    simp only [rename_core]
    rw [← hk, ChoiceTest.equivariant p m.sem.constVal m.ops.inv m.sem.keyRank m.sem.recRank
      (m.sem.obsTest st.core) (m.sem.obsVal st.core) (m.sem.obsInt st.core)
      m.sem.fixedAtom st hv m.ops.initObservation hjust (renameKeys p.inverse keys) {}]
    exact h _

theorem constraint_rename (p : GroupPerm sizes) (st : m.RState) (hv : m.valid st) :
    m.rawConstrained.constraint (rename p st) ↔ m.rawConstrained.constraint st := by
  have hjust := m.opsValid_constrained_parts.2
  constructor
  · intro h keys
    have hp := h (renameKeys p keys)
    simp only [rename_core] at hp
    rwa [ChoiceTest.equivariant p m.sem.constVal m.ops.inv m.sem.keyRank m.sem.recRank
      (m.sem.obsTest st.core) (m.sem.obsVal st.core) (m.sem.obsInt st.core)
      m.sem.fixedAtom st hv m.ops.constraintTest hjust keys {}] at hp
  · intro h keys
    have hk : renameKeys p (renameKeys p.inverse keys) = keys := by funext i; exact p.right (keys i)
    simp only [rename_core]
    rw [← hk, ChoiceTest.equivariant p m.sem.constVal m.ops.inv m.sem.keyRank m.sem.recRank
      (m.sem.obsTest st.core) (m.sem.obsVal st.core) (m.sem.obsInt st.core)
      m.sem.fixedAtom st hv m.ops.constraintTest hjust (renameKeys p.inverse keys) {}]
    exact h _

theorem actionConstraint_rename (p : GroupPerm sizes) (st t : m.RState) :
    m.rawConstrained.actionConstraint (rename p st) (rename p t) ↔
      m.rawConstrained.actionConstraint st t := by
  constructor
  · intro h keys
    have hp := h (renameKeys p keys)
    simp only [rename_core] at hp
    rwa [ActionPureTest.equivariant p (m.sem.actionTest st.core t.core) m.sem.fixedAtom st t m.ops.actionConstraintTest keys {}] at hp
  · intro h keys
    have hk : renameKeys p (renameKeys p.inverse keys) = keys := by funext i; exact p.right (keys i)
    simp only [rename_core]
    rw [← hk, ActionPureTest.equivariant p (m.sem.actionTest st.core t.core) m.sem.fixedAtom st t m.ops.actionConstraintTest (renameKeys p.inverse keys) {}]
    exact h _

theorem actionSafe_rename (p : GroupPerm sizes) (st t : m.RState) :
    m.rawConstrained.actionSafe (rename p st) (rename p t) ↔
      m.rawConstrained.actionSafe st t := by
  constructor
  · intro h keys
    have hp := h (renameKeys p keys)
    simp only [rename_core] at hp
    rwa [ActionPureTest.equivariant p (m.sem.actionTest st.core t.core) m.sem.fixedAtom st t m.ops.actionObservation keys {}] at hp
  · intro h keys
    have hk : renameKeys p (renameKeys p.inverse keys) = keys := by funext i; exact p.right (keys i)
    simp only [rename_core]
    rw [← hk, ActionPureTest.equivariant p (m.sem.actionTest st.core t.core) m.sem.fixedAtom st t m.ops.actionObservation (renameKeys p.inverse keys) {}]
    exact h _

def validConstrained : ConstrainedSystem m.ValidState where
  toSystem := m.validConcrete
  initSafe s := m.rawConstrained.initSafe s.val
  constraint s := m.rawConstrained.constraint s.val
  actionConstraint s t := m.rawConstrained.actionConstraint s.val t.val
  actionSafe s t := m.rawConstrained.actionSafe s.val t.val

def constrainedReduced : ConstrainedSystem (Quotient m.orbits) where
  toSystem := m.reduced
  initSafe a := Quotient.liftOn a m.validConstrained.initSafe (by
    rintro s t ⟨p, hp⟩
    have hts : t = m.renameValid p s := Subtype.ext hp.symm
    subst hts
    exact propext (m.initSafe_rename p s.val s.property).symm)
  constraint a := Quotient.liftOn a m.validConstrained.constraint (by
    rintro s t ⟨p, hp⟩
    have hts : t = m.renameValid p s := Subtype.ext hp.symm
    subst hts
    exact propext (m.constraint_rename p s.val s.property).symm)
  actionConstraint a b := ∃ s t, m.project s = a ∧ m.validConcrete.next s t ∧
    m.validConstrained.actionConstraint s t ∧ m.project t = b
  actionSafe a b := ∀ s t, m.project s = a → m.project t = b → m.validConcrete.next s t →
    m.validConstrained.actionSafe s t

theorem constrained_certificate :
    ConstrainedCertificate m.validConstrained m.constrainedReduced m.project := by
  refine ⟨m.certificate.initial, m.certificate.next, m.certificate.observe, fun _ => Iff.rfl, fun _ => Iff.rfl, ?_, ?_⟩
  · intro s a
    constructor
    · rintro ⟨_, hc, x, y, hx, hxy, hac, hy⟩
      obtain ⟨p, hp⟩ := Quotient.exact hx
      have hsx : s = m.renameValid p x := Subtype.ext hp.symm
      subst hsx
      let t := m.renameValid p y
      have hnext : m.validConcrete.next (m.renameValid p x) t := m.next_rename p x.val y.val x.property hxy
      have hact : m.validConstrained.actionConstraint (m.renameValid p x) t :=
        (m.actionConstraint_rename p x.val y.val).mpr hac
      have hpt : m.project t = a := (m.project_rename p y).trans hy
      have hct : m.validConstrained.constraint t := by
        change m.constrainedReduced.constraint (m.project t)
        rw [hpt]
        exact hc
      exact ⟨t, hnext, hct, hact, hpt⟩
    · rintro ⟨t, hn, hc, hac, rfl⟩
      exact ⟨⟨s, t, rfl, hn, rfl⟩, hc, ⟨s, t, rfl, hn, hac, rfl⟩⟩
  · intro s a
    constructor
    · intro h _ x y hx hy hxy
      obtain ⟨p, hp⟩ := Quotient.exact hx
      have hsx : s = m.renameValid p x := Subtype.ext hp.symm
      subst hsx
      let t := m.renameValid p y
      have hnext : m.validConcrete.next (m.renameValid p x) t := m.next_rename p x.val y.val x.property hxy
      have hpt : m.project t = a := (m.project_rename p y).trans hy
      have has := h t hnext hpt
      exact (m.actionSafe_rename p x.val y.val).mp has
    · intro h t hst hpt
      exact h ⟨s, t, rfl, hst, hpt⟩ s t rfl hpt hst

theorem admitted_validConstrained_iff (s : m.ValidState) :
    AdmittedReachable m.validConstrained s ↔ AdmittedReachable m.rawConstrained s.val := by
  constructor
  · intro hr
    induction hr with
    | initial hi hc => exact .initial hi hc
    | step _ hn hc hac ih => exact .step ih hn hc hac
  · intro hr
    have lift : ∀ {st : m.RState}, AdmittedReachable m.rawConstrained st →
        ∀ (hv : m.valid st), AdmittedReachable m.validConstrained ⟨st, hv⟩ := by
      intro st hst
      induction hst with
      | initial hi hc => intro hv; exact .initial hi hc
      | @step x y hx hn hc hac ih =>
        intro hvy
        have hvx := m.inductive_invariant x (admitted_implies_reachable m.rawConstrained hx)
        exact .step (ih hvx) hn hc hac
    exact lift hr s.property

theorem raw_constrained_safety_iff :
    ConstrainedSafe m.rawConstrained ↔ ConstrainedSafe m.validConstrained := by
  constructor
  · rintro ⟨hInit, hStep⟩
    refine ⟨fun s hs => hInit s.val hs, fun s t hs hst => hStep s.val t.val ((m.admitted_validConstrained_iff s).mp hs) hst⟩
  · rintro ⟨hInit, hStep⟩
    constructor
    · intro st hi
      exact hInit ⟨st, m.initial_valid st hi⟩ hi
    · intro st t hs hst
      have hvst := m.inductive_invariant st (admitted_implies_reachable m.rawConstrained hs)
      have hvt := m.next_valid st t hvst hst
      exact hStep ⟨st, hvst⟩ ⟨t, hvt⟩ ((m.admitted_validConstrained_iff ⟨st, hvst⟩).mpr hs) hst

theorem constrained_optimization_correct :
    ConstrainedSafe m.rawConstrained ↔ ConstrainedSafe m.constrainedReduced :=
  m.raw_constrained_safety_iff.trans (constrained_safety_iff m.constrained_certificate)

theorem constrained_init_counterexample_lifts {a}
    (ha : m.constrainedReduced.initial a)
    (bad : ¬ (m.constrainedReduced.safe a ∧ m.constrainedReduced.initSafe a)) :
    ∃ s : m.ValidState, m.rawConstrained.initial s.val ∧ m.project s = a ∧
      ¬ (m.rawConstrained.safe s.val ∧ m.rawConstrained.initSafe s.val) :=
  TlxOptimization.constrained_init_counterexample_lifts m.constrained_certificate ha bad

theorem constrained_step_counterexample_lifts {a b}
    (ha : AdmittedReachable m.constrainedReduced a) (hab : m.constrainedReduced.next a b)
    (bad : ¬ (m.constrainedReduced.safe b ∧ m.constrainedReduced.actionSafe a b)) :
    ∃ s t : m.ValidState, AdmittedReachable m.rawConstrained s.val ∧ m.rawConstrained.next s.val t.val ∧
      m.project s = a ∧ m.project t = b ∧
      ¬ (m.rawConstrained.safe t.val ∧ m.rawConstrained.actionSafe s.val t.val) := by
  obtain ⟨s, t, hs, hst, hps, hpt, hbad⟩ :=
    TlxOptimization.constrained_step_counterexample_lifts m.constrained_certificate ha hab bad
  exact ⟨s, t, (m.admitted_validConstrained_iff s).mp hs, hst, hps, hpt, hbad⟩

theorem admitted_deadlock_preserved :
    (∃ s : m.RState, AdmittedReachable m.rawConstrained s ∧ ¬ ∃ t : m.RState, m.rawConstrained.next s t) ↔
    (∃ a, AdmittedReachable m.constrainedReduced a ∧ ¬ ∃ b, m.constrainedReduced.next a b) := by
  have hv := constrained_deadlock_iff m.constrained_certificate
  constructor
  · rintro ⟨s, hs, hno⟩
    have hvs := m.inductive_invariant s (admitted_implies_reachable m.rawConstrained hs)
    exact hv.mp ⟨⟨s, hvs⟩, (m.admitted_validConstrained_iff ⟨s, hvs⟩).mpr hs, fun ⟨t, ht⟩ => hno ⟨t.val, ht⟩⟩
  · intro h
    obtain ⟨s, hs, hno⟩ := hv.mpr h
    refine ⟨s.val, (m.admitted_validConstrained_iff s).mp hs, fun ⟨t, ht⟩ => ?_⟩
    have hvt := m.next_valid s.val t s.property ht
    exact hno ⟨⟨t, hvt⟩, ht⟩

end Model
end
end TlxOptimization.ChooseSymRule
