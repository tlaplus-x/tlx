/- Generic recursive finite equivariant value and expression rule IR for disjoint
products of full permutation groups.
All key operations, sets, finite functions, records, sequences, quantifiers,
comprehensions, and cardinalities are explicit. Atom leaves receive key-free
atoms only. -/
set_option autoImplicit false
namespace TlxOptimization.EquivRule
noncomputable section
open TlxOptimization

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

inductive RawVal (K A : Type) where
  | err
  | atom (a : A)
  | key (k : K)
  | seq (xs : List (RawVal K A))
  | set (xs : List (RawVal K A))
  | fn (entries : List (RawVal K A × RawVal K A))

mutual
def renameRaw {d : Nat} {sizes : Fin d → Nat} {A : Type} (p : GroupPerm sizes) :
    RawVal (Key sizes) A → RawVal (Key sizes) A
  | .err => .err
  | .atom a => .atom a
  | .key k => .key (p.toFun k)
  | .seq xs => .seq (renameRawList p xs)
  | .set xs => .set (renameRawList p xs)
  | .fn ps => .fn (renameRawPairs p ps)

def renameRawList {d : Nat} {sizes : Fin d → Nat} {A : Type} (p : GroupPerm sizes) :
    List (RawVal (Key sizes) A) → List (RawVal (Key sizes) A)
  | [] => []
  | x :: xs => renameRaw p x :: renameRawList p xs

def renameRawPairs {d : Nat} {sizes : Fin d → Nat} {A : Type} (p : GroupPerm sizes) :
    List (RawVal (Key sizes) A × RawVal (Key sizes) A) → List (RawVal (Key sizes) A × RawVal (Key sizes) A)
  | [] => []
  | (k, v) :: ps => (renameRaw p k, renameRaw p v) :: renameRawPairs p ps
end

theorem renameRawList_eq_map {d : Nat} {sizes : Fin d → Nat} {A : Type} (p : GroupPerm sizes)
    (xs : List (RawVal (Key sizes) A)) :
    renameRawList p xs = xs.map (renameRaw p) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [renameRawList, List.map_cons, ih]

theorem renameRawPairs_eq_map {d : Nat} {sizes : Fin d → Nat} {A : Type} (p : GroupPerm sizes)
    (ps : List (RawVal (Key sizes) A × RawVal (Key sizes) A)) :
    renameRawPairs p ps = ps.map (fun kv => (renameRaw p kv.1, renameRaw p kv.2)) := by
  induction ps with
  | nil => rfl
  | cons kv ps ih =>
    cases kv
    simp only [renameRawPairs, List.map_cons, ih]

mutual
theorem renameRaw_identity {d : Nat} {sizes : Fin d → Nat} {A : Type} :
    ∀ x : RawVal (Key sizes) A, renameRaw GroupPerm.identity x = x
  | .err => rfl
  | .atom _ => rfl
  | .key ⟨_, _⟩ => rfl
  | .seq xs => congrArg RawVal.seq (renameRawList_identity xs)
  | .set xs => congrArg RawVal.set (renameRawList_identity xs)
  | .fn ps => congrArg RawVal.fn (renameRawPairs_identity ps)

theorem renameRawList_identity {d : Nat} {sizes : Fin d → Nat} {A : Type} :
    ∀ xs : List (RawVal (Key sizes) A), renameRawList GroupPerm.identity xs = xs
  | [] => rfl
  | x :: xs => by simp only [renameRawList, renameRaw_identity x, renameRawList_identity xs]

theorem renameRawPairs_identity {d : Nat} {sizes : Fin d → Nat} {A : Type} :
    ∀ ps : List (RawVal (Key sizes) A × RawVal (Key sizes) A), renameRawPairs GroupPerm.identity ps = ps
  | [] => rfl
  | (k, v) :: ps => by
    simp only [renameRawPairs, renameRaw_identity k, renameRaw_identity v, renameRawPairs_identity ps]
end

mutual
theorem renameRaw_then {d : Nat} {sizes : Fin d → Nat} {A : Type} (p q : GroupPerm sizes) :
    ∀ x : RawVal (Key sizes) A, renameRaw (p.then q) x = renameRaw q (renameRaw p x)
  | .err => rfl
  | .atom _ => rfl
  | .key ⟨_, _⟩ => rfl
  | .seq xs => congrArg RawVal.seq (renameRawList_then p q xs)
  | .set xs => congrArg RawVal.set (renameRawList_then p q xs)
  | .fn ps => congrArg RawVal.fn (renameRawPairs_then p q ps)

theorem renameRawList_then {d : Nat} {sizes : Fin d → Nat} {A : Type} (p q : GroupPerm sizes) :
    ∀ xs : List (RawVal (Key sizes) A), renameRawList (p.then q) xs = renameRawList q (renameRawList p xs)
  | [] => rfl
  | x :: xs => by simp only [renameRawList, renameRaw_then p q x, renameRawList_then p q xs]

theorem renameRawPairs_then {d : Nat} {sizes : Fin d → Nat} {A : Type} (p q : GroupPerm sizes) :
    ∀ ps : List (RawVal (Key sizes) A × RawVal (Key sizes) A),
      renameRawPairs (p.then q) ps = renameRawPairs q (renameRawPairs p ps)
  | [] => rfl
  | (k, v) :: ps => by
    simp only [renameRawPairs, renameRaw_then p q k, renameRaw_then p q v, renameRawPairs_then p q ps]
end

theorem GroupPerm.then_inverse {d : Nat} {sizes : Fin d → Nat} (p : GroupPerm sizes) :
    p.then p.inverse = GroupPerm.identity := by
  funext g
  have hl : (fun k => (p g).invFun ((p g).toFun k)) = id := funext (p g).left
  unfold GroupPerm.then GroupPerm.inverse GroupPerm.identity Permutation.then Permutation.inverse Permutation.identity
  simp only [hl]

theorem renameRaw_inverse {d : Nat} {sizes : Fin d → Nat} {A : Type} (p : GroupPerm sizes)
    (x : RawVal (Key sizes) A) :
    renameRaw p.inverse (renameRaw p x) = x := by
  rw [← renameRaw_then p p.inverse x, GroupPerm.then_inverse]
  exact renameRaw_identity x

mutual
def rawDepth {K A : Type} : RawVal K A → Nat
  | .err => 0
  | .atom _ => 0
  | .key _ => 0
  | .seq xs => 1 + rawDepthList xs
  | .set xs => 1 + rawDepthList xs
  | .fn ps => 1 + rawDepthPairs ps

def rawDepthList {K A : Type} : List (RawVal K A) → Nat
  | [] => 0
  | x :: xs => max (rawDepth x) (rawDepthList xs)

def rawDepthPairs {K A : Type} : List (RawVal K A × RawVal K A) → Nat
  | [] => 0
  | (k, v) :: ps => max (max (rawDepth k) (rawDepth v)) (rawDepthPairs ps)
end

private theorem rawDepth_mem_list {K A : Type} {xs : List (RawVal K A)} {x : RawVal K A} (h : x ∈ xs) :
    rawDepth x ≤ rawDepthList xs := by
  induction xs with
  | nil => cases h
  | cons a t ih =>
    simp only [rawDepthList]
    rcases List.mem_cons.mp h with rfl | ht
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih ht) (Nat.le_max_right _ _)

private theorem rawDepth_mem_pairs {K A : Type} {ps : List (RawVal K A × RawVal K A)}
    {kv : RawVal K A × RawVal K A} (h : kv ∈ ps) :
    rawDepth kv.1 ≤ rawDepthPairs ps ∧ rawDepth kv.2 ≤ rawDepthPairs ps := by
  induction ps with
  | nil => cases h
  | cons p t ih =>
    rcases p with ⟨k, v⟩
    simp only [rawDepthPairs]
    rcases List.mem_cons.mp h with rfl | ht
    · exact ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),
             Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)⟩
    · rcases ih ht with ⟨h1, h2⟩
      exact ⟨Nat.le_trans h1 (Nat.le_max_right _ _), Nat.le_trans h2 (Nat.le_max_right _ _)⟩

mutual
theorem rawDepth_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} (p : GroupPerm sizes) :
    ∀ x : RawVal (Key sizes) A, rawDepth (renameRaw p x) = rawDepth x
  | .err => rfl
  | .atom _ => rfl
  | .key _ => rfl
  | .seq xs => congrArg (1 + ·) (rawDepthList_rename p xs)
  | .set xs => congrArg (1 + ·) (rawDepthList_rename p xs)
  | .fn ps => congrArg (1 + ·) (rawDepthPairs_rename p ps)

theorem rawDepthList_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} (p : GroupPerm sizes) :
    ∀ xs : List (RawVal (Key sizes) A), rawDepthList (renameRawList p xs) = rawDepthList xs
  | [] => rfl
  | x :: xs => by simp only [renameRawList, rawDepthList, rawDepth_rename p x, rawDepthList_rename p xs]

theorem rawDepthPairs_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} (p : GroupPerm sizes) :
    ∀ ps : List (RawVal (Key sizes) A × RawVal (Key sizes) A),
      rawDepthPairs (renameRawPairs p ps) = rawDepthPairs ps
  | [] => rfl
  | (k, v) :: ps => by
    simp only [renameRawPairs, rawDepthPairs, rawDepth_rename p k, rawDepth_rename p v, rawDepthPairs_rename p ps]
end

class HasNatAtom (A : Type) where
  natAtom : Nat → A
  natAtom_inj : ∀ m n, natAtom m = natAtom n → m = n

def seqPairsAux {K A : Type} (natAtom : Nat → A) : Nat → List (RawVal K A) → List (RawVal K A × RawVal K A)
  | _, [] => []
  | i, x :: xs => (.atom (natAtom i), x) :: seqPairsAux natAtom (i + 1) xs

def seqPairs {K A : Type} [HasNatAtom A] (xs : List (RawVal K A)) : List (RawVal K A × RawVal K A) :=
  seqPairsAux HasNatAtom.natAtom 1 xs

def rawFnPairs {K A : Type} [HasNatAtom A] : RawVal K A → Option (List (RawVal K A × RawVal K A))
  | .fn ps => some ps
  | .seq xs => some (seqPairs xs)
  | _ => none

private theorem mem_seqPairsAux {K A : Type} (natAtom : Nat → A) :
    ∀ (base : Nat) (xs : List (RawVal K A)) (kv : RawVal K A × RawVal K A),
      kv ∈ seqPairsAux natAtom base xs ↔
        ∃ (j : Nat) (hj : j < xs.length), kv = (.atom (natAtom (base + j)), xs[j])
  | _, [], _ => Iff.intro (fun h => nomatch h) (fun ⟨_, hj, _⟩ => nomatch hj)
  | base, x :: xs, kv => by
    simp only [seqPairsAux, List.mem_cons, mem_seqPairsAux natAtom (base + 1) xs]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨0, Nat.zero_lt_succ _, rfl⟩
      · refine ⟨j + 1, Nat.succ_lt_succ hj, ?_⟩
        simp only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 j]
    · rintro ⟨j, hj, rfl⟩
      cases j with
      | zero => left; rfl
      | succ j' =>
        right
        refine ⟨j', Nat.lt_of_succ_lt_succ hj, ?_⟩
        simp only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 j']

private theorem rawDepth_mem_seqPairsAux {K A : Type} (natAtom : Nat → A)
    {base : Nat} {xs : List (RawVal K A)} {kv : RawVal K A × RawVal K A}
    (h : kv ∈ seqPairsAux natAtom base xs) :
    rawDepth kv.1 = 0 ∧ rawDepth kv.2 ≤ rawDepthList xs := by
  rcases (mem_seqPairsAux natAtom base xs kv).mp h with ⟨j, hj, rfl⟩
  exact ⟨rfl, rawDepth_mem_list (List.getElem_mem hj)⟩

private theorem rawDepth_mem_rawFnPairs {K A : Type} [HasNatAtom A]
    {x : RawVal K A} {ps : List (RawVal K A × RawVal K A)}
    (h : rawFnPairs x = some ps) {kv : RawVal K A × RawVal K A} (hkv : kv ∈ ps) :
    rawDepth kv.1 < rawDepth x ∧ rawDepth kv.2 < rawDepth x := by
  cases x with
  | fn qs =>
    simp only [rawFnPairs, Option.some.injEq] at h
    subst h
    rcases rawDepth_mem_pairs hkv with ⟨h1, h2⟩
    simp only [rawDepth]; omega
  | seq xs =>
    simp only [rawFnPairs, Option.some.injEq] at h
    subst h
    rcases rawDepth_mem_seqPairsAux HasNatAtom.natAtom hkv with ⟨h1, h2⟩
    simp only [rawDepth]; omega
  | _ => cases h

private theorem seqPairsAux_rename {d : Nat} {sizes : Fin d → Nat} {A : Type}
    (p : GroupPerm sizes) (natAtom : Nat → A) :
    ∀ (base : Nat) (xs : List (RawVal (Key sizes) A)),
      seqPairsAux natAtom base (renameRawList p xs) = renameRawPairs p (seqPairsAux natAtom base xs)
  | _, [] => rfl
  | base, x :: xs => by
    simp only [renameRawList, seqPairsAux, renameRawPairs, renameRaw, seqPairsAux_rename p natAtom (base + 1) xs]

private theorem rawFnPairs_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (x : RawVal (Key sizes) A) :
    rawFnPairs (renameRaw p x) = (rawFnPairs x).map (renameRawPairs p) := by
  cases x with
  | fn ps => rfl
  | seq xs =>
    simp only [renameRaw, rawFnPairs, Option.map_some, seqPairs, seqPairsAux_rename]
  | _ => rfl

def fnPairsEq {K A : Type} (R : RawVal K A → RawVal K A → Prop)
    (ps qs : List (RawVal K A × RawVal K A)) : Prop :=
  (∀ kv ∈ ps, ∃ q ∈ qs, R kv.1 q.1 ∧ R kv.2 q.2) ∧
  (∀ q ∈ qs, ∃ kv ∈ ps, R kv.1 q.1 ∧ R kv.2 q.2)

def ValEqAux {K A : Type} [HasNatAtom A] : Nat → RawVal K A → RawVal K A → Prop
  | 0, _, _ => False
  | _ + 1, .err, .err => True
  | _ + 1, .atom a, .atom b => a = b
  | _ + 1, .key k1, .key k2 => k1 = k2
  | n + 1, .set xs, .set ys =>
      (∀ x ∈ xs, ∃ y ∈ ys, ValEqAux n x y) ∧ (∀ y ∈ ys, ∃ x ∈ xs, ValEqAux n x y)
  | n + 1, .seq xs, .seq ys => fnPairsEq (ValEqAux n) (seqPairs xs) (seqPairs ys)
  | n + 1, .seq xs, .fn qs => fnPairsEq (ValEqAux n) (seqPairs xs) qs
  | n + 1, .fn ps, .seq ys => fnPairsEq (ValEqAux n) ps (seqPairs ys)
  | n + 1, .fn ps, .fn qs => fnPairsEq (ValEqAux n) ps qs
  | _ + 1, _, _ => False

private theorem valEqAux_fnPairs {K A : Type} [HasNatAtom A] {n : Nat} {x y : RawVal K A}
    {ps qs : List (RawVal K A × RawVal K A)}
    (hx : rawFnPairs x = some ps) (hy : rawFnPairs y = some qs) :
    ValEqAux (n + 1) x y ↔ fnPairsEq (ValEqAux n) ps qs := by
  cases x with
  | fn _ | seq _ =>
    cases hx
    cases y with
    | fn _ | seq _ => cases hy; exact Iff.rfl
    | _ => cases hy
  | _ => cases hx

theorem ValEqAux_irrel {K A : Type} [HasNatAtom A] :
    ∀ (n m : Nat) (x y : RawVal K A), rawDepth x < n → rawDepth x < m →
      (ValEqAux n x y ↔ ValEqAux m x y)
  | 0, _, _, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | _, 0, _, _, _, hm => absurd hm (Nat.not_lt_zero _)
  | n + 1, m + 1, x, y, hn, hm => by
    have hfp : ∀ {ps qs : List (RawVal K A × RawVal K A)},
        rawFnPairs x = some ps → rawFnPairs y = some qs →
        (fnPairsEq (ValEqAux n) ps qs ↔ fnPairsEq (ValEqAux m) ps qs) := by
      intro ps qs hx hy
      unfold fnPairsEq
      apply and_congr
      · constructor
        · intro h a ha
          rcases rawDepth_mem_rawFnPairs hx ha with ⟨hd1, hd2⟩
          rcases h a ha with ⟨b, hb, h1, h2⟩
          exact ⟨b, hb, (ValEqAux_irrel n m a.1 b.1 (by omega) (by omega)).mp h1,
                        (ValEqAux_irrel n m a.2 b.2 (by omega) (by omega)).mp h2⟩
        · intro h a ha
          rcases rawDepth_mem_rawFnPairs hx ha with ⟨hd1, hd2⟩
          rcases h a ha with ⟨b, hb, h1, h2⟩
          exact ⟨b, hb, (ValEqAux_irrel n m a.1 b.1 (by omega) (by omega)).mpr h1,
                        (ValEqAux_irrel n m a.2 b.2 (by omega) (by omega)).mpr h2⟩
      · constructor
        · intro h b hb
          rcases h b hb with ⟨a, ha, h1, h2⟩
          rcases rawDepth_mem_rawFnPairs hx ha with ⟨hd1, hd2⟩
          exact ⟨a, ha, (ValEqAux_irrel n m a.1 b.1 (by omega) (by omega)).mp h1,
                        (ValEqAux_irrel n m a.2 b.2 (by omega) (by omega)).mp h2⟩
        · intro h b hb
          rcases h b hb with ⟨a, ha, h1, h2⟩
          rcases rawDepth_mem_rawFnPairs hx ha with ⟨hd1, hd2⟩
          exact ⟨a, ha, (ValEqAux_irrel n m a.1 b.1 (by omega) (by omega)).mpr h1,
                        (ValEqAux_irrel n m a.2 b.2 (by omega) (by omega)).mpr h2⟩
    cases x with
    | err => cases y <;> exact Iff.rfl
    | atom _ => cases y <;> exact Iff.rfl
    | key _ => cases y <;> exact Iff.rfl
    | set xs =>
      cases y with
      | set ys =>
        simp only [rawDepth] at hn hm
        apply and_congr
        · constructor
          · intro h a ha
            have hd := rawDepth_mem_list ha
            rcases h a ha with ⟨b, hb, hab⟩
            exact ⟨b, hb, (ValEqAux_irrel n m a b (by omega) (by omega)).mp hab⟩
          · intro h a ha
            have hd := rawDepth_mem_list ha
            rcases h a ha with ⟨b, hb, hab⟩
            exact ⟨b, hb, (ValEqAux_irrel n m a b (by omega) (by omega)).mpr hab⟩
        · constructor
          · intro h b hb
            rcases h b hb with ⟨a, ha, hab⟩
            have hd := rawDepth_mem_list ha
            exact ⟨a, ha, (ValEqAux_irrel n m a b (by omega) (by omega)).mp hab⟩
          · intro h b hb
            rcases h b hb with ⟨a, ha, hab⟩
            have hd := rawDepth_mem_list ha
            exact ⟨a, ha, (ValEqAux_irrel n m a b (by omega) (by omega)).mpr hab⟩
      | _ => exact Iff.rfl
    | seq _ | fn _ =>
      cases y with
      | seq _ | fn _ => exact hfp rfl rfl
      | _ => exact Iff.rfl

def ValEq {K A : Type} [HasNatAtom A] (x y : RawVal K A) : Prop :=
  ValEqAux (rawDepth x + 1) x y

theorem ValEq_iff_aux {K A : Type} [HasNatAtom A] {n : Nat} {x y : RawVal K A} (h : rawDepth x < n) :
    ValEq x y ↔ ValEqAux n x y :=
  ValEqAux_irrel (rawDepth x + 1) n x y (Nat.lt_succ_self _) h

theorem ValEqAux_refl {K A : Type} [HasNatAtom A] :
    ∀ (n : Nat) (x : RawVal K A), rawDepth x < n → ValEqAux n x x
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, .err, _ => trivial
  | n + 1, .atom _, _ => rfl
  | n + 1, .key _, _ => rfl
  | n + 1, .seq xs, h => by
    refine ⟨fun a ha => ⟨a, ha,
              ValEqAux_refl n a.1 (by have := (rawDepth_mem_rawFnPairs (x := .seq xs) rfl ha).1; omega),
              ValEqAux_refl n a.2 (by have := (rawDepth_mem_rawFnPairs (x := .seq xs) rfl ha).2; omega)⟩,
            fun a ha => ⟨a, ha,
              ValEqAux_refl n a.1 (by have := (rawDepth_mem_rawFnPairs (x := .seq xs) rfl ha).1; omega),
              ValEqAux_refl n a.2 (by have := (rawDepth_mem_rawFnPairs (x := .seq xs) rfl ha).2; omega)⟩⟩
  | n + 1, .set xs, h => by
    simp only [rawDepth] at h
    refine ⟨fun a ha => ⟨a, ha, ValEqAux_refl n a (by have := rawDepth_mem_list ha; omega)⟩,
            fun a ha => ⟨a, ha, ValEqAux_refl n a (by have := rawDepth_mem_list ha; omega)⟩⟩
  | n + 1, .fn ps, h => by
    simp only [rawDepth] at h
    refine ⟨fun a ha => ⟨a, ha,
              ValEqAux_refl n a.1 (by have := (rawDepth_mem_pairs ha).1; omega),
              ValEqAux_refl n a.2 (by have := (rawDepth_mem_pairs ha).2; omega)⟩,
            fun a ha => ⟨a, ha,
              ValEqAux_refl n a.1 (by have := (rawDepth_mem_pairs ha).1; omega),
              ValEqAux_refl n a.2 (by have := (rawDepth_mem_pairs ha).2; omega)⟩⟩

theorem ValEq.refl {K A : Type} [HasNatAtom A] (x : RawVal K A) : ValEq x x :=
  ValEqAux_refl (rawDepth x + 1) x (Nat.lt_succ_self _)

private theorem fnPairsEq_symm {K A : Type} [HasNatAtom A] {n : Nat}
    {ps qs : List (RawVal K A × RawVal K A)}
    (hsym : ∀ a b : RawVal K A, ValEqAux n a b → ValEqAux n b a)
    (h : fnPairsEq (ValEqAux n) ps qs) : fnPairsEq (ValEqAux n) qs ps := by
  rcases h with ⟨h1, h2⟩
  exact ⟨fun b hb => let ⟨a, ha, h1e, h2e⟩ := h2 b hb; ⟨a, ha, hsym a.1 b.1 h1e, hsym a.2 b.2 h2e⟩,
         fun a ha => let ⟨b, hb, h1e, h2e⟩ := h1 a ha; ⟨b, hb, hsym a.1 b.1 h1e, hsym a.2 b.2 h2e⟩⟩

theorem ValEqAux_symm {K A : Type} [HasNatAtom A] :
    ∀ (n : Nat) (x y : RawVal K A), ValEqAux n x y → ValEqAux n y x
  | 0, _, _, h => False.elim h
  | n + 1, x, y, h => by
    cases x with
    | err => cases y with | err => trivial | _ => exact False.elim h
    | atom _ => cases y with | atom _ => exact h.symm | _ => exact False.elim h
    | key _ => cases y with | key _ => exact h.symm | _ => exact False.elim h
    | set xs =>
      cases y with
      | set ys =>
        rcases h with ⟨h1, h2⟩
        exact ⟨fun b hb => let ⟨a, ha, hab⟩ := h2 b hb; ⟨a, ha, ValEqAux_symm n a b hab⟩,
               fun a ha => let ⟨b, hb, hab⟩ := h1 a ha; ⟨b, hb, ValEqAux_symm n a b hab⟩⟩
      | _ => exact False.elim h
    | seq _ | fn _ =>
      cases y with
      | seq _ | fn _ => exact fnPairsEq_symm (ValEqAux_symm n) h
      | _ => exact False.elim h

theorem ValEq.symm {K A : Type} [HasNatAtom A] {x y : RawVal K A} (h : ValEq x y) : ValEq y x := by
  let n := max (rawDepth x) (rawDepth y) + 1
  have h1 : ValEqAux n x y := (ValEq_iff_aux (by omega)).mp h
  exact (ValEq_iff_aux (by omega)).mpr (ValEqAux_symm n x y h1)

private theorem fnPairsEq_trans {K A : Type} [HasNatAtom A] {n : Nat}
    {ps qs rs : List (RawVal K A × RawVal K A)}
    (htr : ∀ a b c : RawVal K A, ValEqAux n a b → ValEqAux n b c → ValEqAux n a c)
    (h12 : fnPairsEq (ValEqAux n) ps qs) (h23 : fnPairsEq (ValEqAux n) qs rs) :
    fnPairsEq (ValEqAux n) ps rs := by
  rcases h12 with ⟨h1, h2⟩
  rcases h23 with ⟨h3, h4⟩
  exact ⟨fun a ha => let ⟨b, hb, h1a, h1b⟩ := h1 a ha; let ⟨c, hc, h2a, h2b⟩ := h3 b hb;
           ⟨c, hc, htr a.1 b.1 c.1 h1a h2a, htr a.2 b.2 c.2 h1b h2b⟩,
         fun c hc => let ⟨b, hb, h2a, h2b⟩ := h4 c hc; let ⟨a, ha, h1a, h1b⟩ := h2 b hb;
           ⟨a, ha, htr a.1 b.1 c.1 h1a h2a, htr a.2 b.2 c.2 h1b h2b⟩⟩

theorem ValEqAux_trans {K A : Type} [HasNatAtom A] :
    ∀ (n : Nat) (x y z : RawVal K A), ValEqAux n x y → ValEqAux n y z → ValEqAux n x z
  | 0, _, _, _, h, _ => False.elim h
  | n + 1, x, y, z, hxy, hyz => by
    cases x with
    | err =>
      cases y with
      | err => cases z with | err => trivial | _ => exact False.elim hyz
      | _ => exact False.elim hxy
    | atom _ =>
      cases y with
      | atom _ => cases z with | atom _ => exact hxy.trans hyz | _ => exact False.elim hyz
      | _ => exact False.elim hxy
    | key _ =>
      cases y with
      | key _ => cases z with | key _ => exact hxy.trans hyz | _ => exact False.elim hyz
      | _ => exact False.elim hxy
    | set xs =>
      cases y with
      | set ys =>
        cases z with
        | set zs =>
          rcases hxy with ⟨h1, h2⟩
          rcases hyz with ⟨h3, h4⟩
          exact ⟨fun a ha => let ⟨b, hb, h1e⟩ := h1 a ha; let ⟨c, hc, h2e⟩ := h3 b hb; ⟨c, hc, ValEqAux_trans n a b c h1e h2e⟩,
                 fun c hc => let ⟨b, hb, h2e⟩ := h4 c hc; let ⟨a, ha, h1e⟩ := h2 b hb; ⟨a, ha, ValEqAux_trans n a b c h1e h2e⟩⟩
        | _ => exact False.elim hyz
      | _ => exact False.elim hxy
    | seq _ | fn _ =>
      cases y with
      | seq _ | fn _ =>
        cases z with
        | seq _ | fn _ => exact fnPairsEq_trans (ValEqAux_trans n) hxy hyz
        | _ => exact False.elim hyz
      | _ => exact False.elim hxy

theorem ValEq.trans {K A : Type} [HasNatAtom A] {x y z : RawVal K A} (hxy : ValEq x y) (hyz : ValEq y z) : ValEq x z := by
  let n := max (max (rawDepth x) (rawDepth y)) (rawDepth z) + 1
  have h1 : ValEqAux n x y := (ValEq_iff_aux (by omega)).mp hxy
  have h2 : ValEqAux n y z := (ValEq_iff_aux (by omega)).mp hyz
  exact (ValEq_iff_aux (by omega)).mpr (ValEqAux_trans n x y z h1 h2)

private theorem fnPairsEq_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) {n : Nat} {ps qs : List (RawVal (Key sizes) A × RawVal (Key sizes) A)}
    (hren : ∀ a b : RawVal (Key sizes) A, ValEqAux n (renameRaw p a) (renameRaw p b) ↔ ValEqAux n a b) :
    fnPairsEq (ValEqAux n) (renameRawPairs p ps) (renameRawPairs p qs) ↔ fnPairsEq (ValEqAux n) ps qs := by
  simp only [fnPairsEq, renameRawPairs_eq_map]
  apply and_congr
  · constructor
    · intro h a ha
      rcases h (renameRaw p a.1, renameRaw p a.2) (List.mem_map_of_mem ha) with ⟨b', hb', h1, h2⟩
      rcases List.mem_map.mp hb' with ⟨b, hb, rfl⟩
      exact ⟨b, hb, (hren a.1 b.1).mp h1, (hren a.2 b.2).mp h2⟩
    · intro h a' ha'
      rcases List.mem_map.mp ha' with ⟨a, ha, rfl⟩
      rcases h a ha with ⟨b, hb, h1, h2⟩
      exact ⟨(renameRaw p b.1, renameRaw p b.2), List.mem_map_of_mem hb,
        (hren a.1 b.1).mpr h1, (hren a.2 b.2).mpr h2⟩
  · constructor
    · intro h b hb
      rcases h (renameRaw p b.1, renameRaw p b.2) (List.mem_map_of_mem hb) with ⟨a', ha', h1, h2⟩
      rcases List.mem_map.mp ha' with ⟨a, ha, rfl⟩
      exact ⟨a, ha, (hren a.1 b.1).mp h1, (hren a.2 b.2).mp h2⟩
    · intro h b' hb'
      rcases List.mem_map.mp hb' with ⟨b, hb, rfl⟩
      rcases h b hb with ⟨a, ha, h1, h2⟩
      exact ⟨(renameRaw p a.1, renameRaw p a.2), List.mem_map_of_mem ha,
        (hren a.1 b.1).mpr h1, (hren a.2 b.2).mpr h2⟩

theorem ValEqAux_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) :
    ∀ (n : Nat) (x y : RawVal (Key sizes) A),
      ValEqAux n (renameRaw p x) (renameRaw p y) ↔ ValEqAux n x y
  | 0, _, _ => Iff.rfl
  | n + 1, x, y => by
    cases x with
    | err => cases y <;> exact Iff.rfl
    | atom _ => cases y <;> exact Iff.rfl
    | key _ =>
      cases y with
      | key _ => exact p.injective
      | _ => exact Iff.rfl
    | set xs =>
      cases y with
      | set ys =>
        change ((∀ a ∈ renameRawList p xs, ∃ b ∈ renameRawList p ys, ValEqAux n a b) ∧
                (∀ b ∈ renameRawList p ys, ∃ a ∈ renameRawList p xs, ValEqAux n a b)) ↔ _
        rw [renameRawList_eq_map, renameRawList_eq_map]
        apply and_congr
        · constructor
          · intro h a ha
            rcases h (renameRaw p a) (List.mem_map_of_mem ha) with ⟨b', hb', hab⟩
            rcases List.mem_map.mp hb' with ⟨b, hb, rfl⟩
            exact ⟨b, hb, (ValEqAux_rename p n a b).mp hab⟩
          · intro h a' ha'
            rcases List.mem_map.mp ha' with ⟨a, ha, rfl⟩
            rcases h a ha with ⟨b, hb, hab⟩
            exact ⟨renameRaw p b, List.mem_map_of_mem hb, (ValEqAux_rename p n a b).mpr hab⟩
        · constructor
          · intro h b hb
            rcases h (renameRaw p b) (List.mem_map_of_mem hb) with ⟨a', ha', hab⟩
            rcases List.mem_map.mp ha' with ⟨a, ha, rfl⟩
            exact ⟨a, ha, (ValEqAux_rename p n a b).mp hab⟩
          · intro h b' hb'
            rcases List.mem_map.mp hb' with ⟨b, hb, rfl⟩
            rcases h b hb with ⟨a, ha, hab⟩
            exact ⟨renameRaw p a, List.mem_map_of_mem ha, (ValEqAux_rename p n a b).mpr hab⟩
      | _ => exact Iff.rfl
    | seq xs =>
      cases y with
      | seq ys =>
        change fnPairsEq (ValEqAux n) (seqPairs (renameRawList p xs)) (seqPairs (renameRawList p ys)) ↔ _
        rw [seqPairs, seqPairs, seqPairsAux_rename, seqPairsAux_rename]
        exact fnPairsEq_rename p (ValEqAux_rename p n)
      | fn qs =>
        change fnPairsEq (ValEqAux n) (seqPairs (renameRawList p xs)) (renameRawPairs p qs) ↔ _
        rw [seqPairs, seqPairsAux_rename]
        exact fnPairsEq_rename p (ValEqAux_rename p n)
      | _ => exact Iff.rfl
    | fn ps =>
      cases y with
      | seq ys =>
        change fnPairsEq (ValEqAux n) (renameRawPairs p ps) (seqPairs (renameRawList p ys)) ↔ _
        rw [seqPairs, seqPairsAux_rename]
        exact fnPairsEq_rename p (ValEqAux_rename p n)
      | fn qs => exact fnPairsEq_rename p (ValEqAux_rename p n)
      | _ => exact Iff.rfl

theorem ValEq.rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (x y : RawVal (Key sizes) A) :
    ValEq (renameRaw p x) (renameRaw p y) ↔ ValEq x y := by
  unfold ValEq
  rw [rawDepth_rename]
  exact ValEqAux_rename p (rawDepth x + 1) x y

theorem ValEq.rawFnPairs_some {K A : Type} [HasNatAtom A] {x y : RawVal K A}
    (h : ValEq x y) :
    (rawFnPairs x).isSome = (rawFnPairs y).isSome := by
  cases x with
  | seq _ | fn _ =>
    cases y with
    | seq _ | fn _ => rfl
    | _ => exact False.elim h
  | _ =>
    cases y with
    | seq _ | fn _ => exact False.elim h
    | _ => rfl

theorem ValEq.fnPairs_iff {K A : Type} [HasNatAtom A] {x y : RawVal K A}
    {ps qs : List (RawVal K A × RawVal K A)}
    (hx : rawFnPairs x = some ps) (hy : rawFnPairs y = some qs) :
    ValEq x y ↔
      (∀ kv ∈ ps, ∃ q ∈ qs, ValEq kv.1 q.1 ∧ ValEq kv.2 q.2) ∧
      (∀ q ∈ qs, ∃ kv ∈ ps, ValEq kv.1 q.1 ∧ ValEq kv.2 q.2) := by
  unfold ValEq
  rw [valEqAux_fnPairs hx hy]
  unfold fnPairsEq
  apply and_congr
  · constructor
    · intro h a ha
      rcases rawDepth_mem_rawFnPairs hx ha with ⟨hd1, hd2⟩
      rcases h a ha with ⟨b, hb, h1, h2⟩
      exact ⟨b, hb, (ValEq_iff_aux (by omega)).mpr h1, (ValEq_iff_aux (by omega)).mpr h2⟩
    · intro h a ha
      rcases rawDepth_mem_rawFnPairs hx ha with ⟨hd1, hd2⟩
      rcases h a ha with ⟨b, hb, h1, h2⟩
      exact ⟨b, hb, (ValEq_iff_aux (by omega)).mp h1, (ValEq_iff_aux (by omega)).mp h2⟩
  · constructor
    · intro h b hb
      rcases h b hb with ⟨a, ha, h1, h2⟩
      rcases rawDepth_mem_rawFnPairs hx ha with ⟨hd1, hd2⟩
      exact ⟨a, ha, (ValEq_iff_aux (by omega)).mpr h1, (ValEq_iff_aux (by omega)).mpr h2⟩
    · intro h b hb
      rcases h b hb with ⟨a, ha, h1, h2⟩
      rcases rawDepth_mem_rawFnPairs hx ha with ⟨hd1, hd2⟩
      exact ⟨a, ha, (ValEq_iff_aux (by omega)).mp h1, (ValEq_iff_aux (by omega)).mp h2⟩

theorem ValEq.set_iff {K A : Type} [HasNatAtom A] {xs ys : List (RawVal K A)} :
    ValEq (.set xs) (.set ys) ↔
      (∀ x ∈ xs, ∃ y ∈ ys, ValEq x y) ∧ (∀ y ∈ ys, ∃ x ∈ xs, ValEq x y) := by
  change ((∀ x ∈ xs, ∃ y ∈ ys, ValEqAux (rawDepth (.set xs)) x y) ∧
          (∀ y ∈ ys, ∃ x ∈ xs, ValEqAux (rawDepth (.set xs)) x y)) ↔ _
  have hdep : ∀ a ∈ xs, rawDepth a < rawDepth (.set xs) := fun a ha => by
    have := rawDepth_mem_list ha
    simp only [rawDepth]
    omega
  apply and_congr
  · constructor
    · intro h a ha
      rcases h a ha with ⟨b, hb, hab⟩
      exact ⟨b, hb, (ValEq_iff_aux (hdep a ha)).mpr hab⟩
    · intro h a ha
      rcases h a ha with ⟨b, hb, hab⟩
      exact ⟨b, hb, (ValEq_iff_aux (hdep a ha)).mp hab⟩
  · constructor
    · intro h b hb
      rcases h b hb with ⟨a, ha, hab⟩
      exact ⟨a, ha, (ValEq_iff_aux (hdep a ha)).mpr hab⟩
    · intro h b hb
      rcases h b hb with ⟨a, ha, hab⟩
      exact ⟨a, ha, (ValEq_iff_aux (hdep a ha)).mp hab⟩

theorem ValEq.fn_iff {K A : Type} [HasNatAtom A] {ps qs : List (RawVal K A × RawVal K A)} :
    ValEq (.fn ps) (.fn qs) ↔
      (∀ kv ∈ ps, ∃ q ∈ qs, ValEq kv.1 q.1 ∧ ValEq kv.2 q.2) ∧
      (∀ q ∈ qs, ∃ kv ∈ ps, ValEq kv.1 q.1 ∧ ValEq kv.2 q.2) :=
  ValEq.fnPairs_iff (x := .fn ps) (y := .fn qs) rfl rfl

private theorem lift_set_sound {K A : Type} [HasNatAtom A] {β : Sort _}
    {g : RawVal K A → β} {fallback : β}
    (hset : ∀ xs ys, ValEq (.set xs) (.set ys) → g (.set xs) = g (.set ys))
    (herr : g .err = fallback := by rfl)
    (hatom : ∀ a, g (.atom a) = fallback := by intro _; rfl)
    (hkey : ∀ k, g (.key k) = fallback := by intro _; rfl)
    (hseq : ∀ xs, g (.seq xs) = fallback := by intro _; rfl)
    (hfn : ∀ ps, g (.fn ps) = fallback := by intro _; rfl)
    (s1 s2 : RawVal K A) (h : ValEq s1 s2) : g s1 = g s2 := by
  cases s1 with
  | set xs =>
    cases s2 with
    | set ys => exact hset xs ys h
    | _ => exact False.elim h
  | _ =>
    cases s2 with
    | set _ => exact False.elim h
    | _ => simp only [herr, hatom, hkey, hseq, hfn]

private theorem lift₂_set_sound {K A : Type} [HasNatAtom A] {β : Sort _}
    {g : RawVal K A → RawVal K A → β} {fallback : β}
    (hset : ∀ xs1 xs2 ys1 ys2, ValEq (.set xs1) (.set xs2) → ValEq (.set ys1) (.set ys2) →
      g (.set xs1) (.set ys1) = g (.set xs2) (.set ys2))
    (h1err : ∀ r, g .err r = fallback := by intro _; rfl)
    (h1atom : ∀ a r, g (.atom a) r = fallback := by intro _ _; rfl)
    (h1key : ∀ k r, g (.key k) r = fallback := by intro _ _; rfl)
    (h1seq : ∀ xs r, g (.seq xs) r = fallback := by intro _ _; rfl)
    (h1fn : ∀ ps r, g (.fn ps) r = fallback := by intro _ _; rfl)
    (h2err : ∀ xs, g (.set xs) .err = fallback := by intro _; rfl)
    (h2atom : ∀ xs a, g (.set xs) (.atom a) = fallback := by intro _ _; rfl)
    (h2key : ∀ xs k, g (.set xs) (.key k) = fallback := by intro _ _; rfl)
    (h2seq : ∀ xs ys, g (.set xs) (.seq ys) = fallback := by intro _ _; rfl)
    (h2fn : ∀ xs ps, g (.set xs) (.fn ps) = fallback := by intro _ _; rfl)
    (s1 r1 s2 r2 : RawVal K A) (hs : ValEq s1 s2) (hr : ValEq r1 r2) : g s1 r1 = g s2 r2 := by
  cases s1 with
  | set xs1 =>
    cases s2 with
    | set xs2 =>
      cases r1 with
      | set ys1 =>
        cases r2 with
        | set ys2 => exact hset xs1 xs2 ys1 ys2 hs hr
        | _ => exact False.elim hr
      | _ =>
        cases r2 with
        | set _ => exact False.elim hr
        | _ => simp only [h2err, h2atom, h2key, h2seq, h2fn]
    | _ => exact False.elim hs
  | _ =>
    cases s2 with
    | set _ => exact False.elim hs
    | _ => simp only [h1err, h1atom, h1key, h1seq, h1fn]

def valSetoid (K A : Type) [HasNatAtom A] : Setoid (RawVal K A) where
  r := ValEq
  iseqv := ⟨ValEq.refl, ValEq.symm, ValEq.trans⟩

abbrev Val {d : Nat} (sizes : Fin d → Nat) (A : Type) [HasNatAtom A] := Quotient (valSetoid (Key sizes) A)

def mkVal {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (x : RawVal (Key sizes) A) : Val sizes A :=
  Quotient.mk (valSetoid (Key sizes) A) x

def renameVal {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) :
    Val sizes A → Val sizes A :=
  Quotient.lift (fun x => mkVal (renameRaw p x)) (fun x y h =>
    Quotient.sound ((ValEq.rename p x y).mpr h))

theorem renameVal_mk {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (x : RawVal (Key sizes) A) :
    renameVal p (mkVal x) = mkVal (renameRaw p x) := rfl

theorem renameVal_identity {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (v : Val sizes A) :
    renameVal GroupPerm.identity v = v := by
  induction v using Quotient.ind with
  | _ x => exact congrArg mkVal (renameRaw_identity x)

theorem renameVal_then {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p q : GroupPerm sizes)
    (v : Val sizes A) :
    renameVal (p.then q) v = renameVal q (renameVal p v) := by
  induction v using Quotient.ind with
  | _ x => exact congrArg mkVal (renameRaw_then p q x)

theorem renameVal_inverse {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (v : Val sizes A) :
    renameVal p.inverse (renameVal p v) = v := by
  induction v using Quotient.ind with
  | _ x => exact congrArg mkVal (renameRaw_inverse p x)

theorem renameVal_right {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (v : Val sizes A) :
    renameVal p (renameVal p.inverse v) = v := by
  have h := renameVal_inverse p.inverse v
  have hp : p.inverse.inverse = p := by funext g; rfl
  rw [hp] at h
  exact h

theorem renameVal_injective {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    {u v : Val sizes A} :
    renameVal p u = renameVal p v ↔ u = v := by
  constructor
  · intro h
    have := congrArg (renameVal p.inverse) h
    simpa only [renameVal_inverse] using this
  · intro h; exact congrArg (renameVal p) h

def valOut {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (v : Val sizes A) : RawVal (Key sizes) A :=
  Classical.choose (Quotient.exists_rep v)

theorem valOut_eq {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (v : Val sizes A) :
    mkVal (valOut v) = v :=
  Classical.choose_spec (Quotient.exists_rep v)

private theorem valEq_out_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (v : Val sizes A) :
    ValEq (renameRaw p (valOut v)) (valOut (renameVal p v)) :=
  @Quotient.exact _ (valSetoid (Key sizes) A) _ _ (by
    change mkVal (renameRaw p (valOut v)) = mkVal (valOut (renameVal p v))
    rw [← renameVal_mk, valOut_eq, valOut_eq])

private theorem nodup_length_eq {α : Type} [DecidableEq α] :
    ∀ {l1 l2 : List α}, l1.Nodup → l2.Nodup → (∀ x, x ∈ l1 ↔ x ∈ l2) → l1.length = l2.length
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, heq => absurd ((heq b).mpr List.mem_cons_self) List.not_mem_nil
  | a :: t, l2, h1, h2, heq => by
    have ha_not_t : a ∉ t := (List.nodup_cons.mp h1).1
    have ht_nd : t.Nodup := (List.nodup_cons.mp h1).2
    have ha_l2 : a ∈ l2 := (heq a).mp List.mem_cons_self
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

def dedupList {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: t => if a ∈ t then dedupList t else a :: dedupList t

theorem mem_dedupList {α : Type} [DecidableEq α] {l : List α} {x : α} :
    x ∈ dedupList l ↔ x ∈ l := by
  induction l with
  | nil => exact Iff.rfl
  | cons a t ih =>
    simp only [dedupList]
    split
    · case isTrue h =>
      rw [ih]
      constructor
      · intro hx; exact List.mem_cons_of_mem a hx
      · intro hx; rcases List.mem_cons.mp hx with rfl | ht
        · exact h
        · exact ht
    · case isFalse _ =>
      simp only [List.mem_cons, ih]

theorem nodup_dedupList {α : Type} [DecidableEq α] (l : List α) : (dedupList l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    simp only [dedupList]
    split
    · exact ih
    · case isFalse h =>
      rw [List.nodup_cons]
      exact ⟨fun hm => h (mem_dedupList.mp hm), ih⟩

-- Lifted constructors on Val
def Val.err {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] : Val sizes A := mkVal .err
def Val.atom {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (a : A) : Val sizes A := mkVal (.atom a)
def Val.key {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (k : Key sizes) : Val sizes A := mkVal (.key k)
def Val.seq {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (xs : List (Val sizes A)) : Val sizes A :=
  mkVal (.seq (xs.map valOut))
def Val.set {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (xs : List (Val sizes A)) : Val sizes A :=
  mkVal (.set (xs.map valOut))
def Val.fn {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (ps : List (Val sizes A × Val sizes A)) : Val sizes A :=
  mkVal (.fn (ps.map (fun kv => (valOut kv.1, valOut kv.2))))

theorem Val.rename_err {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) :
    renameVal p (Val.err (A := A)) = Val.err := rfl

theorem Val.rename_atom {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) (a : A) :
    renameVal p (Val.atom a) = Val.atom a := rfl

theorem Val.rename_key {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) (k : Key sizes) :
    renameVal p (Val.key (A := A) k) = Val.key (p.toFun k) := rfl

theorem Val.rename_seq {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (xs : List (Val sizes A)) :
    renameVal p (Val.seq xs) = Val.seq (xs.map (renameVal p)) := by
  apply Quotient.sound
  change ValEq (renameRaw p (.seq (xs.map valOut))) (.seq ((xs.map (renameVal p)).map valOut))
  rw [ValEq.fnPairs_iff (rawFnPairs_rename p (.seq (xs.map valOut))) rfl]
  simp only [seqPairs, renameRawPairs_eq_map]
  constructor
  · intro kv hkv
    rcases List.mem_map.mp hkv with ⟨r, hr, rfl⟩
    rcases (mem_seqPairsAux HasNatAtom.natAtom 1 (xs.map valOut) r).mp hr with ⟨j, hj, rfl⟩
    have hj' : j < xs.length := by simpa only [List.length_map] using hj
    refine ⟨(.atom (HasNatAtom.natAtom (1 + j)), valOut (renameVal p xs[j])), ?_, ValEq.refl _, ?_⟩
    · rw [mem_seqPairsAux]
      refine ⟨j, by simpa only [List.length_map] using hj', ?_⟩
      simp only [List.getElem_map]
    · simp only [List.getElem_map]
      exact valEq_out_rename p xs[j]
  · intro q hq
    rcases (mem_seqPairsAux HasNatAtom.natAtom 1 ((xs.map (renameVal p)).map valOut) q).mp hq with ⟨j, hj, rfl⟩
    have hj' : j < xs.length := by simpa only [List.length_map] using hj
    refine ⟨(renameRaw p (.atom (HasNatAtom.natAtom (1 + j))), renameRaw p (valOut xs[j])), ?_, ValEq.refl _, ?_⟩
    · refine List.mem_map.mpr ⟨(.atom (HasNatAtom.natAtom (1 + j)), valOut xs[j]), ?_, rfl⟩
      rw [mem_seqPairsAux]
      refine ⟨j, by simpa only [List.length_map] using hj', ?_⟩
      simp only [List.getElem_map]
    · simp only [List.getElem_map]
      exact valEq_out_rename p xs[j]

theorem Val.rename_set {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (xs : List (Val sizes A)) :
    renameVal p (Val.set xs) = Val.set (xs.map (renameVal p)) := by
  apply Quotient.sound
  change ValEq (renameRaw p (.set (xs.map valOut))) (.set ((xs.map (renameVal p)).map valOut))
  simp only [renameRaw, renameRawList_eq_map, ValEq.set_iff]
  constructor
  · intro x hx
    rcases List.mem_map.mp hx with ⟨r, hr, rfl⟩
    rcases List.mem_map.mp hr with ⟨v, hv, rfl⟩
    exact ⟨valOut (renameVal p v),
      List.mem_map_of_mem (List.mem_map_of_mem hv), valEq_out_rename p v⟩
  · intro y hy
    rcases List.mem_map.mp hy with ⟨v', hv', rfl⟩
    rcases List.mem_map.mp hv' with ⟨v, hv, rfl⟩
    exact ⟨renameRaw p (valOut v),
      List.mem_map_of_mem (List.mem_map_of_mem hv), valEq_out_rename p v⟩

theorem Val.rename_fn {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (ps : List (Val sizes A × Val sizes A)) :
    renameVal p (Val.fn ps) = Val.fn (ps.map (fun kv => (renameVal p kv.1, renameVal p kv.2))) := by
  apply Quotient.sound
  change ValEq (renameRaw p (.fn (ps.map (fun kv => (valOut kv.1, valOut kv.2)))))
    (.fn ((ps.map (fun kv => (renameVal p kv.1, renameVal p kv.2))).map (fun kv => (valOut kv.1, valOut kv.2))))
  simp only [renameRaw, renameRawPairs_eq_map, ValEq.fn_iff]
  constructor
  · intro kv hkv
    rcases List.mem_map.mp hkv with ⟨r, hr, rfl⟩
    rcases List.mem_map.mp hr with ⟨w, hw, rfl⟩
    exact ⟨(valOut (renameVal p w.1), valOut (renameVal p w.2)),
      List.mem_map.mpr ⟨(renameVal p w.1, renameVal p w.2), List.mem_map_of_mem hw, rfl⟩,
      valEq_out_rename p w.1, valEq_out_rename p w.2⟩
  · intro q hq
    rcases List.mem_map.mp hq with ⟨w', hw', rfl⟩
    rcases List.mem_map.mp hw' with ⟨w, hw, rfl⟩
    exact ⟨(renameRaw p (valOut w.1), renameRaw p (valOut w.2)),
      List.mem_map.mpr ⟨(valOut w.1, valOut w.2), List.mem_map_of_mem hw, rfl⟩,
      valEq_out_rename p w.1, valEq_out_rename p w.2⟩

def valSeqPairsAux {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] :
    Nat → List (Val sizes A) → List (Val sizes A × Val sizes A)
  | _, [] => []
  | i, v :: vs => (Val.atom (HasNatAtom.natAtom i), v) :: valSeqPairsAux (i + 1) vs

def valSeqPairs {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (xs : List (Val sizes A)) : List (Val sizes A × Val sizes A) :=
  valSeqPairsAux 1 xs

private theorem mem_valSeqPairsAux {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] :
    ∀ (base : Nat) (xs : List (Val sizes A)) (kv : Val sizes A × Val sizes A),
      kv ∈ valSeqPairsAux base xs ↔
        ∃ (j : Nat) (hj : j < xs.length), kv = (Val.atom (HasNatAtom.natAtom (base + j)), xs[j])
  | _, [], _ => Iff.intro (fun h => nomatch h) (fun ⟨_, hj, _⟩ => nomatch hj)
  | base, x :: xs, kv => by
    simp only [valSeqPairsAux, List.mem_cons, mem_valSeqPairsAux (base + 1) xs]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨0, Nat.zero_lt_succ _, rfl⟩
      · refine ⟨j + 1, Nat.succ_lt_succ hj, ?_⟩
        simp only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 j]
    · rintro ⟨j, hj, rfl⟩
      cases j with
      | zero => left; rfl
      | succ j' =>
        right
        refine ⟨j', Nat.lt_of_succ_lt_succ hj, ?_⟩
        simp only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 j']

theorem Val.seq_eq_fn {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (xs : List (Val sizes A)) :
    Val.seq xs = Val.fn (valSeqPairs xs) := by
  apply Quotient.sound
  change ValEq (.seq (xs.map valOut)) (.fn ((valSeqPairs xs).map (fun kv => (valOut kv.1, valOut kv.2))))
  rw [ValEq.fnPairs_iff (x := .seq (xs.map valOut)) (y := .fn _) rfl rfl]
  simp only [seqPairs]
  constructor
  · intro kv hkv
    rcases (mem_seqPairsAux HasNatAtom.natAtom 1 (xs.map valOut) kv).mp hkv with ⟨j, hj, rfl⟩
    have hj' : j < xs.length := by simpa only [List.length_map] using hj
    refine ⟨(valOut (Val.atom (HasNatAtom.natAtom (1 + j))), valOut xs[j]), ?_, ?_, ?_⟩
    · refine List.mem_map.mpr ⟨(Val.atom (HasNatAtom.natAtom (1 + j)), xs[j]), ?_, rfl⟩
      exact (mem_valSeqPairsAux 1 xs _).mpr ⟨j, hj', rfl⟩
    · exact @Quotient.exact _ (valSetoid (Key sizes) A) _ _ (valOut_eq (Val.atom (HasNatAtom.natAtom (1 + j)))).symm
    · simp only [List.getElem_map]; exact ValEq.refl _
  · intro q hq
    rcases List.mem_map.mp hq with ⟨kv, hkv, rfl⟩
    rcases (mem_valSeqPairsAux 1 xs kv).mp hkv with ⟨j, hj, rfl⟩
    refine ⟨(.atom (HasNatAtom.natAtom (1 + j)), valOut xs[j]), ?_, ?_, ValEq.refl _⟩
    · rw [mem_seqPairsAux]
      exact ⟨j, by simpa only [List.length_map] using hj, by simp only [List.getElem_map]⟩
    · exact @Quotient.exact _ (valSetoid (Key sizes) A) _ _ (valOut_eq (Val.atom (HasNatAtom.natAtom (1 + j)))).symm

theorem Val.seq_singleton_eq_fn {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (v : Val sizes A) :
    Val.seq [v] = Val.fn [(Val.atom (HasNatAtom.natAtom 1), v)] :=
  Val.seq_eq_fn [v]

theorem Val.atom_inj {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] {a b : A}
    (h : Val.atom (sizes := sizes) a = Val.atom b) : a = b :=
  @Quotient.exact _ (valSetoid (Key sizes) A) (.atom a) (.atom b) h

theorem Val.seq_inj {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    {xs ys : List (Val sizes A)} (h : Val.seq xs = Val.seq ys) : xs = ys := by
  have heq : ValEq (.seq (xs.map valOut)) (.seq (ys.map valOut)) := Quotient.exact h
  rcases (ValEq.fnPairs_iff (x := .seq (xs.map valOut)) (y := .seq (ys.map valOut)) rfl rfl).mp heq with ⟨h1, h2⟩
  have hle1 : xs.length ≤ ys.length := by
    by_cases hx : xs.length = 0
    · omega
    · have hmem : (.atom (HasNatAtom.natAtom (1 + (xs.length - 1))), valOut xs[xs.length - 1]) ∈
          seqPairs (xs.map valOut) := by
        rw [seqPairs, mem_seqPairsAux]
        exact ⟨xs.length - 1, by rw [List.length_map]; omega, by simp only [List.getElem_map]⟩
      rcases h1 _ hmem with ⟨q, hq, hk, _⟩
      rcases (mem_seqPairsAux HasNatAtom.natAtom 1 (ys.map valOut) q).mp hq with ⟨j, hj, rfl⟩
      have hna : HasNatAtom.natAtom (1 + (xs.length - 1)) = HasNatAtom.natAtom (1 + j) :=
        Val.atom_inj (sizes := sizes) (Quotient.sound hk)
      have hij : 1 + (xs.length - 1) = 1 + j := HasNatAtom.natAtom_inj _ _ hna
      have hj' : j < ys.length := by simpa only [List.length_map] using hj
      omega
  have hle2 : ys.length ≤ xs.length := by
    by_cases hy : ys.length = 0
    · omega
    · have hmem : (.atom (HasNatAtom.natAtom (1 + (ys.length - 1))), valOut ys[ys.length - 1]) ∈
          seqPairs (ys.map valOut) := by
        rw [seqPairs, mem_seqPairsAux]
        exact ⟨ys.length - 1, by rw [List.length_map]; omega, by simp only [List.getElem_map]⟩
      rcases h2 _ hmem with ⟨kv, hkv, hk, _⟩
      rcases (mem_seqPairsAux HasNatAtom.natAtom 1 (xs.map valOut) kv).mp hkv with ⟨i, hi, rfl⟩
      have hna : HasNatAtom.natAtom (1 + i) = HasNatAtom.natAtom (1 + (ys.length - 1)) :=
        Val.atom_inj (sizes := sizes) (Quotient.sound hk)
      have hij : 1 + i = 1 + (ys.length - 1) := HasNatAtom.natAtom_inj _ _ hna
      have hi' : i < xs.length := by simpa only [List.length_map] using hi
      omega
  apply List.ext_getElem (by omega)
  intro i h1i h2i
  have hmem : (.atom (HasNatAtom.natAtom (1 + i)), valOut xs[i]) ∈ seqPairs (xs.map valOut) := by
    rw [seqPairs, mem_seqPairsAux]
    exact ⟨i, by simpa only [List.length_map] using h1i, by simp only [List.getElem_map]⟩
  rcases h1 _ hmem with ⟨q, hq, hk, hv⟩
  rcases (mem_seqPairsAux HasNatAtom.natAtom 1 (ys.map valOut) q).mp hq with ⟨j, hj, rfl⟩
  have hna : HasNatAtom.natAtom (1 + i) = HasNatAtom.natAtom (1 + j) :=
    Val.atom_inj (sizes := sizes) (Quotient.sound hk)
  have hij : i = j := by have := HasNatAtom.natAtom_inj _ _ hna; omega
  subst hij
  simp only [List.getElem_map] at hv
  rw [← valOut_eq xs[i], ← valOut_eq ys[i]]
  exact Quotient.sound hv

theorem Val.set_eq_iff {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] {xs ys : List (Val sizes A)} :
    Val.set xs = Val.set ys ↔ (∀ v, v ∈ xs ↔ v ∈ ys) := by
  constructor
  · intro h v
    have heq : ValEq (.set (xs.map valOut)) (.set (ys.map valOut)) := Quotient.exact h
    rcases ValEq.set_iff.mp heq with ⟨h1, h2⟩
    constructor
    · intro hv
      rcases h1 (valOut v) (List.mem_map_of_mem hv) with ⟨r, hr, hvr⟩
      rcases List.mem_map.mp hr with ⟨w, hw, rfl⟩
      have hvw : v = w := by
        rw [← valOut_eq v, ← valOut_eq w]
        exact Quotient.sound hvr
      exact hvw ▸ hw
    · intro hv
      rcases h2 (valOut v) (List.mem_map_of_mem hv) with ⟨r, hr, hrv⟩
      rcases List.mem_map.mp hr with ⟨w, hw, rfl⟩
      have hwv : w = v := by
        rw [← valOut_eq w, ← valOut_eq v]
        exact Quotient.sound hrv
      exact hwv ▸ hw
  · intro h
    apply Quotient.sound
    change ValEq (.set (xs.map valOut)) (.set (ys.map valOut))
    rw [ValEq.set_iff]
    constructor
    · intro x hx
      rcases List.mem_map.mp hx with ⟨v, hv, rfl⟩
      exact ⟨valOut v, List.mem_map_of_mem ((h v).mp hv), ValEq.refl _⟩
    · intro y hy
      rcases List.mem_map.mp hy with ⟨v, hv, rfl⟩
      exact ⟨valOut v, List.mem_map_of_mem ((h v).mpr hv), ValEq.refl _⟩

theorem Val.fn_eq_iff {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    {ps qs : List (Val sizes A × Val sizes A)} :
    Val.fn ps = Val.fn qs ↔ (∀ kv, kv ∈ ps ↔ kv ∈ qs) := by
  constructor
  · intro h kv
    have heq : ValEq (.fn (ps.map (fun kv => (valOut kv.1, valOut kv.2))))
        (.fn (qs.map (fun kv => (valOut kv.1, valOut kv.2)))) := Quotient.exact h
    rcases ValEq.fn_iff.mp heq with ⟨h1, h2⟩
    constructor
    · intro hkv
      rcases h1 (valOut kv.1, valOut kv.2) (List.mem_map_of_mem hkv) with ⟨r, hr, h1e, h2e⟩
      rcases List.mem_map.mp hr with ⟨w, hw, rfl⟩
      have hw1 : kv.1 = w.1 := by rw [← valOut_eq kv.1, ← valOut_eq w.1]; exact Quotient.sound h1e
      have hw2 : kv.2 = w.2 := by rw [← valOut_eq kv.2, ← valOut_eq w.2]; exact Quotient.sound h2e
      have : kv = w := Prod.ext hw1 hw2
      exact this ▸ hw
    · intro hkv
      rcases h2 (valOut kv.1, valOut kv.2) (List.mem_map_of_mem hkv) with ⟨r, hr, h1e, h2e⟩
      rcases List.mem_map.mp hr with ⟨w, hw, rfl⟩
      have hw1 : w.1 = kv.1 := by rw [← valOut_eq w.1, ← valOut_eq kv.1]; exact Quotient.sound h1e
      have hw2 : w.2 = kv.2 := by rw [← valOut_eq w.2, ← valOut_eq kv.2]; exact Quotient.sound h2e
      have : w = kv := Prod.ext hw1 hw2
      exact this ▸ hw
  · intro h
    apply Quotient.sound
    change ValEq (.fn (ps.map (fun kv => (valOut kv.1, valOut kv.2))))
      (.fn (qs.map (fun kv => (valOut kv.1, valOut kv.2))))
    rw [ValEq.fn_iff]
    constructor
    · intro r hr
      rcases List.mem_map.mp hr with ⟨kv, hkv, rfl⟩
      exact ⟨(valOut kv.1, valOut kv.2), List.mem_map_of_mem ((h kv).mp hkv), ValEq.refl _, ValEq.refl _⟩
    · intro r hr
      rcases List.mem_map.mp hr with ⟨kv, hkv, rfl⟩
      exact ⟨(valOut kv.1, valOut kv.2), List.mem_map_of_mem ((h kv).mpr hkv), ValEq.refl _, ValEq.refl _⟩

-- Predicates and destructors on Val
def Val.asAtom {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] : Val sizes A → Option A :=
  Quotient.lift (fun x => match x with | .atom a => some a | _ => none) (by
    intro x y h
    cases x with
    | atom _ =>
      cases y with
      | atom _ => exact congrArg some h
      | _ => exact False.elim h
    | _ =>
      cases y with
      | atom _ => exact False.elim h
      | _ => rfl)

theorem Val.asAtom_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) (v : Val sizes A) :
    Val.asAtom (renameVal p v) = Val.asAtom v := by
  induction v using Quotient.ind with
  | _ x => cases x <;> rfl

def Val.isSet {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] : Val sizes A → Prop :=
  Quotient.lift (fun x => match x with | .set _ => True | _ => False)
    (lift_set_sound (fallback := False) (fun _ _ _ => rfl))

theorem Val.isSet_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) (v : Val sizes A) :
    Val.isSet (renameVal p v) ↔ Val.isSet v := by
  induction v using Quotient.ind with
  | _ x => cases x <;> rfl

def Val.isFn {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] : Val sizes A → Prop :=
  Quotient.lift (fun x => (rawFnPairs x).isSome = true) (by
    intro x y h
    exact congrArg (· = true) (ValEq.rawFnPairs_some h))

theorem Val.isFn_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) (v : Val sizes A) :
    Val.isFn (renameVal p v) ↔ Val.isFn v := by
  induction v using Quotient.ind with
  | _ x =>
    change ((rawFnPairs (renameRaw p x)).isSome = true) ↔ ((rawFnPairs x).isSome = true)
    rw [rawFnPairs_rename]
    cases rawFnPairs x <;> rfl

def Val.isFinite {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (v : Val sizes A) : Prop :=
  Val.isSet v ∨ Val.isFn v

theorem Val.isFinite_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (v : Val sizes A) :
    Val.isFinite (renameVal p v) ↔ Val.isFinite v :=
  or_congr (Val.isSet_rename p v) (Val.isFn_rename p v)

theorem Val.isFinite_seq {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (xs : List (Val sizes A)) :
    Val.isFinite (Val.seq xs) :=
  Or.inr rfl

def Val.seqElems {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (v : Val sizes A) :
    Option (List (Val sizes A)) := by
  classical
  exact if h : ∃ xs : List (Val sizes A), v = Val.seq xs then some (Classical.choose h) else none

theorem Val.seqElems_seq {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (xs : List (Val sizes A)) :
    Val.seqElems (Val.seq xs) = some xs := by
  classical
  unfold Val.seqElems
  have h : ∃ ys : List (Val sizes A), Val.seq xs = Val.seq ys := ⟨xs, rfl⟩
  simp only [h, ↓reduceDIte]
  congr 1
  exact (Val.seq_inj (Classical.choose_spec h)).symm

theorem Val.seqElems_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (v : Val sizes A) :
    Val.seqElems (renameVal p v) = (Val.seqElems v).map (List.map (renameVal p)) := by
  classical
  unfold Val.seqElems
  by_cases h : ∃ xs : List (Val sizes A), v = Val.seq xs
  · rcases h with ⟨xs0, rfl⟩
    have h' : ∃ xs : List (Val sizes A), renameVal p (Val.seq xs0) = Val.seq xs :=
      ⟨xs0.map (renameVal p), Val.rename_seq p xs0⟩
    simp only [h', ↓reduceDIte]
    have h0 : ∃ xs : List (Val sizes A), Val.seq xs0 = Val.seq xs := ⟨xs0, rfl⟩
    simp only [h0, ↓reduceDIte, Option.map_some]
    congr 1
    have hc1 : Classical.choose h0 = xs0 := (Val.seq_inj (Classical.choose_spec h0)).symm
    have hc2 : Val.seq (xs0.map (renameVal p)) = Val.seq (Classical.choose h') :=
      (Val.rename_seq p xs0).symm.trans (Classical.choose_spec h')
    rw [hc1]
    exact (Val.seq_inj hc2).symm
  · have h' : ¬ ∃ xs : List (Val sizes A), renameVal p v = Val.seq xs := by
      rintro ⟨xs, hxs⟩
      apply h
      refine ⟨xs.map (renameVal p.inverse), ?_⟩
      have := congrArg (renameVal p.inverse) hxs
      rwa [renameVal_inverse, Val.rename_seq] at this
    simp only [h, h', ↓reduceDIte, Option.map_none]

def Val.mem {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (x : Val sizes A) : Val sizes A → Prop :=
  Quotient.lift (fun s => match s with | .set xs => ∃ y ∈ xs, mkVal y = x | _ => False)
    (lift_set_sound (fallback := False) (by
      intro xs ys h
      apply propext
      rcases ValEq.set_iff.mp h with ⟨h1, h2⟩
      constructor
      · rintro ⟨a, ha, rfl⟩
        rcases h1 a ha with ⟨b, hb, hab⟩
        exact ⟨b, hb, (Quotient.sound hab).symm⟩
      · rintro ⟨b, hb, rfl⟩
        rcases h2 b hb with ⟨a, ha, hab⟩
        exact ⟨a, ha, Quotient.sound hab⟩))

theorem Val.mem_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (x s : Val sizes A) :
    Val.mem (renameVal p x) (renameVal p s) ↔ Val.mem x s := by
  induction s using Quotient.ind with
  | _ sr =>
    cases sr with
    | set xs =>
      change (∃ y ∈ renameRawList p xs, mkVal y = renameVal p x) ↔ (∃ y ∈ xs, mkVal y = x)
      simp only [renameRawList_eq_map]
      constructor
      · rintro ⟨y', hy', heq⟩
        rcases List.mem_map.mp hy' with ⟨y, hy, rfl⟩
        exact ⟨y, hy, (renameVal_injective p).mp heq⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨renameRaw p y, List.mem_map_of_mem hy, rfl⟩
    | _ => rfl

def Val.mapsTo {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (f k v : Val sizes A) : Prop :=
  Quotient.liftOn f (fun fr => match rawFnPairs fr with | some ps => ∃ kv ∈ ps, mkVal kv.1 = k ∧ mkVal kv.2 = v | none => False) (by
    intro f1 f2 h
    have hs := ValEq.rawFnPairs_some h
    cases hf1 : rawFnPairs f1 <;> cases hf2 : rawFnPairs f2
    · rfl
    · rw [hf1, hf2] at hs; cases hs
    · rw [hf1, hf2] at hs; cases hs
    · case some.some ps qs =>
      apply propext
      rcases (ValEq.fnPairs_iff hf1 hf2).mp h with ⟨h1, h2⟩
      constructor
      · rintro ⟨a, ha, rfl, rfl⟩
        rcases h1 a ha with ⟨b, hb, h1e, h2e⟩
        exact ⟨b, hb, (Quotient.sound h1e).symm, (Quotient.sound h2e).symm⟩
      · rintro ⟨b, hb, rfl, rfl⟩
        rcases h2 b hb with ⟨a, ha, h1e, h2e⟩
        exact ⟨a, ha, Quotient.sound h1e, Quotient.sound h2e⟩)

theorem Val.mapsTo_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (f k v : Val sizes A) :
    Val.mapsTo (renameVal p f) (renameVal p k) (renameVal p v) ↔ Val.mapsTo f k v := by
  induction f using Quotient.ind with
  | _ fr =>
    change (match rawFnPairs (renameRaw p fr) with | some ps => ∃ kv ∈ ps, mkVal kv.1 = renameVal p k ∧ mkVal kv.2 = renameVal p v | none => False) ↔
      (match rawFnPairs fr with | some ps => ∃ kv ∈ ps, mkVal kv.1 = k ∧ mkVal kv.2 = v | none => False)
    rw [rawFnPairs_rename]
    cases rawFnPairs fr with
    | none => rfl
    | some ps =>
      simp only [Option.map_some, renameRawPairs_eq_map]
      constructor
      · rintro ⟨kv', hkv', h1, h2⟩
        rcases List.mem_map.mp hkv' with ⟨kv, hkv, rfl⟩
        exact ⟨kv, hkv, (renameVal_injective p).mp h1, (renameVal_injective p).mp h2⟩
      · rintro ⟨kv, hkv, rfl, rfl⟩
        exact ⟨(renameRaw p kv.1, renameRaw p kv.2), List.mem_map_of_mem hkv, rfl, rfl⟩

def Val.isSingleValuedFn {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (v : Val sizes A) : Prop :=
  Val.isFn v ∧ ∀ k w1 w2, Val.mapsTo v k w1 → Val.mapsTo v k w2 → w1 = w2

theorem Val.isSingleValuedFn_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (v : Val sizes A) :
    Val.isSingleValuedFn (renameVal p v) ↔ Val.isSingleValuedFn v := by
  unfold Val.isSingleValuedFn
  apply and_congr (Val.isFn_rename p v)
  constructor
  · intro h k w1 w2 h1 h2
    have hp1 := (Val.mapsTo_rename p v k w1).mpr h1
    have hp2 := (Val.mapsTo_rename p v k w2).mpr h2
    exact (renameVal_injective p).mp (h (renameVal p k) (renameVal p w1) (renameVal p w2) hp1 hp2)
  · intro h k w1 w2 h1 h2
    have hm1 : Val.mapsTo v (renameVal p.inverse k) (renameVal p.inverse w1) := by
      have := (Val.mapsTo_rename p v (renameVal p.inverse k) (renameVal p.inverse w1)).mp
      rw [renameVal_right, renameVal_right] at this
      exact this h1
    have hm2 : Val.mapsTo v (renameVal p.inverse k) (renameVal p.inverse w2) := by
      have := (Val.mapsTo_rename p v (renameVal p.inverse k) (renameVal p.inverse w2)).mp
      rw [renameVal_right, renameVal_right] at this
      exact this h2
    have heq := h _ _ _ hm1 hm2
    rw [← renameVal_right p w1, ← renameVal_right p w2, heq]

-- Unique functional lookup
def Val.fnLookup {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (f k : Val sizes A) : Option (Val sizes A) := by
  classical
  exact if h : ∃ v, Val.mapsTo f k v ∧ ∀ w, Val.mapsTo f k w → w = v then some (Classical.choose h) else none

theorem Val.fnLookup_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (f k : Val sizes A) :
    Val.fnLookup (renameVal p f) (renameVal p k) = (Val.fnLookup f k).map (renameVal p) := by
  classical
  unfold Val.fnLookup
  by_cases h : ∃ v, Val.mapsTo f k v ∧ ∀ w, Val.mapsTo f k w → w = v
  · have h' : ∃ v, Val.mapsTo (renameVal p f) (renameVal p k) v ∧
        ∀ w, Val.mapsTo (renameVal p f) (renameVal p k) w → w = v := by
      rcases h with ⟨v0, hm, hu⟩
      refine ⟨renameVal p v0, (Val.mapsTo_rename p f k v0).mpr hm, fun w hw => ?_⟩
      have hw' : Val.mapsTo f k (renameVal p.inverse w) := by
        have := (Val.mapsTo_rename p f k (renameVal p.inverse w)).mp
        rw [renameVal_right] at this
        exact this hw
      have heq := hu _ hw'
      rw [← renameVal_right p w, heq]
    simp only [h, h', ↓reduceDIte, Option.map_some]
    congr 1
    have hc1 := Classical.choose_spec h
    have hc2 := Classical.choose_spec h'
    have hinv : Val.mapsTo f k (renameVal p.inverse (Classical.choose h')) := by
      have := (Val.mapsTo_rename p f k (renameVal p.inverse (Classical.choose h'))).mp
      rw [renameVal_right] at this
      exact this hc2.1
    have heq := hc1.2 _ hinv
    rw [← renameVal_right p (Classical.choose h'), heq]
  · have h' : ¬ ∃ v, Val.mapsTo (renameVal p f) (renameVal p k) v ∧
        ∀ w, Val.mapsTo (renameVal p f) (renameVal p k) w → w = v := by
      rintro ⟨v0, hm, hu⟩
      apply h
      refine ⟨renameVal p.inverse v0, ?_, fun w hw => ?_⟩
      · have := (Val.mapsTo_rename p f k (renameVal p.inverse v0)).mp
        rw [renameVal_right] at this
        exact this hm
      · have hw' : Val.mapsTo (renameVal p f) (renameVal p k) (renameVal p w) :=
          (Val.mapsTo_rename p f k w).mpr hw
        have heq := hu _ hw'
        rw [← renameVal_inverse p w, heq]
    simp only [h, h', ↓reduceDIte, Option.map_none]

def Val.apply {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (f k : Val sizes A) : Val sizes A :=
  (Val.fnLookup f k).getD Val.err

theorem Val.apply_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (f k : Val sizes A) :
    Val.apply (renameVal p f) (renameVal p k) = renameVal p (Val.apply f k) := by
  unfold Val.apply
  rw [Val.fnLookup_rename]
  cases Val.fnLookup f k <;> rfl

def Val.domain {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] :
    Val sizes A → Val sizes A :=
  Quotient.lift (fun fr => match rawFnPairs fr with
    | some ps => Val.set (ps.map (fun kv => mkVal kv.1))
    | none => Val.err) (by
    intro f1 f2 h
    have hs := ValEq.rawFnPairs_some h
    cases hf1 : rawFnPairs f1 <;> cases hf2 : rawFnPairs f2
    · rfl
    · rw [hf1, hf2] at hs; cases hs
    · rw [hf1, hf2] at hs; cases hs
    · case some.some ps qs =>
      rw [Val.set_eq_iff]
      rcases (ValEq.fnPairs_iff hf1 hf2).mp h with ⟨h1, h2⟩
      intro v
      simp only [List.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        rcases h1 a ha with ⟨b, hb, h1e, _⟩
        exact ⟨b, hb, (Quotient.sound h1e).symm⟩
      · rintro ⟨b, hb, rfl⟩
        rcases h2 b hb with ⟨a, ha, h1e, _⟩
        exact ⟨a, ha, Quotient.sound h1e⟩)

theorem Val.domain_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (f : Val sizes A) :
    Val.domain (renameVal p f) = renameVal p (Val.domain f) := by
  induction f using Quotient.ind with
  | _ fr =>
    change (match rawFnPairs (renameRaw p fr) with | some ps => Val.set (ps.map (fun kv => mkVal kv.1)) | none => Val.err) =
      renameVal p (match rawFnPairs fr with | some ps => Val.set (ps.map (fun kv => mkVal kv.1)) | none => Val.err)
    rw [rawFnPairs_rename]
    cases rawFnPairs fr with
    | none => rfl
    | some ps =>
      simp only [Option.map_some]
      rw [Val.rename_set, renameRawPairs_eq_map, List.map_map, List.map_map]
      rfl

def Val.update {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (f k newV : Val sizes A) : Val sizes A := by
  classical
  exact Quotient.liftOn f (fun fr => match rawFnPairs fr with
    | some ps => Val.fn (ps.map (fun kv => (mkVal kv.1, if mkVal kv.1 = k then newV else mkVal kv.2)))
    | none => Val.err) (by
    intro f1 f2 h
    have hs := ValEq.rawFnPairs_some h
    cases hf1 : rawFnPairs f1 <;> cases hf2 : rawFnPairs f2
    · rfl
    · rw [hf1, hf2] at hs; cases hs
    · rw [hf1, hf2] at hs; cases hs
    · case some.some ps qs =>
      rw [Val.fn_eq_iff]
      rcases (ValEq.fnPairs_iff hf1 hf2).mp h with ⟨h1, h2⟩
      intro kv
      simp only [List.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        rcases h1 a ha with ⟨b, hb, h1e, h2e⟩
        have e1 : mkVal a.1 = mkVal b.1 := Quotient.sound h1e
        have e2 : mkVal a.2 = mkVal b.2 := Quotient.sound h2e
        exact ⟨b, hb, by rw [e1, e2]⟩
      · rintro ⟨b, hb, rfl⟩
        rcases h2 b hb with ⟨a, ha, h1e, h2e⟩
        have e1 : mkVal a.1 = mkVal b.1 := Quotient.sound h1e
        have e2 : mkVal a.2 = mkVal b.2 := Quotient.sound h2e
        exact ⟨a, ha, by rw [e1, e2]⟩)

theorem Val.update_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (f k newV : Val sizes A) :
    Val.update (renameVal p f) (renameVal p k) (renameVal p newV) =
      renameVal p (Val.update f k newV) := by
  classical
  induction f using Quotient.ind with
  | _ fr =>
    change (match rawFnPairs (renameRaw p fr) with
      | some ps => Val.fn (ps.map (fun kv => (mkVal kv.1, if mkVal kv.1 = renameVal p k then renameVal p newV else mkVal kv.2)))
      | none => Val.err) =
      renameVal p (match rawFnPairs fr with
      | some ps => Val.fn (ps.map (fun kv => (mkVal kv.1, if mkVal kv.1 = k then newV else mkVal kv.2)))
      | none => Val.err)
    rw [rawFnPairs_rename]
    cases rawFnPairs fr with
    | none => rfl
    | some ps =>
      simp only [Option.map_some]
      rw [Val.rename_fn, renameRawPairs_eq_map, List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro kv _
      change (renameVal p (mkVal kv.1),
          if renameVal p (mkVal kv.1) = renameVal p k then renameVal p newV else renameVal p (mkVal kv.2)) =
        (renameVal p (mkVal kv.1), renameVal p (if mkVal kv.1 = k then newV else mkVal kv.2))
      by_cases hk : mkVal kv.1 = k
      · simp only [hk, ↓reduceIte]
      · have hk' : renameVal p (mkVal kv.1) ≠ renameVal p k := fun h => hk ((renameVal_injective p).mp h)
        simp only [hk, hk', ↓reduceIte]

theorem Val.update_seq_oob {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (v w : Val sizes A) :
    Val.update (Val.seq [v]) (Val.atom (HasNatAtom.natAtom 2)) w = Val.seq [v] := by
  classical
  have hne : Val.atom (sizes := sizes) (HasNatAtom.natAtom (A := A) 1) ≠
      Val.atom (HasNatAtom.natAtom (A := A) 2) := by
    intro h
    have h12 : (1 : Nat) = 2 := HasNatAtom.natAtom_inj 1 2 (Val.atom_inj h)
    cases h12
  rw [Val.seq_singleton_eq_fn]
  change Val.fn [(mkVal (valOut (Val.atom (HasNatAtom.natAtom (A := A) 1))),
    if mkVal (valOut (Val.atom (HasNatAtom.natAtom (A := A) 1))) = Val.atom (HasNatAtom.natAtom (A := A) 2)
    then w else mkVal (valOut v))] =
    Val.fn [(Val.atom (HasNatAtom.natAtom (A := A) 1), v)]
  simp only [valOut_eq, hne, ↓reduceIte]

def Val.merge {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (f g : Val sizes A) : Val sizes A := by
  classical
  exact Quotient.liftOn₂ f g (fun fr gr => match rawFnPairs fr, rawFnPairs gr with
    | some ps, some qs =>
      Val.fn (ps.map (fun kv => (mkVal kv.1, mkVal kv.2)) ++
        (qs.filter (fun kv => !decide (∃ p ∈ ps, mkVal p.1 = mkVal kv.1))).map
          (fun kv => (mkVal kv.1, mkVal kv.2)))
    | _, _ => Val.err) (by
    intro f1 g1 f2 g2 hf hg
    have hfs := ValEq.rawFnPairs_some hf
    have hgs := ValEq.rawFnPairs_some hg
    cases hf1 : rawFnPairs f1 <;> cases hf2 : rawFnPairs f2
    · rfl
    · rw [hf1, hf2] at hfs; cases hfs
    · rw [hf1, hf2] at hfs; cases hfs
    · cases hg1 : rawFnPairs g1 <;> cases hg2 : rawFnPairs g2
      · rfl
      · rw [hg1, hg2] at hgs; cases hgs
      · rw [hg1, hg2] at hgs; cases hgs
      · case some.some.some.some ps1 ps2 qs1 qs2 =>
        rcases (ValEq.fnPairs_iff hf1 hf2).mp hf with ⟨hf1', hf2'⟩
        rcases (ValEq.fnPairs_iff hg1 hg2).mp hg with ⟨hg1', hg2'⟩
        have hdom : ∀ k, (∃ p ∈ ps1, mkVal p.1 = k) ↔ (∃ p ∈ ps2, mkVal p.1 = k) := by
          intro k
          constructor
          · rintro ⟨a, ha, rfl⟩
            rcases hf1' a ha with ⟨b, hb, h1e, _⟩
            exact ⟨b, hb, (Quotient.sound h1e).symm⟩
          · rintro ⟨b, hb, rfl⟩
            rcases hf2' b hb with ⟨a, ha, h1e, _⟩
            exact ⟨a, ha, Quotient.sound h1e⟩
        rw [Val.fn_eq_iff]
        intro kv
        simp only [List.mem_append, List.mem_map, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]
        constructor
        · rintro (⟨a, ha, rfl⟩ | ⟨a, ⟨ha, hna⟩, rfl⟩)
          · left
            rcases hf1' a ha with ⟨b, hb, h1e, h2e⟩
            exact ⟨b, hb, Prod.ext (Quotient.sound h1e).symm (Quotient.sound h2e).symm⟩
          · right
            rcases hg1' a ha with ⟨b, hb, h1e, h2e⟩
            have e1 : mkVal a.1 = mkVal b.1 := Quotient.sound h1e
            exact ⟨b, ⟨hb, fun h => hna ((hdom _).mpr (e1 ▸ h))⟩, Prod.ext e1.symm (Quotient.sound h2e).symm⟩
        · rintro (⟨b, hb, rfl⟩ | ⟨b, ⟨hb, hnb⟩, rfl⟩)
          · left
            rcases hf2' b hb with ⟨a, ha, h1e, h2e⟩
            exact ⟨a, ha, Prod.ext (Quotient.sound h1e) (Quotient.sound h2e)⟩
          · right
            rcases hg2' b hb with ⟨a, ha, h1e, h2e⟩
            have e1 : mkVal a.1 = mkVal b.1 := Quotient.sound h1e
            exact ⟨a, ⟨ha, fun h => hnb ((hdom _).mp (e1 ▸ h))⟩, Prod.ext e1 (Quotient.sound h2e)⟩)

theorem Val.merge_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (f g : Val sizes A) :
    Val.merge (renameVal p f) (renameVal p g) = renameVal p (Val.merge f g) := by
  classical
  induction f using Quotient.ind with
  | _ fr =>
    induction g using Quotient.ind with
    | _ gr =>
      change (match rawFnPairs (renameRaw p fr), rawFnPairs (renameRaw p gr) with
        | some ps, some qs =>
          Val.fn (ps.map (fun kv => (mkVal kv.1, mkVal kv.2)) ++
            (qs.filter (fun kv => !decide (∃ r ∈ ps, mkVal r.1 = mkVal kv.1))).map
              (fun kv => (mkVal kv.1, mkVal kv.2)))
        | _, _ => Val.err) =
        renameVal p (match rawFnPairs fr, rawFnPairs gr with
        | some ps, some qs =>
          Val.fn (ps.map (fun kv => (mkVal kv.1, mkVal kv.2)) ++
            (qs.filter (fun kv => !decide (∃ r ∈ ps, mkVal r.1 = mkVal kv.1))).map
              (fun kv => (mkVal kv.1, mkVal kv.2)))
        | _, _ => Val.err)
      rw [rawFnPairs_rename, rawFnPairs_rename]
      cases rawFnPairs fr with
      | none => rfl
      | some ps =>
        cases rawFnPairs gr with
        | none => rfl
        | some qs =>
          simp only [Option.map_some]
          rw [Val.rename_fn, Val.fn_eq_iff, renameRawPairs_eq_map, renameRawPairs_eq_map]
          intro kv
          simp only [List.mem_append, List.mem_map, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]
          constructor
          · rintro (⟨a, ⟨a0, ha0, rfl⟩, rfl⟩ | ⟨a, ⟨⟨a0, ha0, rfl⟩, hna⟩, rfl⟩)
            · exact ⟨(mkVal a0.1, mkVal a0.2), Or.inl ⟨a0, ha0, rfl⟩, rfl⟩
            · refine ⟨(mkVal a0.1, mkVal a0.2), Or.inr ⟨a0, ⟨ha0, ?_⟩, rfl⟩, rfl⟩
              rintro ⟨r, hr, heq⟩
              apply hna
              refine ⟨(renameRaw p r.1, renameRaw p r.2), ⟨r, hr, rfl⟩, ?_⟩
              exact congrArg (renameVal p) heq
          · rintro ⟨w, (⟨a0, ha0, rfl⟩ | ⟨a0, ⟨ha0, hna⟩, rfl⟩), rfl⟩
            · left
              exact ⟨(renameRaw p a0.1, renameRaw p a0.2), ⟨a0, ha0, rfl⟩, rfl⟩
            · right
              refine ⟨(renameRaw p a0.1, renameRaw p a0.2), ⟨⟨a0, ha0, rfl⟩, ?_⟩, rfl⟩
              rintro ⟨r', ⟨r, hr, rfl⟩, heq⟩
              exact hna ⟨r, hr, (renameVal_injective p).mp heq⟩

def Val.card {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] : Val sizes A → Option Nat := by
  classical
  exact Quotient.lift (fun s => match s with
    | .set xs => some (dedupList (xs.map mkVal)).length
    | _ => none)
    (lift_set_sound (fallback := none) (by
      intro xs ys h
      dsimp only
      congr 1
      apply nodup_length_eq (nodup_dedupList _) (nodup_dedupList _)
      intro v
      simp only [mem_dedupList, List.mem_map]
      rcases ValEq.set_iff.mp h with ⟨h1, h2⟩
      constructor
      · rintro ⟨a, ha, rfl⟩
        rcases h1 a ha with ⟨b, hb, hab⟩
        exact ⟨b, hb, (Quotient.sound hab).symm⟩
      · rintro ⟨b, hb, rfl⟩
        rcases h2 b hb with ⟨a, ha, hab⟩
        exact ⟨a, ha, Quotient.sound hab⟩))

theorem Val.card_seq_fn_singleton {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (v : Val sizes A) :
    Val.card (Val.set [Val.seq [v], Val.fn [(Val.atom (HasNatAtom.natAtom 1), v)]]) = some 1 := by
  classical
  rw [← Val.seq_singleton_eq_fn]
  change some (dedupList ((List.map valOut [Val.seq [v], Val.seq [v]]).map mkVal)).length = some 1
  simp only [List.map_cons, List.map_nil, valOut_eq, dedupList, List.mem_singleton, ↓reduceIte,
    List.not_mem_nil, List.length_singleton]

theorem Val.card_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) (s : Val sizes A) :
    Val.card (renameVal p s) = Val.card s := by
  classical
  induction s using Quotient.ind with
  | _ sr =>
    cases sr with
    | set xs =>
      change some (dedupList ((renameRawList p xs).map mkVal)).length = some (dedupList (xs.map mkVal)).length
      congr 1
      have hnd1 := nodup_dedupList ((renameRawList p xs).map mkVal)
      have hnd2 := nodup_map_inj (fun _ _ h => (renameVal_injective p).mp h) (nodup_dedupList (xs.map mkVal))
      have hlen := nodup_length_eq hnd1 hnd2 (fun w => by
        simp only [mem_dedupList, renameRawList_eq_map, List.mem_map]
        constructor
        · rintro ⟨y', ⟨y, hy, rfl⟩, rfl⟩
          exact ⟨mkVal y, ⟨y, hy, rfl⟩, rfl⟩
        · rintro ⟨v, ⟨y, hy, rfl⟩, rfl⟩
          exact ⟨renameRaw p y, ⟨y, hy, rfl⟩, rfl⟩)
      simpa only [List.length_map] using hlen
    | _ => rfl

def Val.cup {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (a b : Val sizes A) : Val sizes A :=
  Quotient.liftOn₂ a b (fun ar br => match ar, br with
    | .set xs, .set ys => Val.set (xs.map mkVal ++ ys.map mkVal)
    | _, _ => Val.err)
    (lift₂_set_sound (fallback := Val.err) (by
      intro xs1 xs2 ys1 ys2 ha hb
      rw [Val.set_eq_iff]
      rcases ValEq.set_iff.mp ha with ⟨ha1, ha2⟩
      rcases ValEq.set_iff.mp hb with ⟨hb1, hb2⟩
      intro v
      simp only [List.mem_append, List.mem_map]
      constructor
      · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
        · left; rcases ha1 x hx with ⟨x', hx', he⟩; exact ⟨x', hx', (Quotient.sound he).symm⟩
        · right; rcases hb1 y hy with ⟨y', hy', he⟩; exact ⟨y', hy', (Quotient.sound he).symm⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
        · left; rcases ha2 x hx with ⟨x', hx', he⟩; exact ⟨x', hx', Quotient.sound he⟩
        · right; rcases hb2 y hy with ⟨y', hy', he⟩; exact ⟨y', hy', Quotient.sound he⟩))

theorem Val.cup_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) (a b : Val sizes A) :
    Val.cup (renameVal p a) (renameVal p b) = renameVal p (Val.cup a b) := by
  induction a using Quotient.ind with
  | _ ar =>
    induction b using Quotient.ind with
    | _ br =>
      cases ar with
      | set xs =>
        cases br with
        | set ys =>
          change Val.set ((renameRawList p xs).map mkVal ++ (renameRawList p ys).map mkVal) =
            renameVal p (Val.set (xs.map mkVal ++ ys.map mkVal))
          rw [Val.rename_set, renameRawList_eq_map, renameRawList_eq_map, List.map_append, List.map_map, List.map_map, List.map_map, List.map_map]
          rfl
        | _ => rfl
      | _ => rfl

def Val.setFilter {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (s : Val sizes A)
    (pred : Val sizes A → Prop) : Val sizes A := by
  classical
  exact Quotient.liftOn s (fun sr => match sr with
    | .set xs => Val.set ((xs.map mkVal).filter (fun v => decide (pred v)))
    | _ => Val.err)
    (lift_set_sound (fallback := Val.err) (by
      intro xs ys h
      rw [Val.set_eq_iff]
      rcases ValEq.set_iff.mp h with ⟨h1, h2⟩
      intro v
      simp only [List.mem_filter, List.mem_map, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hp⟩
        rcases h1 a ha with ⟨b, hb, hab⟩
        exact ⟨⟨b, hb, (Quotient.sound hab).symm⟩, hp⟩
      · rintro ⟨⟨b, hb, rfl⟩, hp⟩
        rcases h2 b hb with ⟨a, ha, hab⟩
        exact ⟨⟨a, ha, Quotient.sound hab⟩, hp⟩))

theorem Val.setFilter_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (s : Val sizes A) (pred pred' : Val sizes A → Prop)
    (heq : ∀ v, pred' (renameVal p v) ↔ pred v) :
    Val.setFilter (renameVal p s) pred' = renameVal p (Val.setFilter s pred) := by
  classical
  induction s using Quotient.ind with
  | _ sr =>
    cases sr with
    | set xs =>
      change Val.set (((renameRawList p xs).map mkVal).filter (fun v => decide (pred' v))) =
        renameVal p (Val.set ((xs.map mkVal).filter (fun v => decide (pred v))))
      rw [Val.rename_set, Val.set_eq_iff, renameRawList_eq_map]
      intro v
      simp only [List.mem_filter, List.mem_map, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨y', ⟨y, hy, rfl⟩, rfl⟩, hp⟩
        exact ⟨mkVal y, ⟨⟨y, hy, rfl⟩, (heq (mkVal y)).mp hp⟩, rfl⟩
      · rintro ⟨w, ⟨⟨y, hy, rfl⟩, hp⟩, rfl⟩
        exact ⟨⟨renameRaw p y, ⟨y, hy, rfl⟩, rfl⟩, (heq (mkVal y)).mpr hp⟩
    | _ => rfl

def Val.cap {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (a b : Val sizes A) : Val sizes A := by
  classical
  exact if Val.isSet b then Val.setFilter a (fun v => Val.mem v b) else Val.err

theorem Val.cap_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) (a b : Val sizes A) :
    Val.cap (renameVal p a) (renameVal p b) = renameVal p (Val.cap a b) := by
  classical
  unfold Val.cap
  rw [propext (Val.isSet_rename p b)]
  split
  · exact Val.setFilter_rename p a _ _ (fun v => Val.mem_rename p v b)
  · rfl

def Val.setMinus {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (a b : Val sizes A) : Val sizes A := by
  classical
  exact if Val.isSet b then Val.setFilter a (fun v => ¬ Val.mem v b) else Val.err

theorem Val.setMinus_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) (a b : Val sizes A) :
    Val.setMinus (renameVal p a) (renameVal p b) = renameVal p (Val.setMinus a b) := by
  classical
  unfold Val.setMinus
  rw [propext (Val.isSet_rename p b)]
  split
  · exact Val.setFilter_rename p a _ _ (fun v => not_congr (Val.mem_rename p v b))
  · rfl

def Val.setMap {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (s : Val sizes A)
    (f : Val sizes A → Val sizes A) : Val sizes A :=
  Quotient.liftOn s (fun sr => match sr with
    | .set xs => Val.set ((xs.map mkVal).map f)
    | _ => Val.err)
    (lift_set_sound (fallback := Val.err) (by
      intro xs ys h
      rw [Val.set_eq_iff]
      rcases ValEq.set_iff.mp h with ⟨h1, h2⟩
      intro v
      simp only [List.mem_map]
      constructor
      · rintro ⟨w, ⟨a, ha, rfl⟩, rfl⟩
        rcases h1 a ha with ⟨b, hb, hab⟩
        exact ⟨mkVal b, ⟨b, hb, rfl⟩, congrArg f (Quotient.sound hab).symm⟩
      · rintro ⟨w, ⟨b, hb, rfl⟩, rfl⟩
        rcases h2 b hb with ⟨a, ha, hab⟩
        exact ⟨mkVal a, ⟨a, ha, rfl⟩, congrArg f (Quotient.sound hab)⟩))

theorem Val.setMap_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (s : Val sizes A) (f f' : Val sizes A → Val sizes A)
    (heq : ∀ v, f' (renameVal p v) = renameVal p (f v)) :
    Val.setMap (renameVal p s) f' = renameVal p (Val.setMap s f) := by
  induction s using Quotient.ind with
  | _ sr =>
    cases sr with
    | set xs =>
      change Val.set (((renameRawList p xs).map mkVal).map f') =
        renameVal p (Val.set ((xs.map mkVal).map f))
      rw [Val.rename_set, renameRawList_eq_map, List.map_map, List.map_map, List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro x _
      exact heq (mkVal x)
    | _ => rfl

def Val.fnConstruct {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (s : Val sizes A)
    (f : Val sizes A → Val sizes A) : Val sizes A :=
  Quotient.liftOn s (fun sr => match sr with
    | .set xs => Val.fn ((xs.map mkVal).map (fun v => (v, f v)))
    | _ => Val.err)
    (lift_set_sound (fallback := Val.err) (by
      intro xs ys h
      rw [Val.fn_eq_iff]
      rcases ValEq.set_iff.mp h with ⟨h1, h2⟩
      intro kv
      simp only [List.mem_map]
      constructor
      · rintro ⟨w, ⟨a, ha, rfl⟩, rfl⟩
        rcases h1 a ha with ⟨b, hb, hab⟩
        have e : mkVal a = mkVal b := Quotient.sound hab
        exact ⟨mkVal b, ⟨b, hb, rfl⟩, by rw [e]⟩
      · rintro ⟨w, ⟨b, hb, rfl⟩, rfl⟩
        rcases h2 b hb with ⟨a, ha, hab⟩
        have e : mkVal a = mkVal b := Quotient.sound hab
        exact ⟨mkVal a, ⟨a, ha, rfl⟩, by rw [e]⟩))

theorem Val.fnConstruct_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (s : Val sizes A) (f f' : Val sizes A → Val sizes A)
    (heq : ∀ v, f' (renameVal p v) = renameVal p (f v)) :
    Val.fnConstruct (renameVal p s) f' = renameVal p (Val.fnConstruct s f) := by
  induction s using Quotient.ind with
  | _ sr =>
    cases sr with
    | set xs =>
      change Val.fn (((renameRawList p xs).map mkVal).map (fun v => (v, f' v))) =
        renameVal p (Val.fn ((xs.map mkVal).map (fun v => (v, f v))))
      rw [Val.rename_fn, renameRawList_eq_map, List.map_map, List.map_map, List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro x _
      exact Prod.ext rfl (heq (mkVal x))
    | _ => rfl

def Val.union {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] : Val sizes A → Val sizes A :=
  Quotient.lift (fun sr => match sr with
    | .set xs => Val.set (xs.flatMap (fun x => match x with | .set ys => ys.map mkVal | _ => []))
    | _ => Val.err)
    (lift_set_sound (fallback := Val.err) (by
      intro xs ys h
      rw [Val.set_eq_iff]
      rcases ValEq.set_iff.mp h with ⟨h1, h2⟩
      intro v
      simp only [List.mem_flatMap]
      constructor
      · rintro ⟨x, hx, hv⟩
        rcases h1 x hx with ⟨y, hy, hxy⟩
        cases x with
        | set ax =>
          cases y with
          | set ay =>
            rcases List.mem_map.mp hv with ⟨a, ha, rfl⟩
            rcases (ValEq.set_iff.mp hxy).1 a ha with ⟨b, hb, hab⟩
            exact ⟨.set ay, hy, List.mem_map.mpr ⟨b, hb, (Quotient.sound hab).symm⟩⟩
          | _ => exact False.elim hxy
        | _ => cases hv
      · rintro ⟨y, hy, hv⟩
        rcases h2 y hy with ⟨x, hx, hxy⟩
        cases y with
        | set ay =>
          cases x with
          | set ax =>
            rcases List.mem_map.mp hv with ⟨b, hb, rfl⟩
            rcases (ValEq.set_iff.mp hxy).2 b hb with ⟨a, ha, hab⟩
            exact ⟨.set ax, hx, List.mem_map.mpr ⟨a, ha, Quotient.sound hab⟩⟩
          | _ => exact False.elim hxy
        | _ => cases hv))

theorem Val.union_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) (s : Val sizes A) :
    Val.union (renameVal p s) = renameVal p (Val.union s) := by
  induction s using Quotient.ind with
  | _ sr =>
    cases sr with
    | set xs =>
      change Val.set ((renameRawList p xs).flatMap (fun x => match x with | .set ys => ys.map mkVal | _ => [])) =
        renameVal p (Val.set (xs.flatMap (fun x => match x with | .set ys => ys.map mkVal | _ => [])))
      rw [Val.rename_set, Val.set_eq_iff, renameRawList_eq_map]
      intro v
      simp only [List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨x', ⟨x, hx, rfl⟩, hv⟩
        cases x with
        | set ys =>
          simp only [renameRaw, renameRawList_eq_map, List.mem_map] at hv
          rcases hv with ⟨y', ⟨y, hy, rfl⟩, rfl⟩
          exact ⟨mkVal y, ⟨.set ys, hx, List.mem_map_of_mem hy⟩, rfl⟩
        | _ => cases hv
      · rintro ⟨w, ⟨x, hx, hw⟩, rfl⟩
        cases x with
        | set ys =>
          rcases List.mem_map.mp hw with ⟨y, hy, rfl⟩
          refine ⟨renameRaw p (.set ys), ⟨.set ys, hx, rfl⟩, ?_⟩
          simp only [renameRaw, renameRawList_eq_map, List.mem_map]
          exact ⟨renameRaw p y, ⟨y, hy, rfl⟩, rfl⟩
        | _ => cases hw
    | _ => rfl

def sublists {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: t => let subs := sublists t; subs ++ subs.map (a :: ·)

theorem mem_sublists {α : Type} {l sub : List α} :
    sub ∈ sublists l → ∀ x ∈ sub, x ∈ l := by
  induction l generalizing sub with
  | nil =>
    intro h x hx
    simp only [sublists, List.mem_singleton] at h
    subst h; cases hx
  | cons a t ih =>
    intro h x hx
    simp only [sublists, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨s, hs, rfl⟩
    · exact List.mem_cons_of_mem a (ih h x hx)
    · rcases List.mem_cons.mp hx with rfl | hxs
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (ih hs x hxs)

theorem filter_mem_sublists {α : Type} (l : List α) (pred : α → Bool) :
    l.filter pred ∈ sublists l := by
  induction l with
  | nil => exact List.mem_cons_self
  | cons a t ih =>
    simp only [List.filter_cons, sublists, List.mem_append, List.mem_map]
    cases pred a
    · exact Or.inl ih
    · exact Or.inr ⟨t.filter pred, ih, rfl⟩

theorem sublists_map {α β : Type} (f : α → β) (l : List α) :
    sublists (l.map f) = (sublists l).map (List.map f) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, sublists, ih, List.map_append, List.map_map]
    rfl

def Val.powerset {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] : Val sizes A → Val sizes A := by
  classical
  exact Quotient.lift (fun sr => match sr with
    | .set xs => Val.set ((sublists (xs.map mkVal)).map Val.set)
    | _ => Val.err)
    (lift_set_sound (fallback := Val.err) (by
      intro xs ys h
      rw [Val.set_eq_iff]
      rcases ValEq.set_iff.mp h with ⟨h1, h2⟩
      have hmem : ∀ v, v ∈ xs.map mkVal ↔ v ∈ ys.map mkVal := by
        intro v
        simp only [List.mem_map]
        constructor
        · rintro ⟨a, ha, rfl⟩; rcases h1 a ha with ⟨b, hb, he⟩; exact ⟨b, hb, (Quotient.sound he).symm⟩
        · rintro ⟨b, hb, rfl⟩; rcases h2 b hb with ⟨a, ha, he⟩; exact ⟨a, ha, Quotient.sound he⟩
      intro v
      simp only [List.mem_map]
      constructor
      · rintro ⟨sub, hsub, rfl⟩
        refine ⟨(ys.map mkVal).filter (fun w => decide (w ∈ sub)), filter_mem_sublists _ _, ?_⟩
        rw [Val.set_eq_iff]
        intro w
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨fun hw => hw.2, fun hw => ⟨(hmem w).mp (mem_sublists hsub w hw), hw⟩⟩
      · rintro ⟨sub, hsub, rfl⟩
        refine ⟨(xs.map mkVal).filter (fun w => decide (w ∈ sub)), filter_mem_sublists _ _, ?_⟩
        rw [Val.set_eq_iff]
        intro w
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨fun hw => hw.2, fun hw => ⟨(hmem w).mpr (mem_sublists hsub w hw), hw⟩⟩))

theorem Val.powerset_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) (s : Val sizes A) :
    Val.powerset (renameVal p s) = renameVal p (Val.powerset s) := by
  induction s using Quotient.ind with
  | _ sr =>
    cases sr with
    | set xs =>
      change Val.set ((sublists ((renameRawList p xs).map mkVal)).map Val.set) =
        renameVal p (Val.set ((sublists (xs.map mkVal)).map Val.set))
      have hmap : (renameRawList p xs).map mkVal = (xs.map mkVal).map (renameVal p) := by
        rw [renameRawList_eq_map, List.map_map, List.map_map]; rfl
      rw [hmap, sublists_map, Val.rename_set, List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro sub _
      exact (Val.rename_set p sub).symm
    | _ => rfl

def cartTuples {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | s :: rest => s.flatMap (fun x => (cartTuples rest).map (x :: ·))

theorem cartTuples_map {α β : Type} (f : α → β) (ss : List (List α)) :
    cartTuples (ss.map (List.map f)) = (cartTuples ss).map (List.map f) := by
  induction ss with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.map_cons, cartTuples, ih, List.flatMap_map, List.map_flatMap, List.map_map]
    rfl

def cartCons {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (s r : Val sizes A) : Val sizes A :=
  Quotient.liftOn₂ s r (fun sr rr => match sr, rr with
    | .set xs, .set rxs =>
      Val.set ((xs.map mkVal).flatMap (fun x =>
        (rxs.map mkVal).flatMap (fun rv => match Val.seqElems rv with | some ys => [Val.seq (x :: ys)] | none => [])))
    | _, _ => Val.err)
    (lift₂_set_sound (fallback := Val.err) (by
      intro xs1 xs2 rxs1 rxs2 hs hr
      rw [Val.set_eq_iff]
      rcases ValEq.set_iff.mp hs with ⟨hs1, hs2⟩
      rcases ValEq.set_iff.mp hr with ⟨hr1, hr2⟩
      intro v
      simp only [List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨x, ⟨a, ha, rfl⟩, rv, ⟨ra, hra, rfl⟩, hv⟩
        rcases hs1 a ha with ⟨b, hb, hab⟩
        rcases hr1 ra hra with ⟨rb, hrb, hrr'⟩
        have hae : mkVal a = mkVal b := Quotient.sound (s := valSetoid (Key sizes) A) hab
        have hre : mkVal ra = mkVal rb := Quotient.sound (s := valSetoid (Key sizes) A) hrr'
        rw [hae, hre] at hv
        exact ⟨mkVal b, ⟨b, hb, rfl⟩, mkVal rb, ⟨rb, hrb, rfl⟩, hv⟩
      · rintro ⟨x, ⟨b, hb, rfl⟩, rv, ⟨rb, hrb, rfl⟩, hv⟩
        rcases hs2 b hb with ⟨a, ha, hab⟩
        rcases hr2 rb hrb with ⟨ra, hra, hrr'⟩
        have hae : mkVal a = mkVal b := Quotient.sound (s := valSetoid (Key sizes) A) hab
        have hre : mkVal ra = mkVal rb := Quotient.sound (s := valSetoid (Key sizes) A) hrr'
        rw [← hae, ← hre] at hv
        exact ⟨mkVal a, ⟨a, ha, rfl⟩, mkVal ra, ⟨ra, hra, rfl⟩, hv⟩))

theorem cartCons_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (s r : Val sizes A) :
    cartCons (renameVal p s) (renameVal p r) = renameVal p (cartCons s r) := by
  induction s using Quotient.ind with
  | _ sr =>
    induction r using Quotient.ind with
    | _ rr =>
      cases sr with
      | set xs =>
        cases rr with
        | set rxs =>
          change Val.set (((renameRawList p xs).map mkVal).flatMap (fun x =>
              ((renameRawList p rxs).map mkVal).flatMap (fun rv => match Val.seqElems rv with | some ys => [Val.seq (x :: ys)] | none => []))) =
            renameVal p (Val.set ((xs.map mkVal).flatMap (fun x =>
              (rxs.map mkVal).flatMap (fun rv => match Val.seqElems rv with | some ys => [Val.seq (x :: ys)] | none => []))))
          rw [Val.rename_set, Val.set_eq_iff, renameRawList_eq_map, renameRawList_eq_map]
          intro v
          simp only [List.mem_flatMap, List.mem_map]
          constructor
          · rintro ⟨x, ⟨a', ⟨a, ha, rfl⟩, rfl⟩, rv', ⟨ra', ⟨ra, hra, rfl⟩, rfl⟩, hv⟩
            have hse : Val.seqElems (mkVal (renameRaw p ra)) = (Val.seqElems (mkVal ra)).map (List.map (renameVal p)) :=
              Val.seqElems_rename p (mkVal ra)
            rw [hse] at hv
            cases hrv : Val.seqElems (mkVal ra) with
            | none => rw [hrv] at hv; cases hv
            | some ys =>
              simp only [hrv, Option.map_some, List.mem_singleton] at hv
              subst hv
              refine ⟨Val.seq (mkVal a :: ys),
                ⟨mkVal a, ⟨a, ha, rfl⟩, mkVal ra, ⟨ra, hra, rfl⟩, by rw [hrv]; exact List.mem_cons_self⟩, ?_⟩
              rw [Val.rename_seq, List.map_cons]
              rfl
          · rintro ⟨w, ⟨x, ⟨a, ha, rfl⟩, rv, ⟨ra, hra, rfl⟩, hw⟩, rfl⟩
            cases hrv : Val.seqElems (mkVal ra) with
            | none => rw [hrv] at hw; cases hw
            | some ys =>
              simp only [hrv, List.mem_singleton] at hw
              subst hw
              refine ⟨renameVal p (mkVal a), ⟨renameRaw p a, ⟨a, ha, rfl⟩, rfl⟩,
                renameVal p (mkVal ra), ⟨renameRaw p ra, ⟨ra, hra, rfl⟩, rfl⟩, ?_⟩
              rw [Val.seqElems_rename, hrv, Option.map_some, List.mem_singleton, Val.rename_seq, List.map_cons]
        | _ => rfl
      | _ => rfl

def cartSet {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] : List (Val sizes A) → Val sizes A
  | [] => Val.set [Val.seq []]
  | s :: rest => cartCons s (cartSet rest)

theorem cartSet_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (ss : List (Val sizes A)) :
    cartSet (ss.map (renameVal p)) = renameVal p (cartSet ss) := by
  induction ss with
  | nil =>
    change Val.set [Val.seq []] = renameVal p (Val.set [Val.seq []])
    rw [Val.rename_set]
    rfl
  | cons s rest ih =>
    simp only [List.map_cons, cartSet, ih, cartCons_rename]

def allMaps {α β : Type} : List α → List β → List (List (α × β))
  | [], _ => [[]]
  | a :: ds, rs => rs.flatMap (fun r => (allMaps ds rs).map (fun m => (a, r) :: m))

theorem mem_allMaps {α β : Type} {ds : List α} {rs : List β} {m : List (α × β)} :
    m ∈ allMaps ds rs ↔ m.map Prod.fst = ds ∧ ∀ kv ∈ m, kv.2 ∈ rs := by
  induction ds generalizing m with
  | nil =>
    simp only [allMaps, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨rfl, fun _ h => nomatch h⟩
    · rintro ⟨hm, _⟩; cases m with | nil => rfl | cons _ _ => cases hm
  | cons a ds ih =>
    simp only [allMaps, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨r, hr, m', hm', rfl⟩
      rcases ih.mp hm' with ⟨h1, h2⟩
      refine ⟨by simp only [List.map_cons, h1], fun kv hkv => ?_⟩
      rcases List.mem_cons.mp hkv with rfl | hkv'
      · exact hr
      · exact h2 kv hkv'
    · rintro ⟨h1, h2⟩
      cases m with
      | nil => cases h1
      | cons kv t =>
        simp only [List.map_cons, List.cons.injEq] at h1
        rcases h1 with ⟨rfl, ht⟩
        refine ⟨kv.2, h2 kv List.mem_cons_self, t,
          ih.mpr ⟨ht, fun x hx => h2 x (List.mem_cons_of_mem kv hx)⟩, by cases kv; rfl⟩

theorem allMaps_map {α β α' β' : Type} (f : α → α') (g : β → β') (ds : List α) (rs : List β) :
    allMaps (ds.map f) (rs.map g) = (allMaps ds rs).map (List.map (fun kv => (f kv.1, g kv.2))) := by
  induction ds with
  | nil => rfl
  | cons a ds ih =>
    simp only [List.map_cons, allMaps, ih, List.flatMap_map, List.map_flatMap, List.map_map]
    rfl

private theorem fn_of_nodup_graph {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    {ds1 ds2 : List (Val sizes A)} {rs : List (Val sizes A)}
    (hnd1 : ds1.Nodup) (heq : ∀ x, x ∈ ds1 ↔ x ∈ ds2)
    {m : List (Val sizes A × Val sizes A)} (hm : m ∈ allMaps ds1 rs) :
    ∃ m' ∈ allMaps ds2 rs, Val.fn m = Val.fn m' := by
  classical
  rcases mem_allMaps.mp hm with ⟨hfst, hsnd⟩
  have hex : ∀ x ∈ ds1, ∃ y ∈ rs, (x, y) ∈ m := by
    intro x hx
    rw [← hfst] at hx
    rcases List.mem_map.mp hx with ⟨kv, hkv, rfl⟩
    exact ⟨kv.2, hsnd kv hkv, hkv⟩
  have huniq : ∀ x y1 y2, (x, y1) ∈ m → (x, y2) ∈ m → y1 = y2 := by
    clear hex hsnd heq hm
    induction m generalizing ds1 with
    | nil => intro _ _ _ h _; cases h
    | cons kv t ih =>
      intro x y1 y2 h1 h2
      cases ds1 with
      | nil => cases hfst
      | cons a ds =>
        simp only [List.map_cons, List.cons.injEq] at hfst
        rcases hfst with ⟨rfl, ht⟩
        have hnd := List.nodup_cons.mp hnd1
        rcases List.mem_cons.mp h1 with e1 | ht1
        · rcases List.mem_cons.mp h2 with e2 | ht2
          · exact (Prod.mk.inj (e1.trans e2.symm)).2
          · exfalso
            have hx : kv.1 = x := (Prod.mk.inj e1).1.symm
            have : kv.1 ∈ ds := ht ▸ List.mem_map.mpr ⟨(x, y2), ht2, hx.symm⟩
            exact hnd.1 this
        · rcases List.mem_cons.mp h2 with e2 | ht2
          · exfalso
            have hx : kv.1 = x := (Prod.mk.inj e2).1.symm
            have : kv.1 ∈ ds := ht ▸ List.mem_map.mpr ⟨(x, y1), ht1, hx.symm⟩
            exact hnd.1 this
          · exact ih hnd.2 ht x y1 y2 ht1 ht2
  let pick : Val sizes A → Val sizes A := fun x =>
    if h : ∃ y, (x, y) ∈ m then Classical.choose h else Val.err
  let m' := ds2.map (fun x => (x, pick x))
  have hm'fst : m'.map Prod.fst = ds2 := by
    simp only [m', List.map_map]
    exact List.map_id ds2
  refine ⟨m', mem_allMaps.mpr ⟨hm'fst, fun kv hkv => ?_⟩, ?_⟩
  · rcases List.mem_map.mp hkv with ⟨x, hx, rfl⟩
    rcases hex x ((heq x).mpr hx) with ⟨y, hy, hxy⟩
    have hch : ∃ y, (x, y) ∈ m := ⟨y, hxy⟩
    have : pick x = Classical.choose hch := by simp only [pick, hch, ↓reduceDIte]
    rw [this]
    exact hsnd (x, Classical.choose hch) (Classical.choose_spec hch)
  · rw [Val.fn_eq_iff]
    intro kv
    constructor
    · intro hkv
      have h1 : kv.1 ∈ ds1 := hfst ▸ List.mem_map_of_mem hkv
      have h2 : kv.1 ∈ ds2 := (heq kv.1).mp h1
      have hch : ∃ y, (kv.1, y) ∈ m := ⟨kv.2, hkv⟩
      have hpe : pick kv.1 = kv.2 := by
        have : pick kv.1 = Classical.choose hch := by simp only [pick, hch, ↓reduceDIte]
        rw [this]
        exact huniq kv.1 _ kv.2 (Classical.choose_spec hch) hkv
      exact List.mem_map.mpr ⟨kv.1, h2, Prod.ext rfl hpe⟩
    · intro hkv
      rcases List.mem_map.mp hkv with ⟨x, hx, rfl⟩
      rcases hex x ((heq x).mpr hx) with ⟨y, _, hxy⟩
      have hch : ∃ y, (x, y) ∈ m := ⟨y, hxy⟩
      have : pick x = Classical.choose hch := by simp only [pick, hch, ↓reduceDIte]
      rw [this]
      exact Classical.choose_spec hch

def Val.fnSet {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (dom ran : Val sizes A) : Val sizes A := by
  classical
  exact Quotient.liftOn₂ dom ran (fun dr rr => match dr, rr with
    | .set ds, .set rs => Val.set ((allMaps (dedupList (ds.map mkVal)) (rs.map mkVal)).map Val.fn)
    | _, _ => Val.err)
    (lift₂_set_sound (fallback := Val.err) (by
      intro ds1 ds2 rs1 rs2 hd hr
      rcases ValEq.set_iff.mp hd with ⟨hd1, hd2⟩
      rcases ValEq.set_iff.mp hr with ⟨hr1, hr2⟩
      have hdeq : ∀ x, x ∈ dedupList (ds1.map mkVal) ↔ x ∈ dedupList (ds2.map mkVal) := by
        intro x
        simp only [mem_dedupList, List.mem_map]
        constructor
        · rintro ⟨a, ha, rfl⟩; rcases hd1 a ha with ⟨b, hb, he⟩; exact ⟨b, hb, (Quotient.sound he).symm⟩
        · rintro ⟨b, hb, rfl⟩; rcases hd2 b hb with ⟨a, ha, he⟩; exact ⟨a, ha, Quotient.sound he⟩
      have hreq : ∀ y, y ∈ rs1.map mkVal ↔ y ∈ rs2.map mkVal := by
        intro y
        simp only [List.mem_map]
        constructor
        · rintro ⟨a, ha, rfl⟩; rcases hr1 a ha with ⟨b, hb, he⟩; exact ⟨b, hb, (Quotient.sound he).symm⟩
        · rintro ⟨b, hb, rfl⟩; rcases hr2 b hb with ⟨a, ha, he⟩; exact ⟨a, ha, Quotient.sound he⟩
      rw [Val.set_eq_iff]
      intro v
      simp only [List.mem_map]
      constructor
      · rintro ⟨m, hm, rfl⟩
        have hm2 : m ∈ allMaps (dedupList (ds1.map mkVal)) (rs2.map mkVal) := by
          rcases mem_allMaps.mp hm with ⟨h1, h2⟩
          exact mem_allMaps.mpr ⟨h1, fun kv hkv => (hreq _).mp (h2 kv hkv)⟩
        rcases fn_of_nodup_graph (nodup_dedupList _) hdeq hm2 with ⟨m', hm', hfe⟩
        exact ⟨m', hm', hfe.symm⟩
      · rintro ⟨m, hm, rfl⟩
        have hm1 : m ∈ allMaps (dedupList (ds2.map mkVal)) (rs1.map mkVal) := by
          rcases mem_allMaps.mp hm with ⟨h1, h2⟩
          exact mem_allMaps.mpr ⟨h1, fun kv hkv => (hreq _).mpr (h2 kv hkv)⟩
        rcases fn_of_nodup_graph (nodup_dedupList _) (fun x => (hdeq x).symm) hm1 with ⟨m', hm', hfe⟩
        exact ⟨m', hm', hfe.symm⟩))

theorem Val.fnSet_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (dom ran : Val sizes A) :
    Val.fnSet (renameVal p dom) (renameVal p ran) = renameVal p (Val.fnSet dom ran) := by
  classical
  induction dom using Quotient.ind with
  | _ dr =>
    induction ran using Quotient.ind with
    | _ rr =>
      cases dr with
      | set ds =>
        cases rr with
        | set rs =>
          change Val.set ((allMaps (dedupList ((renameRawList p ds).map mkVal)) ((renameRawList p rs).map mkVal)).map Val.fn) =
            renameVal p (Val.set ((allMaps (dedupList (ds.map mkVal)) (rs.map mkVal)).map Val.fn))
          have hrmap : (renameRawList p rs).map mkVal = (rs.map mkVal).map (renameVal p) := by
            rw [renameRawList_eq_map, List.map_map, List.map_map]; rfl
          have hdeq : ∀ x, x ∈ dedupList ((renameRawList p ds).map mkVal) ↔
              x ∈ (dedupList (ds.map mkVal)).map (renameVal p) := by
            intro x
            simp only [mem_dedupList, renameRawList_eq_map, List.mem_map]
            constructor
            · rintro ⟨a', ⟨a, ha, rfl⟩, rfl⟩
              exact ⟨mkVal a, ⟨a, ha, rfl⟩, rfl⟩
            · rintro ⟨w, ⟨a, ha, rfl⟩, rfl⟩
              exact ⟨renameRaw p a, ⟨a, ha, rfl⟩, rfl⟩
          rw [hrmap, Val.rename_set, Val.set_eq_iff]
          intro v
          simp only [List.mem_map]
          constructor
          · rintro ⟨m, hm, rfl⟩
            rcases fn_of_nodup_graph (nodup_dedupList _) hdeq hm with ⟨m', hm', hfe⟩
            rw [allMaps_map] at hm'
            rcases List.mem_map.mp hm' with ⟨m0, hm0, rfl⟩
            refine ⟨Val.fn m0, ⟨m0, hm0, rfl⟩, ?_⟩
            rw [Val.rename_fn, hfe]
          · rintro ⟨w, ⟨m0, hm0, rfl⟩, rfl⟩
            have hm' : m0.map (fun kv => (renameVal p kv.1, renameVal p kv.2)) ∈
                allMaps ((dedupList (ds.map mkVal)).map (renameVal p)) ((rs.map mkVal).map (renameVal p)) := by
              rw [allMaps_map]
              exact List.mem_map_of_mem hm0
            have hnd2 := nodup_map_inj (fun _ _ h => (renameVal_injective p).mp h) (nodup_dedupList (ds.map mkVal))
            rcases fn_of_nodup_graph hnd2 (fun x => (hdeq x).symm) hm' with ⟨m, hm, hfe⟩
            refine ⟨m, hm, ?_⟩
            rw [Val.rename_fn, hfe]
        | _ => rfl
      | _ => rfl

def recCons {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (f : A) (s r : Val sizes A) : Val sizes A :=
  Quotient.liftOn₂ s r (fun sr rr => match sr, rr with
    | .set xs, .set rxs =>
      Val.set ((xs.map mkVal).flatMap (fun v =>
        rxs.flatMap (fun rv => match rawFnPairs rv with
          | some ps => [Val.fn ((Val.atom f, v) :: ps.map (fun kv => (mkVal kv.1, mkVal kv.2)))]
          | none => [])))
    | _, _ => Val.err)
    (lift₂_set_sound (fallback := Val.err) (by
      intro xs1 xs2 rxs1 rxs2 hs hr
      rw [Val.set_eq_iff]
      rcases ValEq.set_iff.mp hs with ⟨hs1, hs2⟩
      rcases ValEq.set_iff.mp hr with ⟨hr1, hr2⟩
      intro w
      simp only [List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨v, ⟨a, ha, rfl⟩, rv, hrm, hw⟩
        rcases hs1 a ha with ⟨b, hb, hab⟩
        rcases hr1 rv hrm with ⟨rv', hrv', hrr'⟩
        have hfs := ValEq.rawFnPairs_some hrr'
        cases hp1 : rawFnPairs rv <;> cases hp2 : rawFnPairs rv'
        · rw [hp1] at hw; cases hw
        · rw [hp1, hp2] at hfs; cases hfs
        · rw [hp1, hp2] at hfs; cases hfs
        · case some.some ps1 ps2 =>
          simp only [hp1, List.mem_singleton] at hw
          subst hw
          rcases (ValEq.fnPairs_iff hp1 hp2).mp hrr' with ⟨hf1, hf2⟩
          have hae : mkVal a = mkVal b := Quotient.sound (s := valSetoid (Key sizes) A) hab
          have hfe : Val.fn ((Val.atom f, mkVal a) :: ps1.map (fun kv => (mkVal kv.1, mkVal kv.2))) =
              Val.fn ((Val.atom f, mkVal b) :: ps2.map (fun kv => (mkVal kv.1, mkVal kv.2))) := by
            rw [hae, Val.fn_eq_iff]
            intro kv
            simp only [List.mem_cons, List.mem_map]
            constructor
            · rintro (rfl | ⟨x, hx, rfl⟩)
              · exact Or.inl rfl
              · right
                rcases hf1 x hx with ⟨y, hy, h1e, h2e⟩
                exact ⟨y, hy, Prod.ext (Quotient.sound h1e).symm (Quotient.sound h2e).symm⟩
            · rintro (rfl | ⟨y, hy, rfl⟩)
              · exact Or.inl rfl
              · right
                rcases hf2 y hy with ⟨x, hx, h1e, h2e⟩
                exact ⟨x, hx, Prod.ext (Quotient.sound h1e) (Quotient.sound h2e)⟩
          exact ⟨mkVal b, ⟨b, hb, rfl⟩, rv', hrv', by simp only [hp2, List.mem_singleton, hfe]⟩
      · rintro ⟨v, ⟨b, hb, rfl⟩, rv', hrv', hw⟩
        rcases hs2 b hb with ⟨a, ha, hab⟩
        rcases hr2 rv' hrv' with ⟨rv, hrm, hrr'⟩
        have hfs := ValEq.rawFnPairs_some hrr'
        cases hp1 : rawFnPairs rv <;> cases hp2 : rawFnPairs rv'
        · rw [hp2] at hw; cases hw
        · rw [hp1, hp2] at hfs; cases hfs
        · rw [hp1, hp2] at hfs; cases hfs
        · case some.some ps1 ps2 =>
          simp only [hp2, List.mem_singleton] at hw
          subst hw
          rcases (ValEq.fnPairs_iff hp1 hp2).mp hrr' with ⟨hf1, hf2⟩
          have hae : mkVal a = mkVal b := Quotient.sound (s := valSetoid (Key sizes) A) hab
          have hfe : Val.fn ((Val.atom f, mkVal b) :: ps2.map (fun kv => (mkVal kv.1, mkVal kv.2))) =
              Val.fn ((Val.atom f, mkVal a) :: ps1.map (fun kv => (mkVal kv.1, mkVal kv.2))) := by
            rw [← hae, Val.fn_eq_iff]
            intro kv
            simp only [List.mem_cons, List.mem_map]
            constructor
            · rintro (rfl | ⟨y, hy, rfl⟩)
              · exact Or.inl rfl
              · right
                rcases hf2 y hy with ⟨x, hx, h1e, h2e⟩
                exact ⟨x, hx, Prod.ext (Quotient.sound h1e) (Quotient.sound h2e)⟩
            · rintro (rfl | ⟨x, hx, rfl⟩)
              · exact Or.inl rfl
              · right
                rcases hf1 x hx with ⟨y, hy, h1e, h2e⟩
                exact ⟨y, hy, Prod.ext (Quotient.sound h1e).symm (Quotient.sound h2e).symm⟩
          exact ⟨mkVal a, ⟨a, ha, rfl⟩, rv, hrm, by simp only [hp1, List.mem_singleton, hfe]⟩))

theorem recCons_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (f : A) (s r : Val sizes A) :
    recCons f (renameVal p s) (renameVal p r) = renameVal p (recCons f s r) := by
  induction s using Quotient.ind with
  | _ sr =>
    induction r using Quotient.ind with
    | _ rr =>
      cases sr with
      | set xs =>
        cases rr with
        | set rxs =>
          change Val.set (((renameRawList p xs).map mkVal).flatMap (fun v =>
              (renameRawList p rxs).flatMap (fun rv => match rawFnPairs rv with
                | some ps => [Val.fn ((Val.atom f, v) :: ps.map (fun kv => (mkVal kv.1, mkVal kv.2)))]
                | none => []))) =
            renameVal p (Val.set ((xs.map mkVal).flatMap (fun v =>
              rxs.flatMap (fun rv => match rawFnPairs rv with
                | some ps => [Val.fn ((Val.atom f, v) :: ps.map (fun kv => (mkVal kv.1, mkVal kv.2)))]
                | none => []))))
          rw [Val.rename_set, Val.set_eq_iff, renameRawList_eq_map, renameRawList_eq_map]
          intro w
          simp only [List.mem_flatMap, List.mem_map]
          constructor
          · rintro ⟨v, ⟨a', ⟨a, ha, rfl⟩, rfl⟩, rv', ⟨rv, hrv, rfl⟩, hw⟩
            rw [rawFnPairs_rename] at hw
            cases hp : rawFnPairs rv with
            | none => rw [hp] at hw; cases hw
            | some ps =>
              simp only [hp, Option.map_some, renameRawPairs_eq_map, List.mem_singleton] at hw
              subst hw
              refine ⟨Val.fn ((Val.atom f, mkVal a) :: ps.map (fun kv => (mkVal kv.1, mkVal kv.2))),
                ⟨mkVal a, ⟨a, ha, rfl⟩, rv, hrv, by rw [hp]; exact List.mem_cons_self⟩, ?_⟩
              rw [Val.rename_fn, List.map_cons, List.map_map, List.map_map]
              rfl
          · rintro ⟨w0, ⟨v, ⟨a, ha, rfl⟩, rv, hrv, hw⟩, rfl⟩
            cases hp : rawFnPairs rv with
            | none => rw [hp] at hw; cases hw
            | some ps =>
              simp only [hp, List.mem_singleton] at hw
              subst hw
              refine ⟨renameVal p (mkVal a), ⟨renameRaw p a, ⟨a, ha, rfl⟩, rfl⟩,
                renameRaw p rv, ⟨rv, hrv, rfl⟩, ?_⟩
              rw [rawFnPairs_rename, hp, Option.map_some, renameRawPairs_eq_map, List.mem_singleton]
              rw [Val.rename_fn, List.map_cons, List.map_map, List.map_map]
              rfl
        | _ => rfl
      | _ => rfl

def Val.recSet {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] :
    List (A × Val sizes A) → Val sizes A
  | [] => Val.set [Val.fn []]
  | (f, s) :: rest => recCons f s (Val.recSet rest)

theorem Val.recSet_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (fs : List (A × Val sizes A)) :
    Val.recSet (fs.map (fun kv => (kv.1, renameVal p kv.2))) = renameVal p (Val.recSet fs) := by
  induction fs with
  | nil =>
    change Val.set [Val.fn []] = renameVal p (Val.set [Val.fn []])
    rw [Val.rename_set]
    rfl
  | cons pair rest ih =>
    rcases pair with ⟨f, s⟩
    simp only [List.map_cons, Val.recSet, ih, recCons_rename]

def Val.groupSet {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (mask : GroupMask d) : Val sizes A :=
  Val.set ((List.finRange d).flatMap (fun g =>
    if mask g then (List.finRange (sizes g)).map (fun i => Val.key ⟨g, i⟩) else []))

theorem Val.groupSet_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (mask : GroupMask d) :
    renameVal p (Val.groupSet (A := A) mask) = Val.groupSet mask := by
  unfold Val.groupSet
  rw [Val.rename_set, Val.set_eq_iff]
  intro v
  simp only [List.mem_map, List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨w, ⟨g, hg⟩, rfl⟩
    cases hm : mask g
    · simp only [hm, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at hg
    · simp only [hm, ↓reduceIte, List.mem_map, List.mem_finRange, true_and] at hg
      rcases hg with ⟨i, rfl⟩
      refine ⟨g, ?_⟩
      simp only [hm, ↓reduceIte, List.mem_map, List.mem_finRange, true_and]
      exact ⟨(p g).toFun i, rfl⟩
  · rintro ⟨g, hg⟩
    cases hm : mask g
    · simp only [hm, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at hg
    · simp only [hm, ↓reduceIte, List.mem_map, List.mem_finRange, true_and] at hg
      rcases hg with ⟨i, rfl⟩
      refine ⟨Val.key ⟨g, (p g).invFun i⟩, ⟨g, ?_⟩, ?_⟩
      · simp only [hm, ↓reduceIte, List.mem_map, List.mem_finRange, true_and]
        exact ⟨(p g).invFun i, rfl⟩
      · change Val.key ⟨g, (p g).toFun ((p g).invFun i)⟩ = Val.key ⟨g, i⟩
        rw [(p g).right]

-- Sequence operations on Val
def Val.len {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (v : Val sizes A) : Val sizes A :=
  match Val.seqElems v with
  | some xs => Val.atom (HasNatAtom.natAtom xs.length)
  | none => Val.err

theorem Val.len_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (v : Val sizes A) :
    Val.len (renameVal p v) = renameVal p (Val.len v) := by
  unfold Val.len
  rw [Val.seqElems_rename]
  cases Val.seqElems v with
  | some xs => simp only [Option.map_some, List.length_map]; rfl
  | none => rfl

def Val.head {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (v : Val sizes A) : Val sizes A :=
  match Val.seqElems v with
  | some (x :: _) => x
  | _ => Val.err

theorem Val.head_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) (v : Val sizes A) :
    Val.head (renameVal p v) = renameVal p (Val.head v) := by
  unfold Val.head
  rw [Val.seqElems_rename]
  cases Val.seqElems v with
  | none => rfl
  | some xs => cases xs <;> rfl

def Val.tail {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (v : Val sizes A) : Val sizes A :=
  match Val.seqElems v with
  | some (_ :: xs) => Val.seq xs
  | _ => Val.err

theorem Val.tail_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) (v : Val sizes A) :
    Val.tail (renameVal p v) = renameVal p (Val.tail v) := by
  unfold Val.tail
  rw [Val.seqElems_rename]
  cases Val.seqElems v with
  | none => rfl
  | some xs =>
    cases xs with
    | nil => rfl
    | cons _ t =>
      simp only [Option.map_some, List.map_cons]
      exact (Val.rename_seq p t).symm

def Val.append {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (s elem : Val sizes A) : Val sizes A :=
  match Val.seqElems s with
  | some xs => Val.seq (xs ++ [elem])
  | none => Val.err

theorem Val.append_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (s elem : Val sizes A) :
    Val.append (renameVal p s) (renameVal p elem) = renameVal p (Val.append s elem) := by
  unfold Val.append
  rw [Val.seqElems_rename]
  cases Val.seqElems s with
  | none => rfl
  | some xs =>
    simp only [Option.map_some]
    rw [Val.rename_seq, List.map_append, List.map_singleton]

def Val.concat {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (a b : Val sizes A) : Val sizes A :=
  match Val.seqElems a, Val.seqElems b with
  | some xs, some ys => Val.seq (xs ++ ys)
  | _, _ => Val.err

theorem Val.concat_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (a b : Val sizes A) :
    Val.concat (renameVal p a) (renameVal p b) = renameVal p (Val.concat a b) := by
  unfold Val.concat
  rw [Val.seqElems_rename, Val.seqElems_rename]
  cases Val.seqElems a with
  | none => rfl
  | some xs =>
    cases Val.seqElems b with
    | none => rfl
    | some ys =>
      simp only [Option.map_some]
      rw [Val.rename_seq, List.map_append]

def sliceList {α : Type} (xs : List α) (m n : Int) : List α :=
  if m > n then []
  else (xs.drop (m - 1).toNat).take ((n - m + 1).toNat)

theorem sliceList_map {α β : Type} (f : α → β) (xs : List α) (m n : Int) :
    sliceList (xs.map f) m n = (sliceList xs m n).map f := by
  unfold sliceList
  split
  · rfl
  · simp only [List.map_drop, List.map_take]

def Val.subseq {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (intOf : A → Option Int) (s lo hi : Val sizes A) : Val sizes A :=
  match Val.seqElems s, Val.asAtom lo, Val.asAtom hi with
  | some xs, some al, some ah =>
    match intOf al, intOf ah with
    | some m, some n => Val.seq (sliceList xs m n)
    | _, _ => Val.err
  | _, _, _ => Val.err

theorem Val.subseq_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (intOf : A → Option Int) (s lo hi : Val sizes A) :
    Val.subseq intOf (renameVal p s) (renameVal p lo) (renameVal p hi) =
      renameVal p (Val.subseq intOf s lo hi) := by
  unfold Val.subseq
  rw [Val.seqElems_rename, Val.asAtom_rename, Val.asAtom_rename]
  cases Val.seqElems s with
  | none => rfl
  | some xs =>
    simp only [Option.map_some]
    cases Val.asAtom lo with
    | none => rfl
    | some al =>
      cases Val.asAtom hi with
      | none => rfl
      | some ah =>
        dsimp only
        cases intOf al with
        | none => rfl
        | some m =>
          cases intOf ah with
          | none => rfl
          | some n =>
            dsimp only
            rw [sliceList_map]
            exact (Val.rename_seq p _).symm

def Val.selectSeq {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (s : Val sizes A)
    (pred : Val sizes A → Prop) : Val sizes A := by
  classical
  exact match Val.seqElems s with
  | some xs => Val.seq (xs.filter (fun v => decide (pred v)))
  | none => Val.err

theorem Val.selectSeq_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (s : Val sizes A) (pred pred' : Val sizes A → Prop)
    (heq : ∀ v, pred' (renameVal p v) ↔ pred v) :
    Val.selectSeq (renameVal p s) pred' = renameVal p (Val.selectSeq s pred) := by
  classical
  unfold Val.selectSeq
  rw [Val.seqElems_rename]
  cases Val.seqElems s with
  | none => rfl
  | some xs =>
    simp only [Option.map_some]
    rw [Val.rename_seq]
    congr 1
    induction xs with
    | nil => rfl
    | cons x t ih =>
      simp only [List.map_cons, List.filter_cons]
      have hdec : decide (pred' (renameVal p x)) = decide (pred x) := propext (heq x) ▸ rfl
      rw [hdec]
      cases decide (pred x)
      · exact ih
      · simp only [↓reduceIte, List.map_cons, ih]

-- Sequence fold and commutative-associative mapped-set fold operations on Val
theorem Val.cup_comm {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (a b : Val sizes A) :
    Val.cup a b = Val.cup b a := by
  induction a using Quotient.ind with
  | _ ar =>
    induction b using Quotient.ind with
    | _ br =>
      cases ar with
      | set xs =>
        cases br with
        | set ys =>
          change Val.set (xs.map mkVal ++ ys.map mkVal) = Val.set (ys.map mkVal ++ xs.map mkVal)
          rw [Val.set_eq_iff]
          intro v
          simp only [List.mem_append]
          exact Or.comm
        | _ => rfl
      | _ => cases br <;> rfl

theorem Val.cup_assoc {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (a b c : Val sizes A) :
    Val.cup (Val.cup a b) c = Val.cup a (Val.cup b c) := by
  induction a using Quotient.ind with
  | _ ar =>
    induction b using Quotient.ind with
    | _ br =>
      induction c using Quotient.ind with
      | _ cr =>
        cases ar with
        | set xs =>
          cases br with
          | set ys =>
            cases cr with
            | set zs =>
              change Val.cup (Val.set (xs.map mkVal ++ ys.map mkVal)) (mkVal (.set zs)) =
                Val.cup (mkVal (.set xs)) (Val.set (ys.map mkVal ++ zs.map mkVal))
              unfold Val.set
              change Val.set ((((xs.map mkVal ++ ys.map mkVal).map valOut).map mkVal) ++ zs.map mkVal) =
                Val.set (xs.map mkVal ++ (((ys.map mkVal ++ zs.map mkVal).map valOut).map mkVal))
              rw [Val.set_eq_iff]
              intro v
              simp only [List.mem_append, List.map_map, Function.comp_def, valOut_eq, List.map_id']
              exact or_assoc
            | _ => rfl
          | _ => rfl
        | _ => exact Eq.symm (Quotient.ind (motive := fun v => Val.cup _ v = Val.err) (fun _ => rfl) (Val.cup (mkVal br) (mkVal cr)))

private theorem Val.cap_mk_set {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (xs ys : List (RawVal (Key sizes) A)) :
    Val.cap (mkVal (.set xs)) (mkVal (.set ys)) =
      Val.set ((xs.map mkVal).filter (fun v => @decide (Val.mem v (mkVal (.set ys))) (Classical.propDecidable _))) := by
  classical
  unfold Val.cap
  have hb : Val.isSet (mkVal (.set ys) : Val sizes A) := trivial
  simp only [hb, ↓reduceIte]
  rfl

private theorem Val.cap_not_set_left {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    {a : Val sizes A} (ha : ¬ Val.isSet a) (b : Val sizes A) :
    Val.cap a b = Val.err := by
  classical
  unfold Val.cap
  split
  · induction a using Quotient.ind with
    | _ ar =>
      cases ar with
      | set _ => exact absurd trivial ha
      | _ => rfl
  · rfl

private theorem Val.cap_not_set_right {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (a : Val sizes A) {b : Val sizes A} (hb : ¬ Val.isSet b) :
    Val.cap a b = Val.err := by
  classical
  unfold Val.cap
  simp only [hb, ↓reduceIte]

theorem Val.cap_comm {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (a b : Val sizes A) :
    Val.cap a b = Val.cap b a := by
  classical
  by_cases ha : Val.isSet a
  · by_cases hb : Val.isSet b
    · induction a using Quotient.ind with
      | _ ar =>
        induction b using Quotient.ind with
        | _ br =>
          cases ar <;> try exact absurd ha (by intro h; exact h)
          cases br <;> try exact absurd hb (by intro h; exact h)
          case set.set xs ys =>
            change Val.cap (mkVal (.set xs)) (mkVal (.set ys)) = Val.cap (mkVal (.set ys)) (mkVal (.set xs))
            rw [Val.cap_mk_set, Val.cap_mk_set, Val.set_eq_iff]
            intro v
            simp only [List.mem_filter, List.mem_map, decide_eq_true_eq]
            constructor
            · rintro ⟨⟨x, hx, rfl⟩, ⟨y, hy, hyx⟩⟩
              exact ⟨⟨y, hy, hyx⟩, ⟨x, hx, rfl⟩⟩
            · rintro ⟨⟨y, hy, rfl⟩, ⟨x, hx, hxy⟩⟩
              exact ⟨⟨x, hx, hxy⟩, ⟨y, hy, rfl⟩⟩
    · rw [Val.cap_not_set_right a hb, Val.cap_not_set_left hb a]
  · rw [Val.cap_not_set_left ha b, Val.cap_not_set_right b ha]

theorem Val.cap_assoc {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (a b c : Val sizes A) :
    Val.cap (Val.cap a b) c = Val.cap a (Val.cap b c) := by
  classical
  by_cases ha : Val.isSet a
  · by_cases hb : Val.isSet b
    · by_cases hc : Val.isSet c
      · induction a using Quotient.ind with
        | _ ar =>
          induction b using Quotient.ind with
          | _ br =>
            induction c using Quotient.ind with
            | _ cr =>
              cases ar <;> try exact absurd ha (by intro h; exact h)
              cases br <;> try exact absurd hb (by intro h; exact h)
              cases cr <;> try exact absurd hc (by intro h; exact h)
              case set.set.set xs ys zs =>
                change Val.cap (Val.cap (mkVal (.set xs)) (mkVal (.set ys))) (mkVal (.set zs)) =
                  Val.cap (mkVal (.set xs)) (Val.cap (mkVal (.set ys)) (mkVal (.set zs)))
                rw [Val.cap_mk_set, Val.cap_mk_set]
                unfold Val.set
                rw [Val.cap_mk_set, Val.cap_mk_set, Val.set_eq_iff]
                intro v
                simp only [List.mem_filter, List.map_map, Function.comp_def, valOut_eq, List.map_id', decide_eq_true_eq]
                constructor
                · rintro ⟨⟨hx, hy⟩, hz⟩
                  refine ⟨hx, ?_⟩
                  change ∃ r ∈ ((ys.map mkVal).filter (fun w => @decide (Val.mem w (mkVal (.set zs))) (Classical.propDecidable _))).map valOut, mkVal r = v
                  rcases hy with ⟨y, hy', rfl⟩
                  refine ⟨valOut (mkVal y), List.mem_map_of_mem ?_, valOut_eq _⟩
                  simp only [List.mem_filter, decide_eq_true_eq]
                  exact ⟨List.mem_map_of_mem hy', hz⟩
                · rintro ⟨hx, hyz⟩
                  rcases hyz with ⟨r, hr, rfl⟩
                  rcases List.mem_map.mp hr with ⟨w, hw, rfl⟩
                  rw [valOut_eq] at *
                  simp only [List.mem_filter, List.mem_map, decide_eq_true_eq] at hw
                  rcases hw with ⟨⟨y, hy', rfl⟩, hz⟩
                  exact ⟨⟨hx, ⟨y, hy', rfl⟩⟩, hz⟩
      · have hbc : ¬ Val.isSet (Val.cap b c) := by rw [Val.cap_not_set_right b hc]; exact fun h => h
        rw [Val.cap_not_set_right _ hc, Val.cap_not_set_right a hbc]
    · have hab : ¬ Val.isSet (Val.cap a b) := by rw [Val.cap_not_set_right a hb]; exact fun h => h
      have hbc : ¬ Val.isSet (Val.cap b c) := by rw [Val.cap_not_set_left hb c]; exact fun h => h
      rw [Val.cap_not_set_left hab c, Val.cap_not_set_right a hbc]
  · have hab : ¬ Val.isSet (Val.cap a b) := by rw [Val.cap_not_set_left ha b]; exact fun h => h
    rw [Val.cap_not_set_left hab c, Val.cap_not_set_left ha _]

inductive ACOp where
  | intAdd
  | intMul
  | setCup
  | setCap
  | boolAnd
  | boolOr

def seqIndicesAux {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] : Nat → Nat → List (Val sizes A)
  | _, 0 => []
  | i, n + 1 => Val.atom (HasNatAtom.natAtom i) :: seqIndicesAux (i + 1) n

def seqIndices {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (n : Nat) : List (Val sizes A) :=
  seqIndicesAux 1 n

private theorem seqIndicesAux_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) : ∀ (i n : Nat),
      (seqIndicesAux (sizes := sizes) (A := A) i n).map (renameVal p) = seqIndicesAux i n
  | _, 0 => rfl
  | i, n + 1 => by
    simp only [seqIndicesAux, List.map_cons, Val.rename_atom, seqIndicesAux_rename p (i + 1) n]

theorem seqIndices_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (n : Nat) :
    (seqIndices (sizes := sizes) (A := A) n).map (renameVal p) = seqIndices n :=
  seqIndicesAux_rename p 1 n

def Val.foldSeq {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (right onDomain : Bool) (s base : Val sizes A)
    (step : Val sizes A → Val sizes A → Val sizes A) : Val sizes A :=
  match Val.seqElems s with
  | some xs =>
    let items := if onDomain then seqIndices xs.length else xs
    if right then items.foldr step base
    else items.foldl (fun acc x => step x acc) base
  | none => Val.err

private theorem foldl_map_equiv {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (step step' : Val sizes A → Val sizes A → Val sizes A)
    (hstep : ∀ x acc, step' (renameVal p x) (renameVal p acc) = renameVal p (step x acc)) :
    ∀ (xs : List (Val sizes A)) (base : Val sizes A),
      (xs.map (renameVal p)).foldl (fun acc x => step' x acc) (renameVal p base) =
        renameVal p (xs.foldl (fun acc x => step x acc) base)
  | [], _ => rfl
  | x :: xs, base => by
    simp only [List.map_cons, List.foldl_cons, hstep x base]
    exact foldl_map_equiv p step step' hstep xs (step x base)

private theorem foldr_map_equiv {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (step step' : Val sizes A → Val sizes A → Val sizes A)
    (hstep : ∀ x acc, step' (renameVal p x) (renameVal p acc) = renameVal p (step x acc)) :
    ∀ (xs : List (Val sizes A)) (base : Val sizes A),
      (xs.map (renameVal p)).foldr step' (renameVal p base) =
        renameVal p (xs.foldr step base)
  | [], _ => rfl
  | x :: xs, base => by
    simp only [List.map_cons, List.foldr_cons, foldr_map_equiv p step step' hstep xs base, hstep x _]

theorem Val.foldSeq_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (right onDomain : Bool) (s base : Val sizes A)
    (step step' : Val sizes A → Val sizes A → Val sizes A)
    (hstep : ∀ x acc, step' (renameVal p x) (renameVal p acc) = renameVal p (step x acc)) :
    Val.foldSeq right onDomain (renameVal p s) (renameVal p base) step' =
      renameVal p (Val.foldSeq right onDomain s base step) := by
  unfold Val.foldSeq
  rw [Val.seqElems_rename]
  cases Val.seqElems s with
  | none => rfl
  | some xs =>
    simp only [Option.map_some, List.length_map]
    cases onDomain
    · cases right
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact foldl_map_equiv p step step' hstep xs base
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact foldr_map_equiv p step step' hstep xs base
    · have hind := seqIndices_rename (sizes := sizes) (A := A) p xs.length
      cases right
      · simp only [Bool.false_eq_true, ↓reduceIte]
        simpa only [hind] using foldl_map_equiv p step step' hstep (seqIndices xs.length) base
      · simp only [↓reduceIte]
        simpa only [hind] using foldr_map_equiv p step step' hstep (seqIndices xs.length) base

theorem Val.foldSeq_order {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (a b base : Val sizes A) (step : Val sizes A → Val sizes A → Val sizes A) :
    Val.foldSeq false false (Val.seq [a, b]) base step = step b (step a base) ∧
    Val.foldSeq true false (Val.seq [a, b]) base step = step a (step b base) := by
  simp only [Val.foldSeq, Val.seqElems_seq, Bool.false_eq_true, ↓reduceIte,
    List.foldl_cons, List.foldl_nil, List.foldr_cons, List.foldr_nil, and_self]

-- Atom-only operations (key-free leaves)
def collectAtoms {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] : List (Val sizes A) → Option (List A)
  | [] => some []
  | v :: vs =>
    match Val.asAtom v, collectAtoms vs with
    | some a, some as => some (a :: as)
    | _, _ => none

theorem collectAtoms_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (vs : List (Val sizes A)) :
    collectAtoms (vs.map (renameVal p)) = collectAtoms vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, collectAtoms, Val.asAtom_rename, ih]

def Val.allAtoms {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (s : Val sizes A) : Prop :=
  Val.isSet s ∧ ∀ v, Val.mem v s → (Val.asAtom v).isSome

theorem Val.allAtoms_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (s : Val sizes A) :
    Val.allAtoms (renameVal p s) ↔ Val.allAtoms s := by
  unfold Val.allAtoms
  rw [Val.isSet_rename]
  constructor
  · rintro ⟨hs, ha⟩
    refine ⟨hs, fun v hv => ?_⟩
    have := ha (renameVal p v) ((Val.mem_rename p v s).mpr hv)
    rwa [Val.asAtom_rename] at this
  · rintro ⟨hs, ha⟩
    refine ⟨hs, fun v hv => ?_⟩
    have hv' : Val.mem (renameVal p.inverse v) s := by
      have := (Val.mem_rename p (renameVal p.inverse v) s).mp
      rw [renameVal_right] at this
      exact this hv
    have := ha (renameVal p.inverse v) hv'
    rwa [Val.asAtom_rename] at this

-- Mutual AST for equivariant expressions, formulas, and set predicates
mutual
inductive Expr (d : Nat) (V : Type) where
  | err
  | atom (id : Nat)
  | var (v : V)
  | primeVar (v : V)
  | localVar (idx : Nat)
  | groupSet (mask : GroupMask d)
  | seqLit (elems : List (Expr d V))
  | setEnum (elems : List (Expr d V))
  | recLit (fields : List (Nat × Expr d V))
  | colonGt (k v : Expr d V)
  | atAt (f g : Expr d V)
  | fnApp (f arg : Expr d V)
  | domain (f : Expr d V)
  | except (base key rhs : Expr d V)
  | fnConstruct (dom body : Expr d V)
  | setFilter (dom : Expr d V) (pred : Form d V)
  | setMap (dom body : Expr d V)
  | cup (a b : Expr d V)
  | cap (a b : Expr d V)
  | setMinus (a b : Expr d V)
  | union (s : Expr d V)
  | powerset (s : Expr d V)
  | cartesian (sets : List (Expr d V))
  | fnSet (dom ran : Expr d V)
  | recSet (fields : List (Nat × Expr d V))
  | card (s : Expr d V)
  | len (s : Expr d V)
  | head (s : Expr d V)
  | tail (s : Expr d V)
  | append (s elem : Expr d V)
  | concat (a b : Expr d V)
  | subseq (s lo hi : Expr d V)
  | selectSeq (s : Expr d V) (pred : Form d V)
  | foldSeq (right onDomain : Bool) (seq base step : Expr d V)
  | foldSetAC (op : ACOp) (dom base elem : Expr d V)
  | copiesIn (elem bag : Expr d V)
  | bagCup (b1 b2 : Expr d V)
  | bagDiff (b1 b2 : Expr d V)
  | bagUnion (s : Expr d V)
  | bagCard (b : Expr d V)
  | bagOfAll (bag f : Expr d V)
  | foldBag (op : ACOp) (bag base : Expr d V)
  | ite (cond : Form d V) (yes no : Expr d V)
  | letBind (val body : Expr d V)
  | ofForm (f : Form d V)
  | atomOp (id : Nat) (args : List (Expr d V))
  | atomSetOp (id : Nat) (args : List (Expr d V))
  | atomSetAgg (id : Nat) (s : Expr d V)
  | atomChoose (dom : Expr d V) (pred : Form d V)

inductive Form (d : Nat) (V : Type) where
  | truth (b : Bool)
  | ofExpr (e : Expr d V)
  | eq (a b : Expr d V)
  | mem (elem : Expr d V) (set : SetPred d V)
  | subsetEq (sub : Expr d V) (sup : SetPred d V)
  | isFiniteSet (e : Expr d V)
  | isABag (b : Expr d V)
  | bagIn (elem bag : Expr d V)
  | sqSubseteq (b1 b2 : Expr d V)
  | conj (a b : Form d V)
  | disj (a b : Form d V)
  | neg (a : Form d V)
  | impl (a b : Form d V)
  | iff (a b : Form d V)
  | ite (cond yes no : Form d V)
  | letBind (val : Expr d V) (body : Form d V)
  | all (dom : SetPred d V) (body : Form d V)
  | some (dom : SetPred d V) (body : Form d V)
  | atomRel (id : Nat) (args : List (Expr d V))

inductive SetPred (d : Nat) (V : Type) where
  | expr (e : Expr d V)
  | atomPred (id : Nat)
  | group (mask : GroupMask d)
  | enum (elems : List (Expr d V))
  | cup (a b : SetPred d V)
  | cap (a b : SetPred d V)
  | diff (a b : SetPred d V)
  | subset (p : SetPred d V)
  | seq (p : SetPred d V)
  | times (ps : List (SetPred d V))
  | fnSet (dom ran : SetPred d V)
  | recSet (fields : List (Nat × SetPred d V))
  | filter (dom : SetPred d V) (pred : Form d V)
end

abbrev Env {d : Nat} (sizes : Fin d → Nat) (A : Type) [HasNatAtom A] := Nat → Val sizes A
abbrev State (V : Type) {d : Nat} (sizes : Fin d → Nat) (A : Type) [HasNatAtom A] := V → Val sizes A

def push {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (env : Env sizes A) (v : Val sizes A) : Env sizes A
  | 0 => v
  | i + 1 => env i

def renameEnv {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) (env : Env sizes A) :
    Env sizes A :=
  fun i => renameVal p (env i)

theorem renameEnv_push {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (env : Env sizes A) (v : Val sizes A) :
    renameEnv p (push env v) = push (renameEnv p env) (renameVal p v) := by
  funext i
  cases i <;> rfl

def renameState {V : Type} {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (s : State V sizes A) : State V sizes A :=
  fun v => renameVal p (s v)

theorem renameState_identity {V : Type} {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (s : State V sizes A) :
    renameState GroupPerm.identity s = s := by
  funext v; exact renameVal_identity (s v)

theorem renameState_then {V : Type} {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p q : GroupPerm sizes) (s : State V sizes A) :
    renameState (p.then q) s = renameState q (renameState p s) := by
  funext v; exact renameVal_then p q (s v)

theorem renameState_inverse {V : Type} {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (s : State V sizes A) :
    renameState p.inverse (renameState p s) = s := by
  funext v; exact renameVal_inverse p (s v)

structure AtomOps (A : Type) where
  atomVal : Nat → A
  boolAtom : Bool → A
  intAtom : Int → A
  isTrue : A → Prop
  intOf : A → Option Int
  atomOp : Nat → List A → A
  atomSetOp : Nat → List A → List A
  atomSetAgg : Nat → (A → Prop) → A
  chooseAtom : (A → Prop) → A
  atomRel : Nat → List A → Prop
  atomPred : Nat → A → Prop

def valInt {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (v : Val sizes A) : Option Int :=
  (Val.asAtom v).bind ops.intOf

theorem valInt_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (v : Val sizes A) :
    valInt ops (renameVal p v) = valInt ops v := by
  simp only [valInt, Val.asAtom_rename]

def valBool {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (v : Val sizes A) : Option Bool :=
  (Val.asAtom v).map (fun a => @decide (ops.isTrue a) (Classical.propDecidable _))

theorem valBool_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (v : Val sizes A) :
    valBool ops (renameVal p v) = valBool ops v := by
  simp only [valBool, Val.asAtom_rename]

def foldScalarAC {d : Nat} {sizes : Fin d → Nat} {A α : Type} [HasNatAtom A]
    (decode : Val sizes A → Option α) (encode : α → A) (combine : α → α → α)
    (base : Val sizes A) (vals : List (Val sizes A)) : Val sizes A :=
  match vals.foldl (fun acc v => match acc, decode v with | some a, some x => some (combine a x) | _, _ => none) (decode base) with
  | some r => Val.atom (encode r)
  | none => Val.err

private theorem foldScalarAC_perm {d : Nat} {sizes : Fin d → Nat} {A α : Type} [HasNatAtom A]
    (decode : Val sizes A → Option α) (encode : α → A) (combine : α → α → α)
    (hcomm : ∀ acc x y, combine (combine acc x) y = combine (combine acc y) x)
    (base : Val sizes A) {l1 l2 : List (Val sizes A)} (hp : l1.Perm l2) :
    foldScalarAC decode encode combine base l1 = foldScalarAC decode encode combine base l2 := by
  unfold foldScalarAC
  have hswap : ∀ x ∈ l1, ∀ y ∈ l1, ∀ acc : Option α,
      (match (match acc, decode x with | some a, some b => some (combine a b) | _, _ => none), decode y with
       | some a, some b => some (combine a b) | _, _ => none) =
      (match (match acc, decode y with | some a, some b => some (combine a b) | _, _ => none), decode x with
       | some a, some b => some (combine a b) | _, _ => none) := by
    intro x _ y _ acc
    cases acc with
    | none => rfl
    | some a =>
      cases decode x with
      | none => cases decode y <;> rfl
      | some bx =>
        cases decode y with
        | none => rfl
        | some by' => exact congrArg some (hcomm a bx by')
  rw [hp.foldl_eq' hswap (decode base)]

private theorem foldScalarAC_rename {d : Nat} {sizes : Fin d → Nat} {A α : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (decode : Val sizes A → Option α) (encode : α → A) (combine : α → α → α)
    (hdec : ∀ v, decode (renameVal p v) = decode v)
    (base : Val sizes A) (vals : List (Val sizes A)) :
    foldScalarAC decode encode combine (renameVal p base) (vals.map (renameVal p)) =
      renameVal p (foldScalarAC decode encode combine base vals) := by
  unfold foldScalarAC
  have hfold : ∀ (xs : List (Val sizes A)) (acc : Option α),
      (xs.map (renameVal p)).foldl (fun a v => match a, decode v with | some a, some x => some (combine a x) | _, _ => none) acc =
        xs.foldl (fun a v => match a, decode v with | some a, some x => some (combine a x) | _, _ => none) acc := by
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons x t ih =>
      intro acc
      simp only [List.map_cons, List.foldl_cons, hdec x]
      exact ih _
  rw [hdec base, hfold vals (decode base)]
  cases vals.foldl (fun a v => match a, decode v with | some a, some x => some (combine a x) | _, _ => none) (decode base) <;> rfl

def foldSetACList {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (op : ACOp) (base : Val sizes A) (vals : List (Val sizes A)) : Val sizes A :=
  match op with
  | .intAdd => foldScalarAC (valInt ops) ops.intAtom (· + ·) base vals
  | .intMul => foldScalarAC (valInt ops) ops.intAtom (· * ·) base vals
  | .boolAnd => foldScalarAC (valBool ops) ops.boolAtom (· && ·) base vals
  | .boolOr => foldScalarAC (valBool ops) ops.boolAtom (· || ·) base vals
  | .setCup => vals.foldl (fun acc x => Val.cup x acc) base
  | .setCap => vals.foldl (fun acc x => Val.cap x acc) base

private theorem foldSetACList_perm {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (op : ACOp) (base : Val sizes A)
    {l1 l2 : List (Val sizes A)} (hp : l1.Perm l2) :
    foldSetACList ops op base l1 = foldSetACList ops op base l2 := by
  cases op with
  | intAdd =>
    exact foldScalarAC_perm (valInt ops) ops.intAtom (· + ·) (fun acc x y => by omega) base hp
  | intMul =>
    exact foldScalarAC_perm (valInt ops) ops.intAtom (· * ·) (fun acc x y => by rw [Int.mul_assoc, Int.mul_comm x y, ← Int.mul_assoc]) base hp
  | boolAnd =>
    exact foldScalarAC_perm (valBool ops) ops.boolAtom (· && ·) (fun acc x y => by cases acc <;> cases x <;> cases y <;> rfl) base hp
  | boolOr =>
    exact foldScalarAC_perm (valBool ops) ops.boolAtom (· || ·) (fun acc x y => by cases acc <;> cases x <;> cases y <;> rfl) base hp
  | setCup =>
    exact hp.foldl_eq' (fun x _ y _ acc => by rw [← Val.cup_assoc, Val.cup_comm y x, Val.cup_assoc]) base
  | setCap =>
    exact hp.foldl_eq' (fun x _ y _ acc => by rw [← Val.cap_assoc, Val.cap_comm y x, Val.cap_assoc]) base

private theorem foldSetACList_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (op : ACOp) (base : Val sizes A) (vals : List (Val sizes A)) :
    foldSetACList ops op (renameVal p base) (vals.map (renameVal p)) =
      renameVal p (foldSetACList ops op base vals) := by
  cases op with
  | intAdd => exact foldScalarAC_rename p (valInt ops) ops.intAtom (· + ·) (valInt_rename p ops) base vals
  | intMul => exact foldScalarAC_rename p (valInt ops) ops.intAtom (· * ·) (valInt_rename p ops) base vals
  | boolAnd => exact foldScalarAC_rename p (valBool ops) ops.boolAtom (· && ·) (valBool_rename p ops) base vals
  | boolOr => exact foldScalarAC_rename p (valBool ops) ops.boolAtom (· || ·) (valBool_rename p ops) base vals
  | setCup => exact foldl_map_equiv p Val.cup Val.cup (Val.cup_rename p) vals base
  | setCap => exact foldl_map_equiv p Val.cap Val.cap (Val.cap_rename p) vals base

def Val.foldSetAC {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (op : ACOp) (s base : Val sizes A) (f : Val sizes A → Val sizes A) : Val sizes A := by
  classical
  exact Quotient.liftOn s (fun sr => match sr with
    | .set xs => foldSetACList ops op base ((dedupList (xs.map mkVal)).map f)
    | _ => Val.err)
    (lift_set_sound (fallback := Val.err) (by
      intro xs ys h
      have hperm : (dedupList (xs.map mkVal)).Perm (dedupList (ys.map mkVal)) :=
        (List.perm_ext_iff_of_nodup (nodup_dedupList _) (nodup_dedupList _)).mpr (fun v => by
          simp only [mem_dedupList, List.mem_map]
          rcases ValEq.set_iff.mp h with ⟨h1, h2⟩
          constructor
          · rintro ⟨a, ha, rfl⟩
            rcases h1 a ha with ⟨b, hb, hab⟩
            exact ⟨b, hb, (Quotient.sound hab).symm⟩
          · rintro ⟨b, hb, rfl⟩
            rcases h2 b hb with ⟨a, ha, hab⟩
            exact ⟨a, ha, Quotient.sound hab⟩)
      exact foldSetACList_perm ops op base (hperm.map f)))

theorem Val.foldSetAC_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (op : ACOp) (s base : Val sizes A)
    (f f' : Val sizes A → Val sizes A)
    (hf : ∀ v, f' (renameVal p v) = renameVal p (f v)) :
    Val.foldSetAC ops op (renameVal p s) (renameVal p base) f' =
      renameVal p (Val.foldSetAC ops op s base f) := by
  classical
  induction s using Quotient.ind with
  | _ sr =>
    cases sr with
    | set xs =>
      change foldSetACList ops op (renameVal p base) ((dedupList ((renameRawList p xs).map mkVal)).map f') =
        renameVal p (foldSetACList ops op base ((dedupList (xs.map mkVal)).map f))
      have hnd1 := nodup_dedupList ((renameRawList p xs).map mkVal)
      have hnd2 := nodup_map_inj (fun _ _ h => (renameVal_injective p).mp h) (nodup_dedupList (xs.map mkVal))
      have hperm : (dedupList ((renameRawList p xs).map mkVal)).Perm ((dedupList (xs.map mkVal)).map (renameVal p)) :=
        (List.perm_ext_iff_of_nodup hnd1 hnd2).mpr (fun w => by
          simp only [mem_dedupList, renameRawList_eq_map, List.mem_map]
          constructor
          · rintro ⟨y', ⟨y, hy, rfl⟩, rfl⟩
            exact ⟨mkVal y, ⟨y, hy, rfl⟩, rfl⟩
          · rintro ⟨v, ⟨y, hy, rfl⟩, rfl⟩
            exact ⟨renameRaw p y, ⟨y, hy, rfl⟩, rfl⟩)
      rw [foldSetACList_perm ops op (renameVal p base) (hperm.map f')]
      have hmap : ((dedupList (xs.map mkVal)).map (renameVal p)).map f' =
          ((dedupList (xs.map mkVal)).map f).map (renameVal p) := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro v _
        exact hf v
      rw [hmap]
      exact foldSetACList_rename p ops op base ((dedupList (xs.map mkVal)).map f)
    | _ => rfl

theorem Val.foldSetAC_intAdd_dup_mapped {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (h0 : ops.intOf (ops.intAtom 0) = some 0) (h1 : ops.intOf (ops.intAtom 1) = some 1) :
    Val.foldSetAC ops .intAdd
      (Val.set (sizes := sizes) [Val.atom (HasNatAtom.natAtom 0), Val.atom (HasNatAtom.natAtom 1)])
      (Val.atom (ops.intAtom 0))
      (fun _ => Val.atom (ops.intAtom 1)) =
    Val.atom (ops.intAtom 2) := by
  classical
  have hne : Val.atom (sizes := sizes) (HasNatAtom.natAtom (A := A) 0) ≠
      Val.atom (HasNatAtom.natAtom (A := A) 1) := by
    intro h
    have h01 : (0 : Nat) = 1 := HasNatAtom.natAtom_inj 0 1 (Val.atom_inj h)
    cases h01
  change foldSetACList ops .intAdd (Val.atom (ops.intAtom 0))
    ((dedupList ((List.map valOut [Val.atom (HasNatAtom.natAtom 0), Val.atom (HasNatAtom.natAtom 1)]).map mkVal)).map
      (fun _ => Val.atom (ops.intAtom 1))) = Val.atom (ops.intAtom 2)
  have hv0 : valInt (sizes := sizes) ops (Val.atom (ops.intAtom 0)) = some 0 := h0
  have hv1 : valInt (sizes := sizes) ops (Val.atom (ops.intAtom 1)) = some 1 := h1
  simp only [List.map_cons, List.map_nil, valOut_eq, dedupList, List.mem_singleton, hne, ↓reduceIte,
    List.not_mem_nil, foldSetACList, foldScalarAC, hv0, hv1, List.foldl_cons, List.foldl_nil]
  rfl

-- Multiset (Bags / BagsExt) operations on Val
def Val.isABag {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (v : Val sizes A) : Prop :=
  Val.isFn v ∧ ∀ k w, Val.mapsTo v k w → ∃ n : Int, valInt ops w = some n ∧ n > 0

theorem Val.isABag_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (v : Val sizes A) :
    Val.isABag ops (renameVal p v) ↔ Val.isABag ops v := by
  unfold Val.isABag
  apply and_congr (Val.isFn_rename p v)
  constructor
  · intro h k w hkw
    have h' := h (renameVal p k) (renameVal p w) ((Val.mapsTo_rename p v k w).mpr hkw)
    rwa [valInt_rename] at h'
  · intro h k w hkw
    have hkw' : Val.mapsTo v (renameVal p.inverse k) (renameVal p.inverse w) := by
      have := (Val.mapsTo_rename p v (renameVal p.inverse k) (renameVal p.inverse w)).mp
      rw [renameVal_right, renameVal_right] at this
      exact this hkw
    have h' := h _ _ hkw'
    rwa [valInt_rename] at h'

def Val.bagCountOpt {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (b k : Val sizes A) : Option Int :=
  match Val.fnLookup b k with
  | some w => valInt ops w
  | none => some 0

theorem Val.bagCountOpt_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (b k : Val sizes A) :
    Val.bagCountOpt ops (renameVal p b) (renameVal p k) = Val.bagCountOpt ops b k := by
  unfold Val.bagCountOpt
  rw [Val.fnLookup_rename]
  cases Val.fnLookup b k with
  | none => rfl
  | some w => simp only [Option.map_some, valInt_rename]

def Val.bagIn {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (e b : Val sizes A) : Prop :=
  Val.isFn b ∧ ∃ n : Int, (Val.fnLookup b e).bind (valInt ops) = some n ∧ n > 0

theorem Val.bagIn_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (e b : Val sizes A) :
    Val.bagIn ops (renameVal p e) (renameVal p b) ↔ Val.bagIn ops e b := by
  unfold Val.bagIn
  rw [Val.isFn_rename, Val.fnLookup_rename]
  cases Val.fnLookup b e with
  | none => rfl
  | some w => simp only [Option.map_some, Option.bind_some, valInt_rename]

def Val.copiesIn {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (e b : Val sizes A) : Val sizes A :=
  @ite _ (Val.isFn b) (Classical.propDecidable _)
    (match Val.bagCountOpt ops b e with
     | some n => Val.atom (ops.intAtom n)
     | none => Val.err)
    Val.err

theorem Val.copiesIn_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (e b : Val sizes A) :
    Val.copiesIn ops (renameVal p e) (renameVal p b) = renameVal p (Val.copiesIn ops e b) := by
  unfold Val.copiesIn
  rw [propext (Val.isFn_rename p b), Val.bagCountOpt_rename]
  split
  · cases Val.bagCountOpt ops b e <;> rfl
  · rfl

def Val.sqSubseteq {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (b1 b2 : Val sizes A) : Prop :=
  Val.isFn b1 ∧ Val.isFn b2 ∧
  ∀ k w1, Val.mapsTo b1 k w1 →
    ∃ c1 c2 : Int, valInt ops w1 = some c1 ∧ Val.bagCountOpt ops b2 k = some c2 ∧ c1 ≤ c2

theorem Val.sqSubseteq_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (b1 b2 : Val sizes A) :
    Val.sqSubseteq ops (renameVal p b1) (renameVal p b2) ↔ Val.sqSubseteq ops b1 b2 := by
  unfold Val.sqSubseteq
  apply and_congr (Val.isFn_rename p b1)
  apply and_congr (Val.isFn_rename p b2)
  constructor
  · intro h k w1 hkw
    have h' := h (renameVal p k) (renameVal p w1) ((Val.mapsTo_rename p b1 k w1).mpr hkw)
    rwa [valInt_rename, Val.bagCountOpt_rename] at h'
  · intro h k w1 hkw
    have hkw' : Val.mapsTo b1 (renameVal p.inverse k) (renameVal p.inverse w1) := by
      have := (Val.mapsTo_rename p b1 (renameVal p.inverse k) (renameVal p.inverse w1)).mp
      rw [renameVal_right, renameVal_right] at this
      exact this hkw
    have h' := h _ _ hkw'
    have hbc : Val.bagCountOpt ops (renameVal p b2) k = Val.bagCountOpt ops b2 (renameVal p.inverse k) := by
      have := Val.bagCountOpt_rename p ops b2 (renameVal p.inverse k)
      rwa [renameVal_right] at this
    rwa [valInt_rename, ← hbc] at h'

def Val.bagCup {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (b1 b2 : Val sizes A) : Val sizes A :=
  @ite _ (Val.isABag ops b1 ∧ Val.isABag ops b2) (Classical.propDecidable _)
    (Val.fnConstruct (Val.cup (Val.domain b1) (Val.domain b2)) (fun k =>
      match Val.bagCountOpt ops b1 k, Val.bagCountOpt ops b2 k with
      | some c1, some c2 => Val.atom (ops.intAtom (c1 + c2))
      | _, _ => Val.err))
    Val.err

theorem Val.bagCup_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (b1 b2 : Val sizes A) :
    Val.bagCup ops (renameVal p b1) (renameVal p b2) = renameVal p (Val.bagCup ops b1 b2) := by
  unfold Val.bagCup
  rw [propext (and_congr (Val.isABag_rename p ops b1) (Val.isABag_rename p ops b2))]
  split
  · rw [Val.domain_rename, Val.domain_rename, Val.cup_rename]
    exact Val.fnConstruct_rename p _ _ _ (fun k => by
      rw [Val.bagCountOpt_rename, Val.bagCountOpt_rename]
      cases Val.bagCountOpt ops b1 k <;> cases Val.bagCountOpt ops b2 k <;> rfl)
  · rfl

def Val.bagDiff {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (b1 b2 : Val sizes A) : Val sizes A :=
  @ite _ (Val.isFn b1 ∧ Val.isFn b2) (Classical.propDecidable _)
    (Val.fnConstruct
      (Val.setFilter (Val.domain b1) (fun k =>
        match Val.bagCountOpt ops b1 k, Val.bagCountOpt ops b2 k with
        | some c1, some c2 => c1 - c2 > 0
        | _, _ => False))
      (fun k =>
        match Val.bagCountOpt ops b1 k, Val.bagCountOpt ops b2 k with
        | some c1, some c2 => Val.atom (ops.intAtom (c1 - c2))
        | _, _ => Val.err))
    Val.err

theorem Val.bagDiff_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (b1 b2 : Val sizes A) :
    Val.bagDiff ops (renameVal p b1) (renameVal p b2) = renameVal p (Val.bagDiff ops b1 b2) := by
  unfold Val.bagDiff
  rw [propext (and_congr (Val.isFn_rename p b1) (Val.isFn_rename p b2))]
  split
  · rw [Val.domain_rename]
    have hfilt := Val.setFilter_rename p (Val.domain b1)
      (fun k => match Val.bagCountOpt ops b1 k, Val.bagCountOpt ops b2 k with | some c1, some c2 => c1 - c2 > 0 | _, _ => False)
      (fun k => match Val.bagCountOpt ops (renameVal p b1) k, Val.bagCountOpt ops (renameVal p b2) k with | some c1, some c2 => c1 - c2 > 0 | _, _ => False)
      (fun k => by rw [Val.bagCountOpt_rename, Val.bagCountOpt_rename])
    rw [hfilt]
    exact Val.fnConstruct_rename p _ _ _ (fun k => by
      rw [Val.bagCountOpt_rename, Val.bagCountOpt_rename]
      cases Val.bagCountOpt ops b1 k <;> cases Val.bagCountOpt ops b2 k <;> rfl)
  · rfl

def Val.bagCard {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (b : Val sizes A) : Val sizes A :=
  @ite _ (Val.isABag ops b) (Classical.propDecidable _)
    (Val.foldSetAC ops .intAdd (Val.domain b) (Val.atom (ops.intAtom 0)) (fun k => Val.apply b k))
    Val.err

theorem Val.bagCard_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (b : Val sizes A) :
    Val.bagCard ops (renameVal p b) = renameVal p (Val.bagCard ops b) := by
  unfold Val.bagCard
  rw [propext (Val.isABag_rename p ops b)]
  split
  · rw [Val.domain_rename]
    exact Val.foldSetAC_rename p ops .intAdd (Val.domain b) (Val.atom (ops.intAtom 0))
      (fun k => Val.apply b k) (fun k => Val.apply (renameVal p b) k)
      (fun k => Val.apply_rename p b k)
  · rfl

def Val.bagUnion {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (s : Val sizes A) : Val sizes A :=
  @ite _ (Val.isSet s ∧ ∀ b, Val.mem b s → Val.isABag ops b) (Classical.propDecidable _)
    (Val.fnConstruct (Val.union (Val.setMap s Val.domain)) (fun k =>
      Val.foldSetAC ops .intAdd s (Val.atom (ops.intAtom 0)) (fun b => Val.copiesIn ops k b)))
    Val.err

theorem Val.bagUnion_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (s : Val sizes A) :
    Val.bagUnion ops (renameVal p s) = renameVal p (Val.bagUnion ops s) := by
  unfold Val.bagUnion
  have hcond : (Val.isSet (renameVal p s) ∧ ∀ b, Val.mem b (renameVal p s) → Val.isABag ops b) ↔
      (Val.isSet s ∧ ∀ b, Val.mem b s → Val.isABag ops b) := by
    apply and_congr (Val.isSet_rename p s)
    constructor
    · intro h b hb
      exact (Val.isABag_rename p ops b).mp (h (renameVal p b) ((Val.mem_rename p b s).mpr hb))
    · intro h b hb
      have hb' : Val.mem (renameVal p.inverse b) s := by
        have := (Val.mem_rename p (renameVal p.inverse b) s).mp
        rw [renameVal_right] at this
        exact this hb
      have := (Val.isABag_rename p ops (renameVal p.inverse b)).mpr (h _ hb')
      rwa [renameVal_right] at this
  rw [propext hcond]
  split
  · have hdom : Val.union (Val.setMap (renameVal p s) Val.domain) = renameVal p (Val.union (Val.setMap s Val.domain)) := by
      rw [Val.setMap_rename p s Val.domain Val.domain (Val.domain_rename p), Val.union_rename]
    rw [hdom]
    exact Val.fnConstruct_rename p _ _ _ (fun k =>
      Val.foldSetAC_rename p ops .intAdd s (Val.atom (ops.intAtom 0))
        (fun b => Val.copiesIn ops k b)
        (fun b => Val.copiesIn ops (renameVal p k) b)
        (fun b => Val.copiesIn_rename p ops k b))
  · rfl

def Val.bagOfAll {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (f : Val sizes A → Val sizes A) (b : Val sizes A) : Val sizes A :=
  @ite _ (Val.isABag ops b) (Classical.propDecidable _)
    (Val.fnConstruct (Val.setMap (Val.domain b) f) (fun y =>
      Val.foldSetAC ops .intAdd (Val.setFilter (Val.domain b) (fun k => f k = y))
        (Val.atom (ops.intAtom 0)) (fun k => Val.apply b k)))
    Val.err

theorem Val.bagOfAll_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (f f' : Val sizes A → Val sizes A)
    (hf : ∀ v, f' (renameVal p v) = renameVal p (f v)) (b : Val sizes A) :
    Val.bagOfAll ops f' (renameVal p b) = renameVal p (Val.bagOfAll ops f b) := by
  unfold Val.bagOfAll
  rw [propext (Val.isABag_rename p ops b)]
  split
  · rw [Val.domain_rename, Val.setMap_rename p (Val.domain b) f f' hf]
    exact Val.fnConstruct_rename p _ _ _ (fun y => by
      have hfilt := Val.setFilter_rename p (Val.domain b)
        (fun k => f k = y) (fun k => f' k = renameVal p y)
        (fun k => by rw [hf k, renameVal_injective])
      rw [hfilt]
      exact Val.foldSetAC_rename p ops .intAdd _ (Val.atom (ops.intAtom 0))
        (fun k => Val.apply b k) (fun k => Val.apply (renameVal p b) k)
        (fun k => Val.apply_rename p b k))
  · rfl

private theorem perm_flatMap {α β : Type} (g : α → List β) {l1 l2 : List α} (hp : l1.Perm l2) :
    (l1.flatMap g).Perm (l2.flatMap g) := by
  induction hp with
  | nil => exact List.Perm.nil
  | cons x _ ih => exact List.Perm.append_left (g x) ih
  | swap x y l =>
    simp only [List.flatMap_cons, ← List.append_assoc]
    exact List.Perm.append_right (l.flatMap g) List.perm_append_comm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private def foldBagDom {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (op : ACOp) (b base dVal : Val sizes A) : Val sizes A := by
  classical
  exact Quotient.liftOn dVal (fun sr => match sr with
    | .set xs =>
      foldSetACList ops op base
        ((dedupList (xs.map mkVal)).flatMap (fun k =>
          match (Val.fnLookup b k).bind (valInt ops) with
          | some n => List.replicate n.toNat k
          | none => []))
    | _ => Val.err)
    (lift_set_sound (fallback := Val.err) (by
      intro xs ys h
      have hperm : (dedupList (xs.map mkVal)).Perm (dedupList (ys.map mkVal)) :=
        (List.perm_ext_iff_of_nodup (nodup_dedupList _) (nodup_dedupList _)).mpr (fun v => by
          simp only [mem_dedupList, List.mem_map]
          rcases ValEq.set_iff.mp h with ⟨h1, h2⟩
          constructor
          · rintro ⟨a, ha, rfl⟩
            rcases h1 a ha with ⟨c, hc, hac⟩
            exact ⟨c, hc, (Quotient.sound hac).symm⟩
          · rintro ⟨c, hc, rfl⟩
            rcases h2 c hc with ⟨a, ha, hac⟩
            exact ⟨a, ha, Quotient.sound hac⟩)
      exact foldSetACList_perm ops op base (perm_flatMap _ hperm)))

private theorem foldBagDom_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (op : ACOp) (b base dVal : Val sizes A) :
    foldBagDom ops op (renameVal p b) (renameVal p base) (renameVal p dVal) =
      renameVal p (foldBagDom ops op b base dVal) := by
  classical
  induction dVal using Quotient.ind with
  | _ sr =>
    cases sr with
    | set xs =>
      change foldSetACList ops op (renameVal p base)
        ((dedupList ((renameRawList p xs).map mkVal)).flatMap _) =
        renameVal p (foldSetACList ops op base ((dedupList (xs.map mkVal)).flatMap _))
      have hnd1 := nodup_dedupList ((renameRawList p xs).map mkVal)
      have hnd2 := nodup_map_inj (fun _ _ h => (renameVal_injective p).mp h) (nodup_dedupList (xs.map mkVal))
      have hperm : (dedupList ((renameRawList p xs).map mkVal)).Perm ((dedupList (xs.map mkVal)).map (renameVal p)) :=
        (List.perm_ext_iff_of_nodup hnd1 hnd2).mpr (fun w => by
          simp only [mem_dedupList, renameRawList_eq_map, List.mem_map]
          constructor
          · rintro ⟨y', ⟨y, hy, rfl⟩, rfl⟩; exact ⟨mkVal y, ⟨y, hy, rfl⟩, rfl⟩
          · rintro ⟨v, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨renameRaw p y, ⟨y, hy, rfl⟩, rfl⟩)
      rw [foldSetACList_perm ops op (renameVal p base) (perm_flatMap _ hperm)]
      have hfm : ((dedupList (xs.map mkVal)).map (renameVal p)).flatMap
          (fun k => match (Val.fnLookup (renameVal p b) k).bind (valInt ops) with
            | some n => List.replicate n.toNat k
            | none => []) =
          ((dedupList (xs.map mkVal)).flatMap (fun k =>
            match (Val.fnLookup b k).bind (valInt ops) with
            | some n => List.replicate n.toNat k
            | none => [])).map (renameVal p) := by
        rw [List.flatMap_map, List.map_flatMap]
        congr 1
        funext k
        rw [Val.fnLookup_rename]
        cases Val.fnLookup b k with
        | none => rfl
        | some w =>
          simp only [Option.map_some, Option.bind_some, valInt_rename]
          cases valInt ops w with
          | none => rfl
          | some n => rw [List.map_replicate]
      rw [hfm]
      exact foldSetACList_rename p ops op base _
    | _ => rfl

def Val.foldBag {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (op : ACOp) (b base : Val sizes A) : Val sizes A :=
  @ite _ (Val.isABag ops b) (Classical.propDecidable _)
    (foldBagDom ops op b base (Val.domain b))
    Val.err

theorem Val.foldBag_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (op : ACOp) (b base : Val sizes A) :
    Val.foldBag ops op (renameVal p b) (renameVal p base) = renameVal p (Val.foldBag ops op b base) := by
  unfold Val.foldBag
  rw [propext (Val.isABag_rename p ops b)]
  split
  · rw [Val.domain_rename]
    exact foldBagDom_rename p ops op b base (Val.domain b)
  · rfl

private theorem Val.fnLookup_singleton {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (k v : Val sizes A) :
    Val.fnLookup (Val.fn [(k, v)]) k = some v := by
  classical
  have hm : Val.mapsTo (Val.fn [(k, v)]) k v := by
    change ∃ kv ∈ [(valOut k, valOut v)], mkVal kv.1 = k ∧ mkVal kv.2 = v
    exact ⟨(valOut k, valOut v), List.mem_cons_self, valOut_eq k, valOut_eq v⟩
  have hu : ∀ w, Val.mapsTo (Val.fn [(k, v)]) k w → w = v := by
    intro w hw
    rcases hw with ⟨kv, hkv, _, h2⟩
    rcases List.mem_singleton.mp hkv with rfl
    exact h2.symm.trans (valOut_eq v)
  have hex : ∃ x, Val.mapsTo (Val.fn [(k, v)]) k x ∧ ∀ w, Val.mapsTo (Val.fn [(k, v)]) k w → w = x := ⟨v, hm, hu⟩
  unfold Val.fnLookup
  simp only [hex, ↓reduceDIte]
  congr 1
  exact hu _ (Classical.choose_spec hex).1

theorem Val.bagDiff_drops_zero {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (k : Val sizes A) (h1 : ops.intOf (ops.intAtom 1) = some 1) :
    Val.bagDiff ops (Val.fn [(k, Val.atom (ops.intAtom 1))]) (Val.fn [(k, Val.atom (ops.intAtom 1))]) = Val.fn [] := by
  classical
  have hfn : Val.isFn (Val.fn [(k, Val.atom (ops.intAtom 1))]) := rfl
  have hbc : Val.bagCountOpt ops (Val.fn [(k, Val.atom (ops.intAtom 1))]) k = some 1 := by
    unfold Val.bagCountOpt
    rw [Val.fnLookup_singleton]
    exact h1
  unfold Val.bagDiff
  simp only [hfn, and_self, ↓reduceIte]
  have hdom : Val.domain (Val.fn [(k, Val.atom (ops.intAtom 1))]) = Val.set [k] := by
    change Val.set [mkVal (valOut k)] = Val.set [k]
    rw [valOut_eq]
  rw [hdom]
  have hfilt : Val.setFilter (Val.set [k]) (fun x =>
      match Val.bagCountOpt ops (Val.fn [(k, Val.atom (ops.intAtom 1))]) x,
            Val.bagCountOpt ops (Val.fn [(k, Val.atom (ops.intAtom 1))]) x with
      | some c1, some c2 => c1 - c2 > 0
      | _, _ => False) = Val.set [] := by
    change Val.set (([mkVal (valOut k)]).filter _) = Val.set []
    rw [valOut_eq, List.filter_cons, List.filter_nil]
    have h00 : ¬ ((0 : Int) > 0) := by omega
    simp only [hbc, Int.sub_self, h00, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [hfilt]
  rfl

theorem Val.bagCard_counts_copies {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A) (k : Val sizes A)
    (h0 : ops.intOf (ops.intAtom 0) = some 0) (h2 : ops.intOf (ops.intAtom 2) = some 2) :
    Val.bagCard ops (Val.fn [(k, Val.atom (ops.intAtom 2))]) = Val.atom (ops.intAtom 2) := by
  classical
  have hbag : Val.isABag ops (Val.fn [(k, Val.atom (ops.intAtom 2))]) := by
    refine ⟨rfl, fun x w hxw => ?_⟩
    rcases hxw with ⟨kv, hkv, _, hw⟩
    rcases List.mem_singleton.mp hkv with rfl
    rw [valOut_eq] at hw
    rw [← hw]
    exact ⟨2, h2, by omega⟩
  have hdom : Val.domain (Val.fn [(k, Val.atom (ops.intAtom 2))]) = Val.set [k] := by
    change Val.set [mkVal (valOut k)] = Val.set [k]
    rw [valOut_eq]
  have happ : Val.apply (Val.fn [(k, Val.atom (ops.intAtom 2))]) k = Val.atom (ops.intAtom 2) := by
    unfold Val.apply
    rw [Val.fnLookup_singleton]
    rfl
  unfold Val.bagCard
  simp only [hbag, ↓reduceIte, hdom]
  change foldSetACList ops .intAdd (Val.atom (ops.intAtom 0))
    ((dedupList ((List.map valOut [k]).map mkVal)).map (fun x => Val.apply (Val.fn [(k, Val.atom (ops.intAtom 2))]) x)) =
    Val.atom (ops.intAtom 2)
  have hv0 : valInt (sizes := sizes) ops (Val.atom (ops.intAtom 0)) = some 0 := h0
  have hv2 : valInt (sizes := sizes) ops (Val.atom (ops.intAtom 2)) = some 2 := h2
  simp only [List.map_cons, List.map_nil, valOut_eq, dedupList, List.not_mem_nil, ↓reduceIte,
    happ, foldSetACList, foldScalarAC, hv0, hv2, List.foldl_cons, List.foldl_nil]
  rfl

theorem Val.foldBag_counts_multiplicity {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (ops : AtomOps A)
    (h0 : ops.intOf (ops.intAtom 0) = some 0)
    (h1 : ops.intOf (ops.intAtom 1) = some 1)
    (h2 : ops.intOf (ops.intAtom 2) = some 2) :
    Val.foldBag (sizes := sizes) ops .intAdd
      (Val.fn [(Val.atom (ops.intAtom 1), Val.atom (ops.intAtom 2))])
      (Val.atom (ops.intAtom 0)) = Val.atom (ops.intAtom 2) := by
  classical
  have hbag : Val.isABag (sizes := sizes) ops (Val.fn [(Val.atom (ops.intAtom 1), Val.atom (ops.intAtom 2))]) := by
    refine ⟨rfl, fun x w hxw => ?_⟩
    rcases hxw with ⟨kv, hkv, _, hw⟩
    rcases List.mem_singleton.mp hkv with rfl
    rw [valOut_eq] at hw
    rw [← hw]
    exact ⟨2, h2, by omega⟩
  have hdom : Val.domain (Val.fn (sizes := sizes) [(Val.atom (ops.intAtom 1), Val.atom (ops.intAtom 2))]) =
      Val.set [Val.atom (ops.intAtom 1)] := by
    change Val.set [mkVal (valOut (Val.atom (ops.intAtom 1)))] = Val.set [Val.atom (ops.intAtom 1)]
    rw [valOut_eq]
  have hlu : Val.fnLookup (Val.fn (sizes := sizes) [(Val.atom (ops.intAtom 1), Val.atom (ops.intAtom 2))])
      (Val.atom (ops.intAtom 1)) = some (Val.atom (ops.intAtom 2)) := Val.fnLookup_singleton _ _
  unfold Val.foldBag
  simp only [hbag, ↓reduceIte, hdom]
  change foldSetACList ops .intAdd (Val.atom (ops.intAtom 0))
    ((dedupList ((List.map valOut [Val.atom (ops.intAtom 1)]).map mkVal)).flatMap (fun k =>
      match (Val.fnLookup (Val.fn [(Val.atom (ops.intAtom 1), Val.atom (ops.intAtom 2))]) k).bind (valInt ops) with
      | some n => List.replicate n.toNat k
      | none => [])) = Val.atom (ops.intAtom 2)
  have hv0 : valInt (sizes := sizes) ops (Val.atom (ops.intAtom 0)) = some 0 := h0
  have hv1 : valInt (sizes := sizes) ops (Val.atom (ops.intAtom 1)) = some 1 := h1
  have hv2 : valInt (sizes := sizes) ops (Val.atom (ops.intAtom 2)) = some 2 := h2
  have ht2 : (2 : Int).toNat = 2 := rfl
  simp only [List.map_cons, List.map_nil, valOut_eq, dedupList, List.not_mem_nil, ↓reduceIte,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, hlu, Option.bind_some, hv2, ht2,
    List.replicate_succ, List.replicate_zero,
    foldSetACList, foldScalarAC, hv0, hv1, List.foldl_cons, List.foldl_nil]
  rfl

mutual
def evalExpr {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (ops : AtomOps A)
    (s t : State V sizes A) (env : Env sizes A) : Expr d V → Val sizes A
  | .err => Val.err
  | .atom id => Val.atom (ops.atomVal id)
  | .var v => s v
  | .primeVar v => t v
  | .localVar idx => env idx
  | .groupSet mask => Val.groupSet mask
  | .seqLit elems => Val.seq (evalExprList ops s t env elems)
  | .setEnum elems => Val.set (evalExprList ops s t env elems)
  | .recLit fields => Val.fn (evalRecPairs ops s t env fields)
  | .colonGt k v => Val.fn [(evalExpr ops s t env k, evalExpr ops s t env v)]
  | .atAt f g => Val.merge (evalExpr ops s t env f) (evalExpr ops s t env g)
  | .fnApp f arg => Val.apply (evalExpr ops s t env f) (evalExpr ops s t env arg)
  | .domain f => Val.domain (evalExpr ops s t env f)
  | .except base key rhs =>
      let bv := evalExpr ops s t env base
      let kv := evalExpr ops s t env key
      @ite _ (Val.isFn bv) (Classical.propDecidable _)
        (match Val.fnLookup bv kv with
         | some old => Val.update bv kv (evalExpr ops s t (push env old) rhs)
         | none => bv)
        Val.err
  | .fnConstruct dom body =>
      Val.fnConstruct (evalExpr ops s t env dom) (fun v => evalExpr ops s t (push env v) body)
  | .setFilter dom pred =>
      Val.setFilter (evalExpr ops s t env dom) (fun v => evalForm ops s t (push env v) pred)
  | .setMap dom body =>
      Val.setMap (evalExpr ops s t env dom) (fun v => evalExpr ops s t (push env v) body)
  | .cup a b => Val.cup (evalExpr ops s t env a) (evalExpr ops s t env b)
  | .cap a b => Val.cap (evalExpr ops s t env a) (evalExpr ops s t env b)
  | .setMinus a b => Val.setMinus (evalExpr ops s t env a) (evalExpr ops s t env b)
  | .union x => Val.union (evalExpr ops s t env x)
  | .powerset x => Val.powerset (evalExpr ops s t env x)
  | .cartesian sets => cartSet (evalExprList ops s t env sets)
  | .fnSet dom ran => Val.fnSet (evalExpr ops s t env dom) (evalExpr ops s t env ran)
  | .recSet fields => Val.recSet (evalRecSetPairs ops s t env fields)
  | .card x =>
      match Val.card (evalExpr ops s t env x) with
      | some n => Val.atom (HasNatAtom.natAtom n)
      | none => Val.err
  | .len x => Val.len (evalExpr ops s t env x)
  | .head x => Val.head (evalExpr ops s t env x)
  | .tail x => Val.tail (evalExpr ops s t env x)
  | .append x elem => Val.append (evalExpr ops s t env x) (evalExpr ops s t env elem)
  | .concat a b => Val.concat (evalExpr ops s t env a) (evalExpr ops s t env b)
  | .subseq x lo hi =>
      Val.subseq ops.intOf (evalExpr ops s t env x) (evalExpr ops s t env lo) (evalExpr ops s t env hi)
  | .selectSeq x pred =>
      Val.selectSeq (evalExpr ops s t env x) (fun v => evalForm ops s t (push env v) pred)
  | .foldSeq right onDomain seq base step =>
      Val.foldSeq right onDomain (evalExpr ops s t env seq) (evalExpr ops s t env base)
        (fun x acc => evalExpr ops s t (push (push env acc) x) step)
  | .foldSetAC op dom base elem =>
      Val.foldSetAC ops op (evalExpr ops s t env dom) (evalExpr ops s t env base)
        (fun v => evalExpr ops s t (push env v) elem)
  | .copiesIn elem bag =>
      Val.copiesIn ops (evalExpr ops s t env elem) (evalExpr ops s t env bag)
  | .bagCup b1 b2 =>
      Val.bagCup ops (evalExpr ops s t env b1) (evalExpr ops s t env b2)
  | .bagDiff b1 b2 =>
      Val.bagDiff ops (evalExpr ops s t env b1) (evalExpr ops s t env b2)
  | .bagUnion x =>
      Val.bagUnion ops (evalExpr ops s t env x)
  | .bagCard b =>
      Val.bagCard ops (evalExpr ops s t env b)
  | .bagOfAll bag f =>
      Val.bagOfAll ops (fun v => evalExpr ops s t (push env v) f) (evalExpr ops s t env bag)
  | .foldBag op bag base =>
      Val.foldBag ops op (evalExpr ops s t env bag) (evalExpr ops s t env base)
  | .ite cond yes no =>
      @ite _ (evalForm ops s t env cond) (Classical.propDecidable _)
        (evalExpr ops s t env yes) (evalExpr ops s t env no)
  | .letBind val body => evalExpr ops s t (push env (evalExpr ops s t env val)) body
  | .ofForm f =>
      Val.atom (ops.boolAtom (@decide (evalForm ops s t env f) (Classical.propDecidable _)))
  | .atomOp id args =>
      match collectAtoms (evalExprList ops s t env args) with
      | some as => Val.atom (ops.atomOp id as)
      | none => Val.err
  | .atomSetOp id args =>
      match collectAtoms (evalExprList ops s t env args) with
      | some as => Val.set ((ops.atomSetOp id as).map Val.atom)
      | none => Val.err
  | .atomSetAgg id x =>
      let sv := evalExpr ops s t env x
      @ite _ (Val.allAtoms sv) (Classical.propDecidable _)
        (Val.atom (ops.atomSetAgg id (fun a => Val.mem (Val.atom a) sv))) Val.err
  | .atomChoose dom pred =>
      let sv := evalExpr ops s t env dom
      @ite _ (Val.allAtoms sv) (Classical.propDecidable _)
        (Val.atom (ops.chooseAtom (fun a => Val.mem (Val.atom a) sv ∧ evalForm ops s t (push env (Val.atom a)) pred)))
        Val.err

def evalExprList {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (ops : AtomOps A)
    (s t : State V sizes A) (env : Env sizes A) : List (Expr d V) → List (Val sizes A)
  | [] => []
  | e :: es => evalExpr ops s t env e :: evalExprList ops s t env es

def evalRecPairs {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (ops : AtomOps A)
    (s t : State V sizes A) (env : Env sizes A) : List (Nat × Expr d V) → List (Val sizes A × Val sizes A)
  | [] => []
  | (f, e) :: rest => (Val.atom (ops.atomVal f), evalExpr ops s t env e) :: evalRecPairs ops s t env rest

def evalRecSetPairs {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (ops : AtomOps A)
    (s t : State V sizes A) (env : Env sizes A) : List (Nat × Expr d V) → List (A × Val sizes A)
  | [] => []
  | (f, e) :: rest => (ops.atomVal f, evalExpr ops s t env e) :: evalRecSetPairs ops s t env rest

def evalForm {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (ops : AtomOps A)
    (s t : State V sizes A) (env : Env sizes A) : Form d V → Prop
  | .truth b => b = true
  | .ofExpr e =>
      match Val.asAtom (evalExpr ops s t env e) with
      | some a => ops.isTrue a
      | none => False
  | .eq a b => evalExpr ops s t env a = evalExpr ops s t env b
  | .mem elem set => evalSetPred ops s t env set (evalExpr ops s t env elem)
  | .subsetEq sub sup =>
      let sv := evalExpr ops s t env sub
      Val.isSet sv ∧ ∀ v, Val.mem v sv → evalSetPred ops s t env sup v
  | .isFiniteSet e => Val.isFinite (evalExpr ops s t env e)
  | .isABag b => Val.isABag ops (evalExpr ops s t env b)
  | .bagIn elem bag => Val.bagIn ops (evalExpr ops s t env elem) (evalExpr ops s t env bag)
  | .sqSubseteq b1 b2 => Val.sqSubseteq ops (evalExpr ops s t env b1) (evalExpr ops s t env b2)
  | .conj a b => evalForm ops s t env a ∧ evalForm ops s t env b
  | .disj a b => evalForm ops s t env a ∨ evalForm ops s t env b
  | .neg a => ¬ evalForm ops s t env a
  | .impl a b => evalForm ops s t env a → evalForm ops s t env b
  | .iff a b => evalForm ops s t env a ↔ evalForm ops s t env b
  | .ite cond yes no =>
      (evalForm ops s t env cond ∧ evalForm ops s t env yes) ∨
      (¬ evalForm ops s t env cond ∧ evalForm ops s t env no)
  | .letBind val body => evalForm ops s t (push env (evalExpr ops s t env val)) body
  | .all dom body => ∀ v : Val sizes A, evalSetPred ops s t env dom v → evalForm ops s t (push env v) body
  | .some dom body => ∃ v : Val sizes A, evalSetPred ops s t env dom v ∧ evalForm ops s t (push env v) body
  | .atomRel id args =>
      match collectAtoms (evalExprList ops s t env args) with
      | some as => ops.atomRel id as
      | none => False

def evalSetPred {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (ops : AtomOps A)
    (s t : State V sizes A) (env : Env sizes A) : SetPred d V → Val sizes A → Prop
  | .expr e, v => Val.mem v (evalExpr ops s t env e)
  | .atomPred id, v =>
      match Val.asAtom v with
      | some a => ops.atomPred id a
      | none => False
  | .group mask, v => Val.mem v (Val.groupSet mask)
  | .enum elems, v => v ∈ evalExprList ops s t env elems
  | .cup a b, v => evalSetPred ops s t env a v ∨ evalSetPred ops s t env b v
  | .cap a b, v => evalSetPred ops s t env a v ∧ evalSetPred ops s t env b v
  | .diff a b, v => evalSetPred ops s t env a v ∧ ¬ evalSetPred ops s t env b v
  | .subset p, v => Val.isSet v ∧ ∀ x, Val.mem x v → evalSetPred ops s t env p x
  | .seq p, v =>
      match Val.seqElems v with
      | some xs => ∀ x ∈ xs, evalSetPred ops s t env p x
      | none => False
  | .times ps, v =>
      match Val.seqElems v with
      | some xs => evalSetPredList ops s t env ps xs
      | none => False
  | .fnSet dom ran, v =>
      Val.isSingleValuedFn v ∧
      (∀ k, (∃ w, Val.mapsTo v k w) ↔ evalSetPred ops s t env dom k) ∧
      (∀ k w, Val.mapsTo v k w → evalSetPred ops s t env ran w)
  | .recSet fields, v =>
      Val.isSingleValuedFn v ∧
      (∀ k w, Val.mapsTo v k w → ∃ f ∈ fields, k = Val.atom (ops.atomVal f.1)) ∧
      evalRecSetPreds ops s t env fields v
  | .filter dom pred, v => evalSetPred ops s t env dom v ∧ evalForm ops s t (push env v) pred

def evalSetPredList {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (ops : AtomOps A)
    (s t : State V sizes A) (env : Env sizes A) : List (SetPred d V) → List (Val sizes A) → Prop
  | [], [] => True
  | p :: ps, x :: xs => evalSetPred ops s t env p x ∧ evalSetPredList ops s t env ps xs
  | _, _ => False

def evalRecSetPreds {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (ops : AtomOps A)
    (s t : State V sizes A) (env : Env sizes A) : List (Nat × SetPred d V) → Val sizes A → Prop
  | [], _ => True
  | (f, sp) :: rest, v =>
      (∃ w, Val.mapsTo v (Val.atom (ops.atomVal f)) w) ∧
      (∀ w, Val.mapsTo v (Val.atom (ops.atomVal f)) w → evalSetPred ops s t env sp w) ∧
      evalRecSetPreds ops s t env rest v
end

private theorem congrArg₂ {α β γ : Sort _} (f : α → β → γ) {a₁ a₂ : α} {b₁ b₂ : β}
    (ha : a₁ = a₂) (hb : b₁ = b₂) : f a₁ b₁ = f a₂ b₂ :=
  ha ▸ hb ▸ rfl

mutual
theorem evalExpr_equivariant {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (ops : AtomOps A) (s t : State V sizes A) (env : Env sizes A) :
    ∀ e : Expr d V,
      evalExpr ops (renameState p s) (renameState p t) (renameEnv p env) e =
        renameVal p (evalExpr ops s t env e)
  | .err => rfl
  | .atom _ => rfl
  | .var _ => rfl
  | .primeVar _ => rfl
  | .localVar _ => rfl
  | .groupSet mask => (Val.groupSet_rename p mask).symm
  | .seqLit elems =>
    (congrArg Val.seq (evalExprList_equivariant p ops s t env elems)).trans (Val.rename_seq p _).symm
  | .setEnum elems =>
    (congrArg Val.set (evalExprList_equivariant p ops s t env elems)).trans (Val.rename_set p _).symm
  | .recLit fields =>
    (congrArg Val.fn (evalRecPairs_equivariant p ops s t env fields)).trans (Val.rename_fn p _).symm
  | .colonGt k v =>
    (congrArg₂ (fun a b => Val.fn [(a, b)])
      (evalExpr_equivariant p ops s t env k) (evalExpr_equivariant p ops s t env v)).trans
      (Val.rename_fn p [(evalExpr ops s t env k, evalExpr ops s t env v)]).symm
  | .atAt f g =>
    (congrArg₂ Val.merge (evalExpr_equivariant p ops s t env f) (evalExpr_equivariant p ops s t env g)).trans
      (Val.merge_rename p _ _)
  | .fnApp f arg =>
    (congrArg₂ Val.apply (evalExpr_equivariant p ops s t env f) (evalExpr_equivariant p ops s t env arg)).trans
      (Val.apply_rename p _ _)
  | .domain f =>
    (congrArg Val.domain (evalExpr_equivariant p ops s t env f)).trans (Val.domain_rename p _)
  | .except base key rhs => by
    change @ite _ (Val.isFn (evalExpr _ _ _ _ base)) (Classical.propDecidable _)
        (match Val.fnLookup (evalExpr _ _ _ _ base) (evalExpr _ _ _ _ key) with
         | some old => Val.update (evalExpr _ _ _ _ base) (evalExpr _ _ _ _ key)
             (evalExpr _ _ _ (push _ old) rhs)
         | none => evalExpr _ _ _ _ base) Val.err =
      renameVal p (@ite _ (Val.isFn (evalExpr ops s t env base)) (Classical.propDecidable _)
        (match Val.fnLookup (evalExpr ops s t env base) (evalExpr ops s t env key) with
         | some old => Val.update (evalExpr ops s t env base) (evalExpr ops s t env key)
             (evalExpr ops s t (push env old) rhs)
         | none => evalExpr ops s t env base) Val.err)
    rw [evalExpr_equivariant p ops s t env base, evalExpr_equivariant p ops s t env key]
    rw [propext (Val.isFn_rename p _), Val.fnLookup_rename]
    split
    · cases Val.fnLookup (evalExpr ops s t env base) (evalExpr ops s t env key) with
      | none => rfl
      | some old =>
        simp only [Option.map_some]
        rw [← renameEnv_push, evalExpr_equivariant p ops s t (push env old) rhs, Val.update_rename]
    · rfl
  | .fnConstruct dom body =>
    (congrArg (Val.fnConstruct · _) (evalExpr_equivariant p ops s t env dom)).trans
      (Val.fnConstruct_rename p _ _ _ (fun v => by
        rw [← renameEnv_push]; exact evalExpr_equivariant p ops s t (push env v) body))
  | .setFilter dom pred =>
    (congrArg (Val.setFilter · _) (evalExpr_equivariant p ops s t env dom)).trans
      (Val.setFilter_rename p _ _ _ (fun v => by
        rw [← renameEnv_push]; exact evalForm_equivariant p ops s t (push env v) pred))
  | .setMap dom body =>
    (congrArg (Val.setMap · _) (evalExpr_equivariant p ops s t env dom)).trans
      (Val.setMap_rename p _ _ _ (fun v => by
        rw [← renameEnv_push]; exact evalExpr_equivariant p ops s t (push env v) body))
  | .cup a b =>
    (congrArg₂ Val.cup (evalExpr_equivariant p ops s t env a) (evalExpr_equivariant p ops s t env b)).trans
      (Val.cup_rename p _ _)
  | .cap a b =>
    (congrArg₂ Val.cap (evalExpr_equivariant p ops s t env a) (evalExpr_equivariant p ops s t env b)).trans
      (Val.cap_rename p _ _)
  | .setMinus a b =>
    (congrArg₂ Val.setMinus (evalExpr_equivariant p ops s t env a) (evalExpr_equivariant p ops s t env b)).trans
      (Val.setMinus_rename p _ _)
  | .union x =>
    (congrArg Val.union (evalExpr_equivariant p ops s t env x)).trans (Val.union_rename p _)
  | .powerset x =>
    (congrArg Val.powerset (evalExpr_equivariant p ops s t env x)).trans (Val.powerset_rename p _)
  | .cartesian sets =>
    (congrArg cartSet (evalExprList_equivariant p ops s t env sets)).trans (cartSet_rename p _)
  | .fnSet dom ran =>
    (congrArg₂ Val.fnSet (evalExpr_equivariant p ops s t env dom) (evalExpr_equivariant p ops s t env ran)).trans
      (Val.fnSet_rename p _ _)
  | .recSet fields =>
    (congrArg Val.recSet (evalRecSetPairs_equivariant p ops s t env fields)).trans (Val.recSet_rename p _)
  | .card x => by
    change (match Val.card (evalExpr _ _ _ _ x) with
        | some n => Val.atom (HasNatAtom.natAtom n) | none => Val.err) =
      renameVal p (match Val.card (evalExpr ops s t env x) with
        | some n => Val.atom (HasNatAtom.natAtom n) | none => Val.err)
    rw [evalExpr_equivariant p ops s t env x, Val.card_rename]
    cases Val.card (evalExpr ops s t env x) <;> rfl
  | .len x =>
    (congrArg Val.len (evalExpr_equivariant p ops s t env x)).trans (Val.len_rename p _)
  | .head x =>
    (congrArg Val.head (evalExpr_equivariant p ops s t env x)).trans (Val.head_rename p _)
  | .tail x =>
    (congrArg Val.tail (evalExpr_equivariant p ops s t env x)).trans (Val.tail_rename p _)
  | .append x elem =>
    (congrArg₂ Val.append (evalExpr_equivariant p ops s t env x) (evalExpr_equivariant p ops s t env elem)).trans
      (Val.append_rename p _ _)
  | .concat a b =>
    (congrArg₂ Val.concat (evalExpr_equivariant p ops s t env a) (evalExpr_equivariant p ops s t env b)).trans
      (Val.concat_rename p _ _)
  | .subseq x lo hi => by
    change Val.subseq ops.intOf (evalExpr _ _ _ _ x) (evalExpr _ _ _ _ lo) (evalExpr _ _ _ _ hi) =
      renameVal p (Val.subseq ops.intOf (evalExpr ops s t env x) (evalExpr ops s t env lo) (evalExpr ops s t env hi))
    rw [evalExpr_equivariant p ops s t env x, evalExpr_equivariant p ops s t env lo,
      evalExpr_equivariant p ops s t env hi, Val.subseq_rename]
  | .selectSeq x pred =>
    (congrArg (Val.selectSeq · _) (evalExpr_equivariant p ops s t env x)).trans
      (Val.selectSeq_rename p _ _ _ (fun v => by
        rw [← renameEnv_push]; exact evalForm_equivariant p ops s t (push env v) pred))
  | .foldSeq right onDomain seq base step =>
    (congrArg₂ (Val.foldSeq right onDomain · · _) (evalExpr_equivariant p ops s t env seq)
      (evalExpr_equivariant p ops s t env base)).trans
      (Val.foldSeq_rename p right onDomain _ _ _ _ (fun x acc => by
        rw [← renameEnv_push, ← renameEnv_push]
        exact evalExpr_equivariant p ops s t (push (push env acc) x) step))
  | .foldSetAC op dom base elem =>
    (congrArg₂ (Val.foldSetAC ops op · · _) (evalExpr_equivariant p ops s t env dom)
      (evalExpr_equivariant p ops s t env base)).trans
      (Val.foldSetAC_rename p ops op _ _ _ _ (fun v => by
        rw [← renameEnv_push]
        exact evalExpr_equivariant p ops s t (push env v) elem))
  | .copiesIn elem bag =>
    (congrArg₂ (Val.copiesIn ops) (evalExpr_equivariant p ops s t env elem)
      (evalExpr_equivariant p ops s t env bag)).trans (Val.copiesIn_rename p ops _ _)
  | .bagCup b1 b2 =>
    (congrArg₂ (Val.bagCup ops) (evalExpr_equivariant p ops s t env b1)
      (evalExpr_equivariant p ops s t env b2)).trans (Val.bagCup_rename p ops _ _)
  | .bagDiff b1 b2 =>
    (congrArg₂ (Val.bagDiff ops) (evalExpr_equivariant p ops s t env b1)
      (evalExpr_equivariant p ops s t env b2)).trans (Val.bagDiff_rename p ops _ _)
  | .bagUnion x =>
    (congrArg (Val.bagUnion ops) (evalExpr_equivariant p ops s t env x)).trans (Val.bagUnion_rename p ops _)
  | .bagCard b =>
    (congrArg (Val.bagCard ops) (evalExpr_equivariant p ops s t env b)).trans (Val.bagCard_rename p ops _)
  | .bagOfAll bag f =>
    (congrArg (Val.bagOfAll ops _) (evalExpr_equivariant p ops s t env bag)).trans
      (Val.bagOfAll_rename p ops _ _ (fun v => by
        rw [← renameEnv_push]
        exact evalExpr_equivariant p ops s t (push env v) f) _)
  | .foldBag op bag base =>
    (congrArg₂ (Val.foldBag ops op) (evalExpr_equivariant p ops s t env bag)
      (evalExpr_equivariant p ops s t env base)).trans (Val.foldBag_rename p ops op _ _)
  | .ite cond yes no => by
    change @ite _ (evalForm _ _ _ _ cond) (Classical.propDecidable _) _ _ =
      renameVal p (@ite _ (evalForm ops s t env cond) (Classical.propDecidable _)
        (evalExpr ops s t env yes) (evalExpr ops s t env no))
    rw [propext (evalForm_equivariant p ops s t env cond)]
    split
    · exact evalExpr_equivariant p ops s t env yes
    · exact evalExpr_equivariant p ops s t env no
  | .letBind val body =>
    (congrArg (fun e => evalExpr ops (renameState p s) (renameState p t) e body)
      ((congrArg (push _) (evalExpr_equivariant p ops s t env val)).trans (renameEnv_push p env _).symm)).trans
      (evalExpr_equivariant p ops s t (push env (evalExpr ops s t env val)) body)
  | .ofForm f =>
    congrArg (fun q => Val.atom (ops.boolAtom (@decide q (Classical.propDecidable _))))
      (propext (evalForm_equivariant p ops s t env f))
  | .atomOp id args => by
    change (match collectAtoms (evalExprList _ _ _ _ args) with
        | some as => Val.atom (ops.atomOp id as) | none => Val.err) =
      renameVal p (match collectAtoms (evalExprList ops s t env args) with
        | some as => Val.atom (ops.atomOp id as) | none => Val.err)
    rw [evalExprList_equivariant p ops s t env args, collectAtoms_rename]
    cases collectAtoms (evalExprList ops s t env args) <;> rfl
  | .atomSetOp id args => by
    change (match collectAtoms (evalExprList _ _ _ _ args) with
        | some as => Val.set ((ops.atomSetOp id as).map Val.atom) | none => Val.err) =
      renameVal p (match collectAtoms (evalExprList ops s t env args) with
        | some as => Val.set ((ops.atomSetOp id as).map Val.atom) | none => Val.err)
    rw [evalExprList_equivariant p ops s t env args, collectAtoms_rename]
    cases collectAtoms (evalExprList ops s t env args) with
    | none => rfl
    | some as =>
      rw [Val.rename_set, List.map_map]
      rfl
  | .atomSetAgg id x => by
    change @ite _ (Val.allAtoms (evalExpr _ _ _ _ x)) (Classical.propDecidable _)
        (Val.atom (ops.atomSetAgg id (fun a => Val.mem (Val.atom a) (evalExpr _ _ _ _ x)))) Val.err =
      renameVal p (@ite _ (Val.allAtoms (evalExpr ops s t env x)) (Classical.propDecidable _)
        (Val.atom (ops.atomSetAgg id (fun a => Val.mem (Val.atom a) (evalExpr ops s t env x)))) Val.err)
    rw [evalExpr_equivariant p ops s t env x]
    rw [propext (Val.allAtoms_rename p _)]
    split
    · have hpred : (fun a => Val.mem (Val.atom a) (renameVal p (evalExpr ops s t env x))) =
          (fun a => Val.mem (Val.atom a) (evalExpr ops s t env x)) := by
        funext a
        exact propext (Val.mem_rename p (Val.atom a) (evalExpr ops s t env x))
      rw [hpred]
      rfl
    · rfl
  | .atomChoose dom pred => by
    change @ite _ (Val.allAtoms (evalExpr _ _ _ _ dom)) (Classical.propDecidable _)
        (Val.atom (ops.chooseAtom (fun a =>
          Val.mem (Val.atom a) (evalExpr _ _ _ _ dom) ∧
          evalForm _ _ _ (push _ (Val.atom a)) pred))) Val.err =
      renameVal p (@ite _ (Val.allAtoms (evalExpr ops s t env dom)) (Classical.propDecidable _)
        (Val.atom (ops.chooseAtom (fun a =>
          Val.mem (Val.atom a) (evalExpr ops s t env dom) ∧ evalForm ops s t (push env (Val.atom a)) pred))) Val.err)
    rw [evalExpr_equivariant p ops s t env dom]
    rw [propext (Val.allAtoms_rename p _)]
    split
    · have hpred : (fun a => Val.mem (Val.atom a) (renameVal p (evalExpr ops s t env dom)) ∧
            evalForm ops (renameState p s) (renameState p t) (push (renameEnv p env) (Val.atom a)) pred) =
          (fun a => Val.mem (Val.atom a) (evalExpr ops s t env dom) ∧
            evalForm ops s t (push env (Val.atom a)) pred) := by
        funext a
        have hm := Val.mem_rename p (Val.atom a) (evalExpr ops s t env dom)
        have hf := evalForm_equivariant p ops s t (push env (Val.atom a)) pred
        rw [renameEnv_push] at hf
        exact propext (and_congr hm hf)
      rw [hpred]
      rfl
    · rfl

theorem evalExprList_equivariant {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (ops : AtomOps A) (s t : State V sizes A) (env : Env sizes A) :
    ∀ es : List (Expr d V),
      evalExprList ops (renameState p s) (renameState p t) (renameEnv p env) es =
        (evalExprList ops s t env es).map (renameVal p)
  | [] => rfl
  | e :: es =>
    congrArg₂ List.cons (evalExpr_equivariant p ops s t env e) (evalExprList_equivariant p ops s t env es)

theorem evalRecPairs_equivariant {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (ops : AtomOps A) (s t : State V sizes A) (env : Env sizes A) :
    ∀ fs : List (Nat × Expr d V),
      evalRecPairs ops (renameState p s) (renameState p t) (renameEnv p env) fs =
        (evalRecPairs ops s t env fs).map (fun kv => (renameVal p kv.1, renameVal p kv.2))
  | [] => rfl
  | (_, e) :: rest =>
    congrArg₂ List.cons (Prod.ext rfl (evalExpr_equivariant p ops s t env e))
      (evalRecPairs_equivariant p ops s t env rest)

theorem evalRecSetPairs_equivariant {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (ops : AtomOps A) (s t : State V sizes A) (env : Env sizes A) :
    ∀ fs : List (Nat × Expr d V),
      evalRecSetPairs ops (renameState p s) (renameState p t) (renameEnv p env) fs =
        (evalRecSetPairs ops s t env fs).map (fun kv => (kv.1, renameVal p kv.2))
  | [] => rfl
  | (_, e) :: rest =>
    congrArg₂ List.cons (Prod.ext rfl (evalExpr_equivariant p ops s t env e))
      (evalRecSetPairs_equivariant p ops s t env rest)

theorem evalForm_equivariant {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (ops : AtomOps A) (s t : State V sizes A) (env : Env sizes A) :
    ∀ f : Form d V,
      evalForm ops (renameState p s) (renameState p t) (renameEnv p env) f ↔
        evalForm ops s t env f
  | .truth _ => Iff.rfl
  | .ofExpr e =>
    (congrArg (fun o => match o with | some a => ops.isTrue a | none => False)
      ((congrArg Val.asAtom (evalExpr_equivariant p ops s t env e)).trans (Val.asAtom_rename p _))).to_iff
  | .eq a b =>
    (congrArg₂ Eq (evalExpr_equivariant p ops s t env a) (evalExpr_equivariant p ops s t env b)).to_iff.trans
      (renameVal_injective p)
  | .mem elem set =>
    (congrArg (evalSetPred ops (renameState p s) (renameState p t) (renameEnv p env) set)
      (evalExpr_equivariant p ops s t env elem)).to_iff.trans
      (evalSetPred_equivariant p ops s t env set (evalExpr ops s t env elem))
  | .subsetEq sub sup => by
    change (Val.isSet (evalExpr _ _ _ _ sub) ∧
        ∀ v, Val.mem v (evalExpr _ _ _ _ sub) → evalSetPred _ _ _ _ sup v) ↔ _
    rw [evalExpr_equivariant p ops s t env sub, Val.isSet_rename]
    constructor
    · rintro ⟨hs, hsub⟩
      refine ⟨hs, fun v hv => ?_⟩
      exact (evalSetPred_equivariant p ops s t env sup v).mp (hsub (renameVal p v) ((Val.mem_rename p v _).mpr hv))
    · rintro ⟨hs, hsub⟩
      refine ⟨hs, fun v hv => ?_⟩
      have hv' : Val.mem (renameVal p.inverse v) (evalExpr ops s t env sub) := by
        have := (Val.mem_rename p (renameVal p.inverse v) (evalExpr ops s t env sub)).mp
        rw [renameVal_right] at this
        exact this hv
      have hsp := (evalSetPred_equivariant p ops s t env sup (renameVal p.inverse v)).mpr (hsub _ hv')
      rwa [renameVal_right] at hsp
  | .isFiniteSet e =>
    (congrArg Val.isFinite (evalExpr_equivariant p ops s t env e)).to_iff.trans (Val.isFinite_rename p _)
  | .isABag b =>
    (congrArg (Val.isABag ops) (evalExpr_equivariant p ops s t env b)).to_iff.trans (Val.isABag_rename p ops _)
  | .bagIn elem bag =>
    (congrArg₂ (Val.bagIn ops) (evalExpr_equivariant p ops s t env elem)
      (evalExpr_equivariant p ops s t env bag)).to_iff.trans (Val.bagIn_rename p ops _ _)
  | .sqSubseteq b1 b2 =>
    (congrArg₂ (Val.sqSubseteq ops) (evalExpr_equivariant p ops s t env b1)
      (evalExpr_equivariant p ops s t env b2)).to_iff.trans (Val.sqSubseteq_rename p ops _ _)
  | .conj a b => and_congr (evalForm_equivariant p ops s t env a) (evalForm_equivariant p ops s t env b)
  | .disj a b => or_congr (evalForm_equivariant p ops s t env a) (evalForm_equivariant p ops s t env b)
  | .neg a => not_congr (evalForm_equivariant p ops s t env a)
  | .impl a b => imp_congr (evalForm_equivariant p ops s t env a) (evalForm_equivariant p ops s t env b)
  | .iff a b => iff_congr (evalForm_equivariant p ops s t env a) (evalForm_equivariant p ops s t env b)
  | .ite cond yes no =>
    or_congr (and_congr (evalForm_equivariant p ops s t env cond) (evalForm_equivariant p ops s t env yes))
      (and_congr (not_congr (evalForm_equivariant p ops s t env cond)) (evalForm_equivariant p ops s t env no))
  | .letBind val body =>
    (congrArg (fun e => evalForm ops (renameState p s) (renameState p t) e body)
      ((congrArg (push _) (evalExpr_equivariant p ops s t env val)).trans (renameEnv_push p env _).symm)).to_iff.trans
      (evalForm_equivariant p ops s t (push env (evalExpr ops s t env val)) body)
  | .all dom body => by
    constructor
    · intro h v hv
      have hv' := (evalSetPred_equivariant p ops s t env dom v).mpr hv
      have hb := h (renameVal p v) hv'
      rw [← renameEnv_push] at hb
      exact (evalForm_equivariant p ops s t (push env v) body).mp hb
    · intro h v hv
      have hv' : evalSetPred ops s t env dom (renameVal p.inverse v) := by
        have := (evalSetPred_equivariant p ops s t env dom (renameVal p.inverse v)).mp
        rw [renameVal_right] at this
        exact this hv
      have hb := (evalForm_equivariant p ops s t (push env (renameVal p.inverse v)) body).mpr (h _ hv')
      rw [renameEnv_push, renameVal_right] at hb
      exact hb
  | .some dom body => by
    constructor
    · rintro ⟨v, hv, hb⟩
      have hv' : evalSetPred ops s t env dom (renameVal p.inverse v) := by
        have := (evalSetPred_equivariant p ops s t env dom (renameVal p.inverse v)).mp
        rw [renameVal_right] at this
        exact this hv
      refine ⟨renameVal p.inverse v, hv', (evalForm_equivariant p ops s t (push env (renameVal p.inverse v)) body).mp ?_⟩
      rwa [renameEnv_push, renameVal_right]
    · rintro ⟨v, hv, hb⟩
      refine ⟨renameVal p v, (evalSetPred_equivariant p ops s t env dom v).mpr hv, ?_⟩
      have hb' := (evalForm_equivariant p ops s t (push env v) body).mpr hb
      rwa [renameEnv_push] at hb'
  | .atomRel id args =>
    (congrArg (fun o => match o with | some as => ops.atomRel id as | none => False)
      ((congrArg collectAtoms (evalExprList_equivariant p ops s t env args)).trans (collectAtoms_rename p _))).to_iff

theorem evalSetPred_equivariant {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (ops : AtomOps A) (s t : State V sizes A) (env : Env sizes A) :
    ∀ (sp : SetPred d V) (v : Val sizes A),
      evalSetPred ops (renameState p s) (renameState p t) (renameEnv p env) sp (renameVal p v) ↔
        evalSetPred ops s t env sp v
  | .expr e, v =>
    (congrArg (Val.mem (renameVal p v)) (evalExpr_equivariant p ops s t env e)).to_iff.trans (Val.mem_rename p v _)
  | .atomPred id, v =>
    (congrArg (fun o => match o with | some a => ops.atomPred id a | none => False)
      (Val.asAtom_rename p v)).to_iff
  | .group mask, v => by
    have h := Val.mem_rename p v (Val.groupSet (A := A) mask)
    rwa [Val.groupSet_rename] at h
  | .enum elems, v => by
    change renameVal p v ∈ evalExprList _ _ _ _ elems ↔ _
    rw [evalExprList_equivariant p ops s t env elems, List.mem_map]
    constructor
    · rintro ⟨w, hw, heq⟩
      exact ((renameVal_injective p).mp heq) ▸ hw
    · intro hv
      exact ⟨v, hv, rfl⟩
  | .cup a b, v =>
    or_congr (evalSetPred_equivariant p ops s t env a v) (evalSetPred_equivariant p ops s t env b v)
  | .cap a b, v =>
    and_congr (evalSetPred_equivariant p ops s t env a v) (evalSetPred_equivariant p ops s t env b v)
  | .diff a b, v =>
    and_congr (evalSetPred_equivariant p ops s t env a v) (not_congr (evalSetPred_equivariant p ops s t env b v))
  | .subset sp, v => by
    change (Val.isSet (renameVal p v) ∧ ∀ x, Val.mem x (renameVal p v) → evalSetPred _ _ _ _ sp x) ↔ _
    rw [Val.isSet_rename]
    constructor
    · rintro ⟨hs, hsub⟩
      refine ⟨hs, fun x hx => ?_⟩
      exact (evalSetPred_equivariant p ops s t env sp x).mp (hsub (renameVal p x) ((Val.mem_rename p x v).mpr hx))
    · rintro ⟨hs, hsub⟩
      refine ⟨hs, fun x hx => ?_⟩
      have hx' : Val.mem (renameVal p.inverse x) v := by
        have := (Val.mem_rename p (renameVal p.inverse x) v).mp
        rw [renameVal_right] at this
        exact this hx
      have hsp := (evalSetPred_equivariant p ops s t env sp (renameVal p.inverse x)).mpr (hsub _ hx')
      rwa [renameVal_right] at hsp
  | .seq sp, v => by
    change (match Val.seqElems (renameVal p v) with
        | some xs => ∀ x ∈ xs, evalSetPred _ _ _ _ sp x | none => False) ↔
      (match Val.seqElems v with | some xs => ∀ x ∈ xs, evalSetPred ops s t env sp x | none => False)
    rw [Val.seqElems_rename]
    cases Val.seqElems v with
    | none => exact Iff.rfl
    | some xs =>
      simp only [Option.map_some]
      constructor
      · intro h x hx
        exact (evalSetPred_equivariant p ops s t env sp x).mp (h (renameVal p x) (List.mem_map_of_mem hx))
      · intro h x hx
        rcases List.mem_map.mp hx with ⟨x0, hx0, rfl⟩
        exact (evalSetPred_equivariant p ops s t env sp x0).mpr (h x0 hx0)
  | .times ps, v => by
    change (match Val.seqElems (renameVal p v) with
        | some xs => evalSetPredList _ _ _ _ ps xs | none => False) ↔
      (match Val.seqElems v with | some xs => evalSetPredList ops s t env ps xs | none => False)
    rw [Val.seqElems_rename]
    cases Val.seqElems v with
    | none => exact Iff.rfl
    | some xs =>
      simp only [Option.map_some]
      exact evalSetPredList_equivariant p ops s t env ps xs
  | .fnSet dom ran, v => by
    apply and_congr (Val.isSingleValuedFn_rename p v)
    apply and_congr
    · constructor
      · intro h k
        have hk := h (renameVal p k)
        rw [evalSetPred_equivariant p ops s t env dom k] at hk
        rw [← hk]
        constructor
        · rintro ⟨w, hw⟩; exact ⟨renameVal p w, (Val.mapsTo_rename p v k w).mpr hw⟩
        · rintro ⟨w, hw⟩
          refine ⟨renameVal p.inverse w, ?_⟩
          have := (Val.mapsTo_rename p v k (renameVal p.inverse w)).mp
          rw [renameVal_right] at this
          exact this hw
      · intro h k
        have hk := h (renameVal p.inverse k)
        have hdom := evalSetPred_equivariant p ops s t env dom (renameVal p.inverse k)
        rw [renameVal_right] at hdom
        rw [hdom, ← hk]
        constructor
        · rintro ⟨w, hw⟩
          refine ⟨renameVal p.inverse w, ?_⟩
          have := (Val.mapsTo_rename p v (renameVal p.inverse k) (renameVal p.inverse w)).mp
          rw [renameVal_right, renameVal_right] at this
          exact this hw
        · rintro ⟨w, hw⟩
          refine ⟨renameVal p w, ?_⟩
          have := (Val.mapsTo_rename p v (renameVal p.inverse k) w).mpr hw
          rwa [renameVal_right] at this
    · constructor
      · intro h k w hkw
        have hw := h (renameVal p k) (renameVal p w) ((Val.mapsTo_rename p v k w).mpr hkw)
        exact (evalSetPred_equivariant p ops s t env ran w).mp hw
      · intro h k w hkw
        have hkw' : Val.mapsTo v (renameVal p.inverse k) (renameVal p.inverse w) := by
          have := (Val.mapsTo_rename p v (renameVal p.inverse k) (renameVal p.inverse w)).mp
          rw [renameVal_right, renameVal_right] at this
          exact this hkw
        have hr := (evalSetPred_equivariant p ops s t env ran (renameVal p.inverse w)).mpr (h _ _ hkw')
        rwa [renameVal_right] at hr
  | .recSet fields, v => by
    apply and_congr (Val.isSingleValuedFn_rename p v)
    apply and_congr
    · constructor
      · intro h k w hkw
        rcases h (renameVal p k) (renameVal p w) ((Val.mapsTo_rename p v k w).mpr hkw) with ⟨f, hf, heq⟩
        exact ⟨f, hf, (renameVal_injective p).mp heq⟩
      · intro h k w hkw
        have hkw' : Val.mapsTo v (renameVal p.inverse k) (renameVal p.inverse w) := by
          have := (Val.mapsTo_rename p v (renameVal p.inverse k) (renameVal p.inverse w)).mp
          rw [renameVal_right, renameVal_right] at this
          exact this hkw
        rcases h _ _ hkw' with ⟨f, hf, heq⟩
        refine ⟨f, hf, ?_⟩
        have := congrArg (renameVal p) heq
        rwa [renameVal_right] at this
    · exact evalRecSetPreds_equivariant p ops s t env fields v
  | .filter dom pred, v =>
    and_congr (evalSetPred_equivariant p ops s t env dom v)
      ((congrArg (fun e => evalForm ops (renameState p s) (renameState p t) e pred)
        (renameEnv_push p env v).symm).to_iff.trans
        (evalForm_equivariant p ops s t (push env v) pred))

theorem evalSetPredList_equivariant {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (ops : AtomOps A) (s t : State V sizes A) (env : Env sizes A) :
    ∀ (ps : List (SetPred d V)) (xs : List (Val sizes A)),
      evalSetPredList ops (renameState p s) (renameState p t) (renameEnv p env) ps (xs.map (renameVal p)) ↔
        evalSetPredList ops s t env ps xs
  | [], [] => Iff.rfl
  | [], _ :: _ => Iff.rfl
  | _ :: _, [] => Iff.rfl
  | sp :: ps, x :: xs =>
    and_congr (evalSetPred_equivariant p ops s t env sp x)
      (evalSetPredList_equivariant p ops s t env ps xs)

theorem evalRecSetPreds_equivariant {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (p : GroupPerm sizes)
    (ops : AtomOps A) (s t : State V sizes A) (env : Env sizes A) :
    ∀ (fs : List (Nat × SetPred d V)) (v : Val sizes A),
      evalRecSetPreds ops (renameState p s) (renameState p t) (renameEnv p env) fs (renameVal p v) ↔
        evalRecSetPreds ops s t env fs v
  | [], _ => Iff.rfl
  | (f, sp) :: rest, v => by
    apply and_congr
    · constructor
      · rintro ⟨w, hw⟩
        refine ⟨renameVal p.inverse w, ?_⟩
        have := (Val.mapsTo_rename p v (Val.atom (ops.atomVal f)) (renameVal p.inverse w)).mp
        rw [Val.rename_atom, renameVal_right] at this
        exact this hw
      · rintro ⟨w, hw⟩
        exact ⟨renameVal p w, (Val.mapsTo_rename p v (Val.atom (ops.atomVal f)) w).mpr hw⟩
    · apply and_congr
      · constructor
        · intro h w hw
          have h' := h (renameVal p w) ((Val.mapsTo_rename p v (Val.atom (ops.atomVal f)) w).mpr hw)
          exact (evalSetPred_equivariant p ops s t env sp w).mp h'
        · intro h w hw
          have hw' : Val.mapsTo v (Val.atom (ops.atomVal f)) (renameVal p.inverse w) := by
            have := (Val.mapsTo_rename p v (Val.atom (ops.atomVal f)) (renameVal p.inverse w)).mp
            rw [Val.rename_atom, renameVal_right] at this
            exact this hw
          have hsp := (evalSetPred_equivariant p ops s t env sp (renameVal p.inverse w)).mpr (h _ hw')
          rwa [renameVal_right] at hsp
      · exact evalRecSetPreds_equivariant p ops s t env rest v
end

def Orbit {V : Type} {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (s t : State V sizes A) : Prop :=
  ∃ p : GroupPerm sizes, renameState p s = t

def orbits (V : Type) {d : Nat} (sizes : Fin d → Nat) (A : Type) [HasNatAtom A] :
    Setoid (State V sizes A) where
  r := Orbit
  iseqv := {
    refl := fun s => ⟨GroupPerm.identity, renameState_identity s⟩
    symm := by
      rintro s t ⟨p, rfl⟩
      exact ⟨p.inverse, renameState_inverse p s⟩
    trans := by
      rintro s t u ⟨p, rfl⟩ ⟨q, rfl⟩
      exact ⟨p.then q, renameState_then p q s⟩ }

def project {V : Type} {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (s : State V sizes A) : Quotient (orbits V sizes A) :=
  Quotient.mk _ s

theorem project_rename {V : Type} {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (s : State V sizes A) :
    project (renameState p s) = project s := by
  have h : project s = project (renameState p s) := Quotient.sound (show Orbit s (renameState p s) from ⟨p, rfl⟩)
  exact h.symm

def emptyEnv {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] : Env sizes A :=
  fun _ => Val.err

theorem renameEnv_empty {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] (p : GroupPerm sizes) :
    renameEnv p (emptyEnv (sizes := sizes) (A := A)) = emptyEnv := by
  funext _; rfl

structure Model (d : Nat) (sizes : Fin d → Nat) (V A : Type) where
  ops : AtomOps A
  initForm : Form d V
  nextForm : Form d V
  obsForm : Form d V
  initObsForm : Form d V := .truth true
  constraintForm : Form d V := .truth true
  actionConstraintForm : Form d V := .truth true
  actionObsForm : Form d V := .truth true

namespace Model
variable {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A] (m : Model d sizes V A)

def concrete : System (State V sizes A) where
  initial s := evalForm m.ops s s emptyEnv m.initForm
  next s t := evalForm m.ops s t emptyEnv m.nextForm
  safe s := evalForm m.ops s s emptyEnv m.obsForm

theorem init_rename (p : GroupPerm sizes) (s : State V sizes A) :
    m.concrete.initial (renameState p s) ↔ m.concrete.initial s := by
  have h := evalForm_equivariant p m.ops s s emptyEnv m.initForm
  rwa [renameEnv_empty] at h

theorem next_rename (p : GroupPerm sizes) (s t : State V sizes A) :
    m.concrete.next (renameState p s) (renameState p t) ↔ m.concrete.next s t := by
  have h := evalForm_equivariant p m.ops s t emptyEnv m.nextForm
  rwa [renameEnv_empty] at h

theorem safe_rename (p : GroupPerm sizes) (s : State V sizes A) :
    m.concrete.safe (renameState p s) ↔ m.concrete.safe s := by
  have h := evalForm_equivariant p m.ops s s emptyEnv m.obsForm
  rwa [renameEnv_empty] at h

def reduced : System (Quotient (orbits V sizes A)) where
  initial a := ∃ s, m.concrete.initial s ∧ project s = a
  next a b := ∃ s t, project s = a ∧ m.concrete.next s t ∧ project t = b
  safe a := Quotient.liftOn a m.concrete.safe (by
    rintro s t ⟨p, rfl⟩
    exact propext (m.safe_rename p s).symm)

theorem certificate : Certificate m.concrete m.reduced project := by
  constructor
  · intro a
    rfl
  · intro s a
    constructor
    · rintro ⟨x, t, hx, hn, ht⟩
      obtain ⟨p, hp⟩ := Quotient.exact hx
      refine ⟨renameState p t, ?_, (project_rename p t).trans ht⟩
      have h := (m.next_rename p x t).mpr hn
      rw [hp] at h
      exact h
    · rintro ⟨t, hn, ht⟩
      exact ⟨s, t, rfl, hn, ht⟩
  · intro s
    rfl

theorem optimization_correct :
    (∀ s, Reachable m.concrete s → m.concrete.safe s) ↔
    (∀ a, Reachable m.reduced a → m.reduced.safe a) := safety_iff m.certificate

theorem specification_correct :
    (∀ s, Reachable (withStuttering m.concrete) s → m.concrete.safe s) ↔
    (∀ a, Reachable (withStuttering m.reduced) a → m.reduced.safe a) := by
  simpa only [stuttering_reachable_iff] using m.optimization_correct

theorem counterexample_lifts {a} (ha : Reachable m.reduced a) (bad : ¬ m.reduced.safe a) :
    ∃ s, Reachable m.concrete s ∧ project s = a ∧ ¬ m.concrete.safe s := by
  obtain ⟨s, hs, he⟩ := reachable_backward m.certificate ha
  refine ⟨s, hs, he, ?_⟩
  intro good
  apply bad
  rw [← he]
  exact (m.certificate.observe s).mp good

theorem deadlock_preserved (s : State V sizes A) :
    (¬ ∃ t, m.concrete.next s t) ↔ (¬ ∃ a, m.reduced.next (project s) a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s a).mp ha
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨project t, (m.certificate.next s (project t)).mpr ⟨t, ht, rfl⟩⟩

theorem orbit_key_equivalent (s t : State V sizes A) :
    project s = project t ↔ Orbit s t := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound (show (orbits V sizes A).r s t from h)

def constrainedConcrete : ConstrainedSystem (State V sizes A) where
  toSystem := m.concrete
  initSafe s := evalForm m.ops s s emptyEnv m.initObsForm
  constraint s := evalForm m.ops s s emptyEnv m.constraintForm
  actionConstraint s t := evalForm m.ops s t emptyEnv m.actionConstraintForm
  actionSafe s t := evalForm m.ops s t emptyEnv m.actionObsForm

theorem initSafe_rename (p : GroupPerm sizes) (s : State V sizes A) :
    m.constrainedConcrete.initSafe (renameState p s) ↔ m.constrainedConcrete.initSafe s := by
  have h := evalForm_equivariant p m.ops s s emptyEnv m.initObsForm
  rwa [renameEnv_empty] at h

theorem constraint_rename (p : GroupPerm sizes) (s : State V sizes A) :
    m.constrainedConcrete.constraint (renameState p s) ↔ m.constrainedConcrete.constraint s := by
  have h := evalForm_equivariant p m.ops s s emptyEnv m.constraintForm
  rwa [renameEnv_empty] at h

theorem actionConstraint_rename (p : GroupPerm sizes) (s t : State V sizes A) :
    m.constrainedConcrete.actionConstraint (renameState p s) (renameState p t) ↔
      m.constrainedConcrete.actionConstraint s t := by
  have h := evalForm_equivariant p m.ops s t emptyEnv m.actionConstraintForm
  rwa [renameEnv_empty] at h

theorem actionSafe_rename (p : GroupPerm sizes) (s t : State V sizes A) :
    m.constrainedConcrete.actionSafe (renameState p s) (renameState p t) ↔
      m.constrainedConcrete.actionSafe s t := by
  have h := evalForm_equivariant p m.ops s t emptyEnv m.actionObsForm
  rwa [renameEnv_empty] at h

def constrainedReduced : ConstrainedSystem (Quotient (orbits V sizes A)) where
  toSystem := m.reduced
  initSafe a := Quotient.liftOn a m.constrainedConcrete.initSafe (by
    rintro s t ⟨p, rfl⟩
    exact propext (m.initSafe_rename p s).symm)
  constraint a := Quotient.liftOn a m.constrainedConcrete.constraint (by
    rintro s t ⟨p, rfl⟩
    exact propext (m.constraint_rename p s).symm)
  actionConstraint a b := ∃ s t, project s = a ∧ m.concrete.next s t ∧
    m.constrainedConcrete.actionConstraint s t ∧ project t = b
  actionSafe a b := ∀ s t, project s = a → project t = b → m.concrete.next s t →
    m.constrainedConcrete.actionSafe s t

theorem constrained_certificate :
    ConstrainedCertificate m.constrainedConcrete m.constrainedReduced project := by
  refine ⟨m.certificate.initial, m.certificate.next, m.certificate.observe, fun _ => Iff.rfl, fun _ => Iff.rfl, ?_, ?_⟩
  · intro s a
    constructor
    · rintro ⟨_, hc, x, y, hx, hxy, hac, hy⟩
      obtain ⟨p, hp⟩ := Quotient.exact hx
      let t := renameState p y
      have hnext : m.concrete.next s t := by
        have h := (m.next_rename p x y).mpr hxy
        rwa [hp] at h
      have hact : m.constrainedConcrete.actionConstraint s t := by
        have h := (m.actionConstraint_rename p x y).mpr hac
        rwa [hp] at h
      have hpt : project t = a := (project_rename p y).trans hy
      have hct : m.constrainedConcrete.constraint t := by
        change m.constrainedReduced.constraint (project t)
        rw [hpt]
        exact hc
      exact ⟨t, hnext, hct, hact, hpt⟩
    · rintro ⟨t, hn, hc, hac, rfl⟩
      exact ⟨⟨s, t, rfl, hn, rfl⟩, hc, ⟨s, t, rfl, hn, hac, rfl⟩⟩
  · intro s a
    constructor
    · intro h _ x y hx hy hxy
      obtain ⟨p, hp⟩ := Quotient.exact hx
      let t := renameState p y
      have hnext : m.concrete.next s t := by
        have hn := (m.next_rename p x y).mpr hxy
        rwa [hp] at hn
      have hpt : project t = a := (project_rename p y).trans hy
      have has := h t hnext hpt
      have hrew := (m.actionSafe_rename p x y).mp
      rw [hp] at hrew
      exact hrew has
    · intro h t hst hpt
      exact h ⟨s, t, rfl, hst, hpt⟩ s t rfl hpt hst
end Model

def pushList {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (env : Env sizes A) : List (Val sizes A) → Env sizes A
  | [] => env
  | w :: ws => pushList (push env w) ws

theorem renameEnv_pushList {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) :
    ∀ (env : Env sizes A) (ws : List (Val sizes A)),
      renameEnv p (pushList env ws) = pushList (renameEnv p env) (ws.map (renameVal p))
  | _, [] => rfl
  | env, w :: ws => by
    simp only [pushList, List.map_cons, renameEnv_push, renameEnv_pushList p (push env w) ws]

def evalBounds {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A]
    (ops : AtomOps A) (s t : EquivRule.State V sizes A) :
    Env sizes A → List (SetPred d V) → List (Val sizes A) → Prop
  | _, [], [] => True
  | env, dom :: doms, w :: ws =>
      evalSetPred ops s t env dom w ∧ evalBounds ops s t (push env w) doms ws
  | _, _, _ => False

theorem evalBounds_equivariant {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) (ops : AtomOps A) (s t : EquivRule.State V sizes A) :
    ∀ (env : Env sizes A) (doms : List (SetPred d V)) (ws : List (Val sizes A)),
      evalBounds ops (renameState p s) (renameState p t) (renameEnv p env) doms (ws.map (renameVal p)) ↔
        evalBounds ops s t env doms ws
  | _, [], [] => Iff.rfl
  | _, [], _ :: _ => Iff.rfl
  | _, _ :: _, [] => Iff.rfl
  | env, dom :: doms, w :: ws => by
    simp only [List.map_cons, evalBounds]
    exact and_congr
      (evalSetPred_equivariant p ops s t env dom w)
      (by rw [← renameEnv_push]; exact evalBounds_equivariant p ops s t (push env w) doms ws)

end
end TlxOptimization.EquivRule
