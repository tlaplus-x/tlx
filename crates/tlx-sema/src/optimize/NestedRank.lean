/- Rank keys preserve relative order and exact nonpositive sentinels. -/
set_option autoImplicit false
namespace TlxOptimization.NestedRule

-- Deduplication selects the same occurrence positions whenever equality agrees.
def representatives {I : Type} (f : I → Nat) : List I → List I
  | [] => []
  | i :: is => i :: representatives f (is.filter (fun j => f j != f i))
termination_by is => is.length
decreasing_by
  have := List.length_filter_le (fun j => f j != f i) is
  simp_wf
  omega

theorem representatives_congr {I : Type} (f g : I → Nat) (is : List I)
    (same : ∀ i ∈ is, ∀ j ∈ is, f i = f j ↔ g i = g j) :
    representatives f is = representatives g is := by
  cases hlist : is with
  | nil => simp [representatives]
  | cons i is =>
    rw [hlist] at same
    have filters : is.filter (fun j => f j != f i) = is.filter (fun j => g j != g i) := by
      apply List.filter_congr
      intro j hj
      have h := same j (by simp [hj]) i (by simp)
      exact Bool.eq_iff_iff.mpr (by simpa only [bne_iff_ne, ne_eq] using not_congr h)
    simp only [representatives]
    rw [← filters]
    congr 1
    apply representatives_congr f g (is.filter (fun j => f j != f i))
    intro j hj k hk
    exact same j (by simp [(List.mem_filter.mp hj).1]) k (by simp [(List.mem_filter.mp hk).1])
termination_by is.length
decreasing_by
  have := List.length_filter_le (fun j => f j != f i) is
  simp_wf
  simp_all
  omega

theorem dedup_image {I : Type} (f : I → Nat) (is : List I) :
    (is.map f).eraseDups = (representatives f is).map f := by
  cases hlist : is with
  | nil => simp [representatives]
  | cons i is =>
    simp only [List.map_cons, List.eraseDups_cons, representatives, List.map_cons]
    congr 1
    rw [List.filter_map]
    exact dedup_image f (is.filter (fun j => f j != f i))
termination_by is.length
decreasing_by
  have := List.length_filter_le (fun j => f j != f i) is
  simp_wf
  omega

-- Counting smaller live values strictly preserves their order.
theorem filter_length_mono (xs : List Nat) (x y : Nat) (h : x ≤ y) :
    (xs.filter (fun z => z < x)).length ≤ (xs.filter (fun z => z < y)).length := by
  induction xs with
  | nil => simp
  | cons z zs ih =>
    by_cases hx : z < x <;> by_cases hy : z < y <;>
      simp only [List.filter_cons, decide_eq_true_eq, hx, hy, ite_true, ite_false, List.length_cons] <;> omega

theorem filter_length_strict (xs : List Nat) (x y : Nat) (mem : x ∈ xs) (h : x < y) :
    (xs.filter (fun z => z < x)).length < (xs.filter (fun z => z < y)).length := by
  induction xs with
  | nil => simp at mem
  | cons z zs ih =>
    rcases List.mem_cons.mp mem with eq | mem
    · subst z
      have hm := filter_length_mono zs x y (Nat.le_of_lt h)
      simp [h]
      omega
    · have hi := ih mem
      by_cases hx : z < x <;> by_cases hy : z < y <;>
        simp only [List.filter_cons, decide_eq_true_eq, hx, hy, ite_true, ite_false, List.length_cons] <;> omega

def rank (xs : List Nat) (value : Nat) : Nat := (xs.eraseDups.filter (fun z => z < value)).length

theorem rank_le_iff (xs : List Nat) (x y : Nat) (_hx : x ∈ xs) (hy : y ∈ xs) :
    rank xs x ≤ rank xs y ↔ x ≤ y := by
  constructor
  · intro h
    by_cases hn : x ≤ y
    · exact hn
    have ht := filter_length_strict xs.eraseDups y x (List.mem_eraseDups.mpr hy) (by omega)
    unfold rank at h
    omega
  · intro h
    exact filter_length_mono _ _ _ h

theorem rank_congr {I : Type} (f g : I → Nat) (is : List I)
    (same : ∀ i j, f i ≤ f j ↔ g i ≤ g j) (k : I) :
    rank (is.map f) (f k) = rank (is.map g) (g k) := by
  have eqs (i j : I) : f i = f j ↔ g i = g j := by
    have h := same i j
    have hr := same j i
    omega
  have lt (i j : I) : f i < f j ↔ g i < g j := by
    have h := same j i
    omega
  have reps := representatives_congr f g is (fun i _ j _ => eqs i j)
  unfold rank
  rw [dedup_image, dedup_image, ← reps, List.filter_map, List.filter_map]
  simp only [List.length_map]
  congr 1
  apply List.filter_congr
  intro i _
  exact Bool.eq_iff_iff.mpr (by simpa using lt i k)

theorem ranks_equivalent {I : Type} (f g : I → Nat) (is : List I)
    (complete : ∀ i, i ∈ is) :
    (∀ i, rank (is.map f) (f i) = rank (is.map g) (g i)) ↔
    (∀ i j, f i ≤ f j ↔ g i ≤ g j) := by
  constructor
  · intro h i j
    have fi : f i ∈ is.map f := List.mem_map.mpr ⟨i, complete i, rfl⟩
    have fj : f j ∈ is.map f := List.mem_map.mpr ⟨j, complete j, rfl⟩
    have gi : g i ∈ is.map g := List.mem_map.mpr ⟨i, complete i, rfl⟩
    have gj : g j ∈ is.map g := List.mem_map.mpr ⟨j, complete j, rfl⟩
    rw [← rank_le_iff _ _ _ fi fj, ← rank_le_iff _ _ _ gi gj, h i, h j]
  · intro h i
    exact rank_congr f g is h i

end TlxOptimization.NestedRule
set_option autoImplicit false
namespace TlxOptimization.NestedRule

def positiveRank (xs : List Int) (x : Int) : Nat := rank (0 :: xs.map Int.toNat) x.toNat

def canonical (xs : List Int) (x : Int) : Int :=
  if x ≤ 0 then x else (positiveRank xs x : Int)

def sentinel (x : Int) : Option Int := if x ≤ 0 then some x else none

theorem rank_zero (xs : List Nat) : rank xs 0 = 0 := by
  simp [rank]

theorem positiveRank_pos (xs : List Int) (x : Int) (mem : x ∈ xs) (pos : 0 < x) :
    0 < positiveRank xs x := by
  have hx : x.toNat ∈ 0 :: xs.map Int.toNat := by
    simp [List.mem_map.mpr ⟨x, mem, rfl⟩]
  have hz : 0 ∈ 0 :: xs.map Int.toNat := by simp
  have h := rank_le_iff (0 :: xs.map Int.toNat) x.toNat 0 hx hz
  simp only [rank_zero] at h
  unfold positiveRank
  omega

theorem canonical_order (xs : List Int) (x y : Int) (hx : x ∈ xs) (hy : y ∈ xs) :
    canonical xs x ≤ canonical xs y ↔ x ≤ y := by
  by_cases px : x ≤ 0 <;> by_cases py : y ≤ 0
  · simp [canonical, px, py]
  · have hp := positiveRank_pos xs y hy (by omega)
    simp only [canonical, px, py, ite_true, ite_false]
    omega
  · have hp := positiveRank_pos xs x hx (by omega)
    simp only [canonical, px, py, ite_true, ite_false]
    omega
  · have hx' : x.toNat ∈ 0 :: xs.map Int.toNat := by simp [List.mem_map.mpr ⟨x, hx, rfl⟩]
    have hy' : y.toNat ∈ 0 :: xs.map Int.toNat := by simp [List.mem_map.mpr ⟨y, hy, rfl⟩]
    have h := rank_le_iff (0 :: xs.map Int.toNat) x.toNat y.toNat hx' hy'
    simp only [canonical, px, py, ite_false, positiveRank]
    omega

theorem canonical_sentinel (xs : List Int) (x : Int) (mem : x ∈ xs) :
    sentinel (canonical xs x) = sentinel x := by
  by_cases hx : x ≤ 0
  · simp [canonical, hx]
  · have hp := positiveRank_pos xs x mem (by omega)
    have hn : positiveRank xs x ≠ 0 := by omega
    simp [canonical, sentinel, hx, hn]

theorem sentinel_nonpositive {x y : Int} (h : sentinel x = sentinel y) (hx : x ≤ 0) : x = y := by
  by_cases hy : y ≤ 0 <;> simp [sentinel, hx, hy] at h
  exact h

theorem sentinel_positive {x y : Int} (h : sentinel x = sentinel y) (hx : 0 < x) : 0 < y := by
  by_cases hy : y ≤ 0
  · have hn : ¬ x ≤ 0 := by omega
    simp [sentinel, hn, hy] at h
  · omega

theorem canonical_congr {I : Type} (f g : I → Int) (is : List I)
    (order : ∀ i j, f i ≤ f j ↔ g i ≤ g j)
    (sentinels : ∀ i, sentinel (f i) = sentinel (g i)) (k : I) :
    canonical (is.map f) (f k) = canonical (is.map g) (g k) := by
  by_cases hk : f k ≤ 0
  · have eq := sentinel_nonpositive (sentinels k) hk
    simp [canonical, hk, ← eq]
  · have gk := sentinel_positive (sentinels k) (by omega : 0 < f k)
    let fp : Option I → Nat := fun i => i.elim 0 (fun i => (f i).toNat)
    let gp : Option I → Nat := fun i => i.elim 0 (fun i => (g i).toNat)
    have same (i j : Option I) : fp i ≤ fp j ↔ gp i ≤ gp j := by
      cases i with
      | none => simp [fp, gp]
      | some i =>
        cases j with
        | none =>
          by_cases hi : f i ≤ 0
          · have eq := sentinel_nonpositive (sentinels i) hi
            simp [fp, gp, eq]
          · have hg := sentinel_positive (sentinels i) (by omega : 0 < f i)
            simp only [fp, gp, Option.elim_some, Option.elim_none]
            omega
        | some j =>
          have ho := order i j
          have eqi := sentinels i
          have eqj := sentinels j
          by_cases hi : f i ≤ 0 <;> by_cases hj : f j ≤ 0
          · have ei := sentinel_nonpositive eqi hi
            have ej := sentinel_nonpositive eqj hj
            simp [fp, gp, ei, ej]
          · have ei := sentinel_nonpositive eqi hi
            have gj := sentinel_positive eqj (by omega : 0 < f j)
            simp only [fp, gp, Option.elim_some]
            omega
          · have ej := sentinel_nonpositive eqj hj
            have gi := sentinel_positive eqi (by omega : 0 < f i)
            simp only [fp, gp, Option.elim_some]
            omega
          · have gi := sentinel_positive eqi (by omega : 0 < f i)
            have gj := sentinel_positive eqj (by omega : 0 < f j)
            simp only [fp, gp, Option.elim_some]
            omega
    have ranks := rank_congr fp gp (none :: is.map some) same (some k)
    have hn : ¬ g k ≤ 0 := by omega
    simp only [canonical, hk, hn, ite_false]
    unfold positiveRank
    congr 1
    simpa [fp, gp, List.map_map, Function.comp_def] using ranks

theorem canonical_keys_equivalent {I : Type} (f g : I → Int) (is : List I) (complete : ∀ i, i ∈ is) :
    (∀ i, canonical (is.map f) (f i) = canonical (is.map g) (g i)) ↔
    ((∀ i j, f i ≤ f j ↔ g i ≤ g j) ∧ (∀ i, sentinel (f i) = sentinel (g i))) := by
  constructor
  · intro h
    have hf (i : I) : f i ∈ is.map f := List.mem_map.mpr ⟨i, complete i, rfl⟩
    have hg (i : I) : g i ∈ is.map g := List.mem_map.mpr ⟨i, complete i, rfl⟩
    constructor
    · intro i j
      rw [← canonical_order _ _ _ (hf i) (hf j), ← canonical_order _ _ _ (hg i) (hg j), h i, h j]
    · intro i
      rw [← canonical_sentinel _ _ (hf i), ← canonical_sentinel _ _ (hg i), h i]
  · rintro ⟨ho, hs⟩ i
    exact canonical_congr f g is ho hs i
end TlxOptimization.NestedRule
