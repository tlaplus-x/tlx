/- Homogeneous keyed-state rule IR for disjoint products of full permutation groups.
All key equality, group membership, quantifiers, cardinalities, map reads/writes
and scalar/optional key slot reads/writes are explicit.
Semantic leaves receive key-free payloads, cardinalities and core state only. -/
set_option autoImplicit false
namespace TlxOptimization.KeyedRule
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

theorem Permutation.injective {K : Type} (p : Permutation K) {x y : K} :
    p.toFun x = p.toFun y ↔ x = y := by
  constructor
  · intro h
    have := congrArg p.invFun h
    simpa only [p.left] using this
  · intro h; exact congrArg p.toFun h

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

abbrev KeyVal (K A : Type) := Sum K A
abbrev Environment (K : Type) := Nat → K
abbrev Maps (M K V : Type) := M → K → V
abbrev Slots (S K A : Type) := S → KeyVal K A
abbrev State (C M S K V A : Type) := C × Maps M K V × Slots S K A

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

def rename {d : Nat} {sizes : Fin d → Nat} {C M S V A : Type} (p : GroupPerm sizes)
    (st : State C M S (Key sizes) V A) : State C M S (Key sizes) V A :=
  (st.1, renameMaps p st.2.1, renameSlots p st.2.2)

theorem renameKeys_push {d : Nat} {sizes : Fin d → Nat} (p : GroupPerm sizes)
    (keys : Environment (Key sizes)) (k : Key sizes) :
    renameKeys p (push keys k) = push (renameKeys p keys) (p.toFun k) := by
  funext i
  cases i <;> rfl

theorem renameKeyVal_injective {d : Nat} {sizes : Fin d → Nat} {A : Type}
    (p : GroupPerm sizes) {x y : KeyVal (Key sizes) A} :
    renameKeyVal p x = renameKeyVal p y ↔ x = y := by
  cases x <;> cases y <;> simp only [renameKeyVal, Sum.inl.injEq, Sum.inr.injEq, p.injective, reduceCtorEq]

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
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨q.toFun x, by simpa only [q.left] using hx, q.left x⟩)
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

def read {M K V : Type} (r : Maps M K V) (keys : Environment K) (reads : List (M × Nat)) : List V :=
  reads.map (fun item => r item.1 (keys item.2))

theorem read_rename {d : Nat} {sizes : Fin d → Nat} {M V : Type} (p : GroupPerm sizes)
    (r : Maps M (Key sizes) V) (keys : Environment (Key sizes)) (reads : List (M × Nat)) :
    read (renameMaps p r) (renameKeys p keys) reads = read r keys reads := by
  simp [read, renameMaps, renameKeys, p.left]

def readSlotMaps {M S K V A : Type} (r : Maps M K V) (u : Slots S K A)
    (reads : List (M × S)) : List (Option V) :=
  reads.map (fun item => match u item.2 with | .inl k => some (r item.1 k) | .inr _ => none)

theorem readSlotMaps_rename {d : Nat} {sizes : Fin d → Nat} {M S V A : Type} (p : GroupPerm sizes)
    (r : Maps M (Key sizes) V) (u : Slots S (Key sizes) A) (reads : List (M × S)) :
    readSlotMaps (renameMaps p r) (renameSlots p u) reads = readSlotMaps r u reads := by
  unfold readSlotMaps
  apply List.map_congr_left
  intro item _
  simp only [renameSlots]
  cases u item.2 with
  | inl k => simp only [renameKeyVal, renameMaps, p.left]
  | inr a => rfl

def readSlotFixed {S K A : Type} (u : Slots S K A) (reads : List S) : List (Option A) :=
  reads.map (fun s => match u s with | .inl _ => none | .inr a => some a)

theorem readSlotFixed_rename {d : Nat} {sizes : Fin d → Nat} {S A : Type} (p : GroupPerm sizes)
    (u : Slots S (Key sizes) A) (reads : List S) :
    readSlotFixed (renameSlots p u) reads = readSlotFixed u reads := by
  unfold readSlotFixed
  apply List.map_congr_left
  intro s _
  simp only [renameSlots]
  cases u s <;> rfl

inductive Test (d : Nat) (M S : Type) where
  | truth (value : Bool)
  | leaf (id : Nat) (reads : List (M × Nat)) (slotReads : List (M × S)) (fixedReads : List S)
  | equal (left right : KeyRef S)
  | inGroup (key : KeyRef S) (mask : GroupMask d)
  | conj (left right : Test d M S)
  | disj (left right : Test d M S)
  | neg (body : Test d M S)
  | all (mask : GroupMask d) (body : Test d M S)
  | some (mask : GroupMask d) (body : Test d M S)
  | bindCount (mask : GroupMask d) (pred body : Test d M S)

def Test.eval {d : Nat} {sizes : Fin d → Nat} {M S V A : Type}
    (leaf : Nat → List V → List (Option V) → List (Option A) → List Nat → Prop)
    (fixedAtom : Nat → A) (r : Maps M (Key sizes) V) (u : Slots S (Key sizes) A)
    (keys : Environment (Key sizes)) (nats : List Nat) : Test d M S → Prop := by
  classical
  exact fun t => match t with
    | .truth value => value = true
    | .leaf id reads sreads freads =>
        leaf id (read r keys reads) (readSlotMaps r u sreads) (readSlotFixed u freads) nats
    | .equal a b => evalKeyRef fixedAtom u keys a = evalKeyRef fixedAtom u keys b
    | .inGroup ref mask =>
        match evalKeyRef fixedAtom u keys ref with
        | .inl k => mask k.1 = true
        | .inr _ => False
    | .conj a b => a.eval leaf fixedAtom r u keys nats ∧ b.eval leaf fixedAtom r u keys nats
    | .disj a b => a.eval leaf fixedAtom r u keys nats ∨ b.eval leaf fixedAtom r u keys nats
    | .neg a => ¬ a.eval leaf fixedAtom r u keys nats
    | .all mask a => ∀ k : Key sizes, mask k.1 = true → a.eval leaf fixedAtom r u (push keys k) nats
    | .some mask a => ∃ k : Key sizes, mask k.1 = true ∧ a.eval leaf fixedAtom r u (push keys k) nats
    | .bindCount mask pred body =>
        let n := countKeys sizes mask (fun k => decide (pred.eval leaf fixedAtom r u (push keys k) nats))
        body.eval leaf fixedAtom r u keys (n :: nats)

theorem Test.equivariant {d : Nat} {sizes : Fin d → Nat} {M S V A : Type} (p : GroupPerm sizes)
    (leaf : Nat → List V → List (Option V) → List (Option A) → List Nat → Prop)
    (fixedAtom : Nat → A) (r : Maps M (Key sizes) V) (u : Slots S (Key sizes) A)
    (test : Test d M S) (keys : Environment (Key sizes)) (nats : List Nat) :
    test.eval leaf fixedAtom (renameMaps p r) (renameSlots p u) (renameKeys p keys) nats ↔
      test.eval leaf fixedAtom r u keys nats := by
  classical
  induction test generalizing keys nats with
  | truth value => rfl
  | leaf id reads sreads freads =>
    simp only [Test.eval, read_rename, readSlotMaps_rename, readSlotFixed_rename]
  | equal a b =>
    simp only [Test.eval, evalKeyRef_rename, renameKeyVal_injective]
  | inGroup ref mask =>
    simp only [Test.eval, evalKeyRef_rename]
    cases evalKeyRef fixedAtom u keys ref <;> rfl
  | conj a b ha hb => exact and_congr (ha keys nats) (hb keys nats)
  | disj a b ha hb => exact or_congr (ha keys nats) (hb keys nats)
  | neg a ha => exact not_congr (ha keys nats)
  | all mask a ha =>
    constructor
    · intro h k hm
      apply (ha (push keys k) nats).mp
      rw [renameKeys_push]
      exact h (p.toFun k) hm
    · intro h k hm
      have hp := (ha (push keys (p.invFun k)) nats).mpr (h (p.invFun k) hm)
      simpa only [renameKeys_push, p.right] using hp
  | some mask a ha =>
    constructor
    · rintro ⟨k, hm, h⟩
      refine ⟨p.invFun k, hm, (ha (push keys (p.invFun k)) nats).mp ?_⟩
      simpa only [renameKeys_push, p.right] using h
    · rintro ⟨k, hm, h⟩
      refine ⟨p.toFun k, hm, ?_⟩
      have hp := (ha (push keys k) nats).mpr h
      simpa only [renameKeys_push] using hp
  | bindCount mask pred body hpred hbody =>
    simp only [Test.eval]
    have hc : countKeys sizes mask (fun k => decide (pred.eval leaf fixedAtom (renameMaps p r) (renameSlots p u) (push (renameKeys p keys) k) nats)) =
        countKeys sizes mask (fun k => decide (pred.eval leaf fixedAtom r u (push keys k) nats)) := by
      have hpred' : (fun k => decide (pred.eval leaf fixedAtom (renameMaps p r) (renameSlots p u) (push (renameKeys p keys) k) nats)) =
          (fun k => decide (pred.eval leaf fixedAtom r u (push keys (p.invFun k)) nats)) := by
        funext k
        have heq := hpred (push keys (p.invFun k)) nats
        rw [renameKeys_push, p.right] at heq
        exact propext heq ▸ rfl
      rw [hpred']
      exact countKeys_rename p mask (fun k => decide (pred.eval leaf fixedAtom r u (push keys k) nats))
    rw [hc]
    exact hbody keys _

inductive ValueExpr (d : Nat) (M S : Type) where
  | leaf (id : Nat) (reads : List (M × Nat)) (slotReads : List (M × S)) (fixedReads : List S)
  | branch (condition : Test d M S) (yes no : ValueExpr d M S)
  | bindCount (mask : GroupMask d) (pred : Test d M S) (body : ValueExpr d M S)

def ValueExpr.eval {d : Nat} {sizes : Fin d → Nat} {M S V A : Type}
    (test : Nat → List V → List (Option V) → List (Option A) → List Nat → Prop)
    (value : Nat → List V → List (Option V) → List (Option A) → List Nat → V)
    (fixedAtom : Nat → A) (r : Maps M (Key sizes) V) (u : Slots S (Key sizes) A)
    (keys : Environment (Key sizes)) (nats : List Nat) : ValueExpr d M S → V := by
  classical
  exact fun e => match e with
    | .leaf id reads sreads freads =>
        value id (read r keys reads) (readSlotMaps r u sreads) (readSlotFixed u freads) nats
    | .branch condition yes no =>
        if condition.eval test fixedAtom r u keys nats then
          yes.eval test value fixedAtom r u keys nats
        else
          no.eval test value fixedAtom r u keys nats
    | .bindCount mask pred body =>
        let n := countKeys sizes mask (fun k => decide (pred.eval test fixedAtom r u (push keys k) nats))
        body.eval test value fixedAtom r u keys (n :: nats)

theorem ValueExpr.equivariant {d : Nat} {sizes : Fin d → Nat} {M S V A : Type} (p : GroupPerm sizes)
    (test : Nat → List V → List (Option V) → List (Option A) → List Nat → Prop)
    (value : Nat → List V → List (Option V) → List (Option A) → List Nat → V)
    (fixedAtom : Nat → A) (r : Maps M (Key sizes) V) (u : Slots S (Key sizes) A)
    (keys : Environment (Key sizes)) (nats : List Nat) (e : ValueExpr d M S) :
    e.eval test value fixedAtom (renameMaps p r) (renameSlots p u) (renameKeys p keys) nats =
      e.eval test value fixedAtom r u keys nats := by
  classical
  induction e generalizing keys nats with
  | leaf id reads sreads freads =>
    simp only [ValueExpr.eval, read_rename, readSlotMaps_rename, readSlotFixed_rename]
  | branch condition yes no hy hn =>
    simp only [ValueExpr.eval, hy, hn]
    rw [propext (Test.equivariant p test fixedAtom r u condition keys nats)]
  | bindCount mask pred body hbody =>
    simp only [ValueExpr.eval]
    have hc : countKeys sizes mask (fun k => decide (pred.eval test fixedAtom (renameMaps p r) (renameSlots p u) (push (renameKeys p keys) k) nats)) =
        countKeys sizes mask (fun k => decide (pred.eval test fixedAtom r u (push keys k) nats)) := by
      have hpred' : (fun k => decide (pred.eval test fixedAtom (renameMaps p r) (renameSlots p u) (push (renameKeys p keys) k) nats)) =
          (fun k => decide (pred.eval test fixedAtom r u (push keys (p.invFun k)) nats)) := by
        funext k
        have heq := Test.equivariant p test fixedAtom r u pred (push keys (p.invFun k)) nats
        rw [renameKeys_push, p.right] at heq
        exact propext heq ▸ rfl
      rw [hpred']
      exact countKeys_rename p mask (fun k => decide (pred.eval test fixedAtom r u (push keys k) nats))
    rw [hc]
    exact hbody keys _

inductive SlotExpr (d : Nat) (M S : Type) where
  | ref (target : KeyRef S)
  | fixedVal (id : Nat) (reads : List (M × Nat)) (slotReads : List (M × S)) (fixedReads : List S)
  | branch (condition : Test d M S) (yes no : SlotExpr d M S)
  | bindCount (mask : GroupMask d) (pred : Test d M S) (body : SlotExpr d M S)

def SlotExpr.eval {d : Nat} {sizes : Fin d → Nat} {M S V A : Type}
    (test : Nat → List V → List (Option V) → List (Option A) → List Nat → Prop)
    (fixedVal : Nat → List V → List (Option V) → List (Option A) → List Nat → A)
    (fixedAtom : Nat → A) (r : Maps M (Key sizes) V) (u : Slots S (Key sizes) A)
    (keys : Environment (Key sizes)) (nats : List Nat) : SlotExpr d M S → KeyVal (Key sizes) A := by
  classical
  exact fun e => match e with
    | .ref target => evalKeyRef fixedAtom u keys target
    | .fixedVal id reads sreads freads =>
        .inr (fixedVal id (read r keys reads) (readSlotMaps r u sreads) (readSlotFixed u freads) nats)
    | .branch condition yes no =>
        if condition.eval test fixedAtom r u keys nats then
          yes.eval test fixedVal fixedAtom r u keys nats
        else
          no.eval test fixedVal fixedAtom r u keys nats
    | .bindCount mask pred body =>
        let n := countKeys sizes mask (fun k => decide (pred.eval test fixedAtom r u (push keys k) nats))
        body.eval test fixedVal fixedAtom r u keys (n :: nats)

theorem SlotExpr.equivariant {d : Nat} {sizes : Fin d → Nat} {M S V A : Type} (p : GroupPerm sizes)
    (test : Nat → List V → List (Option V) → List (Option A) → List Nat → Prop)
    (fixedVal : Nat → List V → List (Option V) → List (Option A) → List Nat → A)
    (fixedAtom : Nat → A) (r : Maps M (Key sizes) V) (u : Slots S (Key sizes) A)
    (keys : Environment (Key sizes)) (nats : List Nat) (e : SlotExpr d M S) :
    e.eval test fixedVal fixedAtom (renameMaps p r) (renameSlots p u) (renameKeys p keys) nats =
      renameKeyVal p (e.eval test fixedVal fixedAtom r u keys nats) := by
  classical
  induction e generalizing keys nats with
  | ref target => exact evalKeyRef_rename p fixedAtom u keys target
  | fixedVal id reads sreads freads =>
    simp only [SlotExpr.eval, read_rename, readSlotMaps_rename, readSlotFixed_rename, renameKeyVal]
  | branch condition yes no hy hn =>
    simp only [SlotExpr.eval]
    rw [propext (Test.equivariant p test fixedAtom r u condition keys nats)]
    split <;> simp only [hy, hn]
  | bindCount mask pred body hbody =>
    simp only [SlotExpr.eval]
    have hc : countKeys sizes mask (fun k => decide (pred.eval test fixedAtom (renameMaps p r) (renameSlots p u) (push (renameKeys p keys) k) nats)) =
        countKeys sizes mask (fun k => decide (pred.eval test fixedAtom r u (push keys k) nats)) := by
      have hpred' : (fun k => decide (pred.eval test fixedAtom (renameMaps p r) (renameSlots p u) (push (renameKeys p keys) k) nats)) =
          (fun k => decide (pred.eval test fixedAtom r u (push keys (p.invFun k)) nats)) := by
        funext k
        have heq := Test.equivariant p test fixedAtom r u pred (push keys (p.invFun k)) nats
        rw [renameKeys_push, p.right] at heq
        exact propext heq ▸ rfl
      rw [hpred']
      exact countKeys_rename p mask (fun k => decide (pred.eval test fixedAtom r u (push keys k) nats))
    rw [hc]
    exact hbody keys _

inductive Write (d : Nat) (M S : Type) where
  | point (map : M) (target : KeyRef S) (value : ValueExpr d M S)
  | all (map : M) (mask : GroupMask d) (value : ValueExpr d M S)

def Write.apply {d : Nat} {sizes : Fin d → Nat} {M S V A : Type}
    (test : Nat → List V → List (Option V) → List (Option A) → List Nat → Prop)
    (value : Nat → List V → List (Option V) → List (Option A) → List Nat → V)
    (fixedAtom : Nat → A) (original : Maps M (Key sizes) V) (u : Slots S (Key sizes) A)
    (keys : Environment (Key sizes)) (current : Maps M (Key sizes) V) :
    Write d M S → Maps M (Key sizes) V := by
  classical
  exact fun w => match w with
    | .point map target val =>
        match evalKeyRef fixedAtom u keys target with
        | .inl tk => fun m k => if m = map ∧ k = tk then val.eval test value fixedAtom original u keys [] else current m k
        | .inr _ => current
    | .all map mask val =>
        fun m k => if m = map ∧ mask k.1 = true then val.eval test value fixedAtom original u (push keys k) [] else current m k

theorem Write.equivariant {d : Nat} {sizes : Fin d → Nat} {M S V A : Type} (p : GroupPerm sizes)
    (test : Nat → List V → List (Option V) → List (Option A) → List Nat → Prop)
    (value : Nat → List V → List (Option V) → List (Option A) → List Nat → V)
    (fixedAtom : Nat → A) (original current : Maps M (Key sizes) V) (u : Slots S (Key sizes) A)
    (keys : Environment (Key sizes)) (w : Write d M S) :
    w.apply test value fixedAtom (renameMaps p original) (renameSlots p u) (renameKeys p keys) (renameMaps p current) =
      renameMaps p (w.apply test value fixedAtom original u keys current) := by
  classical
  cases w with
  | point map target val =>
    simp only [Write.apply, evalKeyRef_rename]
    cases evalKeyRef fixedAtom u keys target with
    | inl tk =>
      funext m k
      have eq : k = p.toFun tk ↔ p.invFun k = tk := by
        constructor
        · intro h; rw [h, p.left]
        · intro h; rw [← h, p.right]
      simp only [renameKeyVal, ValueExpr.equivariant, renameMaps, eq]
    | inr a => rfl
  | all map mask val =>
    funext m k
    simp only [Write.apply, renameMaps]
    have hval := ValueExpr.equivariant p test value fixedAtom original u (push keys (p.invFun k)) [] val
    rw [renameKeys_push, p.right] at hval
    simp only [GroupPerm.invFun, hval]
    rfl

def update {d : Nat} {sizes : Fin d → Nat} {M S V A : Type}
    (test : Nat → List V → List (Option V) → List (Option A) → List Nat → Prop)
    (value : Nat → List V → List (Option V) → List (Option A) → List Nat → V)
    (fixedAtom : Nat → A) (r : Maps M (Key sizes) V) (u : Slots S (Key sizes) A)
    (keys : Environment (Key sizes)) (writes : List (Write d M S)) : Maps M (Key sizes) V :=
  writes.foldl (fun current w => w.apply test value fixedAtom r u keys current) r

theorem update_equivariant {d : Nat} {sizes : Fin d → Nat} {M S V A : Type} (p : GroupPerm sizes)
    (test : Nat → List V → List (Option V) → List (Option A) → List Nat → Prop)
    (value : Nat → List V → List (Option V) → List (Option A) → List Nat → V)
    (fixedAtom : Nat → A) (r : Maps M (Key sizes) V) (u : Slots S (Key sizes) A)
    (keys : Environment (Key sizes)) (writes : List (Write d M S)) :
    update test value fixedAtom (renameMaps p r) (renameSlots p u) (renameKeys p keys) writes =
      renameMaps p (update test value fixedAtom r u keys writes) := by
  have fold (ws : List (Write d M S)) (current : Maps M (Key sizes) V) :
      ws.foldl (fun r' w => w.apply test value fixedAtom (renameMaps p r) (renameSlots p u) (renameKeys p keys) r') (renameMaps p current) =
      renameMaps p (ws.foldl (fun r' w => w.apply test value fixedAtom r u keys r') current) := by
    induction ws generalizing current with
    | nil => rfl
    | cons w ws ih =>
      simp only [List.foldl_cons, Write.equivariant]
      exact ih _
  exact fold writes r

structure SlotWrite (d : Nat) (M S : Type) where
  slot : S
  value : SlotExpr d M S

def SlotWrite.apply {d : Nat} {sizes : Fin d → Nat} {M S V A : Type}
    (test : Nat → List V → List (Option V) → List (Option A) → List Nat → Prop)
    (fixedVal : Nat → List V → List (Option V) → List (Option A) → List Nat → A)
    (fixedAtom : Nat → A) (r : Maps M (Key sizes) V) (original : Slots S (Key sizes) A)
    (keys : Environment (Key sizes)) (current : Slots S (Key sizes) A) (w : SlotWrite d M S) :
    Slots S (Key sizes) A := by
  classical
  exact fun s => if s = w.slot then w.value.eval test fixedVal fixedAtom r original keys [] else current s

theorem SlotWrite.equivariant {d : Nat} {sizes : Fin d → Nat} {M S V A : Type} (p : GroupPerm sizes)
    (test : Nat → List V → List (Option V) → List (Option A) → List Nat → Prop)
    (fixedVal : Nat → List V → List (Option V) → List (Option A) → List Nat → A)
    (fixedAtom : Nat → A) (r : Maps M (Key sizes) V) (original current : Slots S (Key sizes) A)
    (keys : Environment (Key sizes)) (w : SlotWrite d M S) :
    w.apply test fixedVal fixedAtom (renameMaps p r) (renameSlots p original) (renameKeys p keys) (renameSlots p current) =
      renameSlots p (w.apply test fixedVal fixedAtom r original keys current) := by
  classical
  funext s
  simp only [SlotWrite.apply, renameSlots]
  split
  · exact SlotExpr.equivariant p test fixedVal fixedAtom r original keys [] w.value
  · rfl

def updateSlots {d : Nat} {sizes : Fin d → Nat} {M S V A : Type}
    (test : Nat → List V → List (Option V) → List (Option A) → List Nat → Prop)
    (fixedVal : Nat → List V → List (Option V) → List (Option A) → List Nat → A)
    (fixedAtom : Nat → A) (r : Maps M (Key sizes) V) (u : Slots S (Key sizes) A)
    (keys : Environment (Key sizes)) (writes : List (SlotWrite d M S)) : Slots S (Key sizes) A :=
  writes.foldl (fun current w => w.apply test fixedVal fixedAtom r u keys current) u

theorem updateSlots_equivariant {d : Nat} {sizes : Fin d → Nat} {M S V A : Type} (p : GroupPerm sizes)
    (test : Nat → List V → List (Option V) → List (Option A) → List Nat → Prop)
    (fixedVal : Nat → List V → List (Option V) → List (Option A) → List Nat → A)
    (fixedAtom : Nat → A) (r : Maps M (Key sizes) V) (u : Slots S (Key sizes) A)
    (keys : Environment (Key sizes)) (writes : List (SlotWrite d M S)) :
    updateSlots test fixedVal fixedAtom (renameMaps p r) (renameSlots p u) (renameKeys p keys) writes =
      renameSlots p (updateSlots test fixedVal fixedAtom r u keys writes) := by
  have fold (ws : List (SlotWrite d M S)) (current : Slots S (Key sizes) A) :
      ws.foldl (fun u' w => w.apply test fixedVal fixedAtom (renameMaps p r) (renameSlots p u) (renameKeys p keys) u') (renameSlots p current) =
      renameSlots p (ws.foldl (fun u' w => w.apply test fixedVal fixedAtom r u keys u') current) := by
    induction ws generalizing current with
    | nil => rfl
    | cons w ws ih =>
      simp only [List.foldl_cons, SlotWrite.equivariant]
      exact ih _
  exact fold writes u

theorem rename_identity {d : Nat} {sizes : Fin d → Nat} {C M S V A : Type}
    (st : State C M S (Key sizes) V A) :
    rename GroupPerm.identity st = st := by
  rcases st with ⟨c, r, u⟩
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext m k; cases k; rfl
  · funext s
    change renameKeyVal GroupPerm.identity (u s) = u s
    cases u s with
    | inl k => cases k; rfl
    | inr a => rfl

theorem rename_then {d : Nat} {sizes : Fin d → Nat} {C M S V A : Type}
    (p q : GroupPerm sizes) (st : State C M S (Key sizes) V A) :
    rename (p.then q) st = rename q (rename p st) := by
  rcases st with ⟨c, r, u⟩
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  · funext s
    change renameKeyVal (p.then q) (u s) = renameKeyVal q (renameKeyVal p (u s))
    cases u s <;> rfl

theorem rename_inverse {d : Nat} {sizes : Fin d → Nat} {C M S V A : Type}
    (p : GroupPerm sizes) (st : State C M S (Key sizes) V A) :
    rename p.inverse (rename p st) = st := by
  rcases st with ⟨c, r, u⟩
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext m k
    exact congrArg (r m) (p.left k)
  · funext s
    change renameKeyVal p.inverse (renameKeyVal p (u s)) = u s
    cases u s with
    | inl k =>
      simp only [renameKeyVal, GroupPerm.inverse, GroupPerm.toFun, Permutation.inverse, (p k.1).left]
    | inr a => rfl

def Orbit {d : Nat} {sizes : Fin d → Nat} {C M S V A : Type}
    (s t : State C M S (Key sizes) V A) : Prop :=
  ∃ p : GroupPerm sizes, rename p s = t

def orbits {d : Nat} (sizes : Fin d → Nat) (C M S V A : Type) :
    Setoid (State C M S (Key sizes) V A) where
  r := Orbit
  iseqv := {
    refl := fun s => ⟨GroupPerm.identity, rename_identity s⟩
    symm := by
      rintro s t ⟨p, rfl⟩
      exact ⟨p.inverse, rename_inverse p s⟩
    trans := by
      rintro s t u ⟨p, rfl⟩ ⟨q, rfl⟩
      exact ⟨p.then q, rename_then p q s⟩ }

def project {d : Nat} {sizes : Fin d → Nat} {C M S V A : Type}
    (s : State C M S (Key sizes) V A) : Quotient (orbits sizes C M S V A) :=
  Quotient.mk _ s

theorem project_rename {d : Nat} {sizes : Fin d → Nat} {C M S V A : Type}
    (p : GroupPerm sizes) (s : State C M S (Key sizes) V A) :
    project (rename p s) = project s := by
  have h : project s = project (rename p s) := Quotient.sound (show Orbit s (rename p s) from ⟨p, rfl⟩)
  exact h.symm

structure Operations (d : Nat) (sizes : Fin d → Nat) (C M S V A B W : Type) where
  fixedAtom : Nat → A
  guard : B → Test d M S
  test : B → C → C → W → Nat → List V → List (Option V) → List (Option A) → List Nat → Prop
  writes : B → List (Write d M S)
  value : B → C → C → W → Nat → List V → List (Option V) → List (Option A) → List Nat → V
  slotWrites : B → List (SlotWrite d M S)
  fixedVal : B → C → C → W → Nat → List V → List (Option V) → List (Option A) → List Nat → A
  observation : Test d M S
  observe : C → Nat → List V → List (Option V) → List (Option A) → List Nat → Prop

structure Model (d : Nat) (sizes : Fin d → Nat) (C M S V A B W : Type)
    extends Operations d sizes C M S V A B W where
  initial : State C M S (Key sizes) V A → Prop

namespace Model
variable {d : Nat} {sizes : Fin d → Nat} {C M S V A B W : Type} (m : Model d sizes C M S V A B W)

def concrete : System (State C M S (Key sizes) V A) where
  initial := m.initial
  next s t := ∃ b w keys,
    (m.guard b).eval (m.test b s.1 t.1 w) m.fixedAtom s.2.1 s.2.2 keys [] ∧
    t = (t.1,
      update (m.test b s.1 t.1 w) (m.value b s.1 t.1 w) m.fixedAtom s.2.1 s.2.2 keys (m.writes b),
      updateSlots (m.test b s.1 t.1 w) (m.fixedVal b s.1 t.1 w) m.fixedAtom s.2.1 s.2.2 keys (m.slotWrites b))
  safe s := ∀ keys, m.observation.eval (m.observe s.1) m.fixedAtom s.2.1 s.2.2 keys []

theorem next_rename (p : GroupPerm sizes) (s t : State C M S (Key sizes) V A)
    (h : m.concrete.next s t) :
    m.concrete.next (rename p s) (rename p t) := by
  obtain ⟨b, w, keys, hg, ht⟩ := h
  refine ⟨b, w, renameKeys p keys, (Test.equivariant p _ _ _ _ _ keys []).mpr hg, ?_⟩
  have hu := update_equivariant p (m.test b s.1 t.1 w) (m.value b s.1 t.1 w) m.fixedAtom s.2.1 s.2.2 keys (m.writes b)
  have hs := updateSlots_equivariant p (m.test b s.1 t.1 w) (m.fixedVal b s.1 t.1 w) m.fixedAtom s.2.1 s.2.2 keys (m.slotWrites b)
  apply Prod.ext
  · rfl
  apply Prod.ext
  · change renameMaps p t.2.1 = update (m.test b s.1 t.1 w) (m.value b s.1 t.1 w) m.fixedAtom (renameMaps p s.2.1) (renameSlots p s.2.2) (renameKeys p keys) (m.writes b)
    rw [hu]
    exact congrArg (renameMaps p) (congrArg (fun x => x.2.1) ht)
  · change renameSlots p t.2.2 = updateSlots (m.test b s.1 t.1 w) (m.fixedVal b s.1 t.1 w) m.fixedAtom (renameMaps p s.2.1) (renameSlots p s.2.2) (renameKeys p keys) (m.slotWrites b)
    rw [hs]
    exact congrArg (renameSlots p) (congrArg (fun x => x.2.2) ht)

theorem safe_rename (p : GroupPerm sizes) (s : State C M S (Key sizes) V A) :
    m.concrete.safe (rename p s) ↔ m.concrete.safe s := by
  constructor
  · intro h keys
    exact (Test.equivariant p _ _ _ _ _ keys []).mp (h (renameKeys p keys))
  · intro h keys
    have hp := (Test.equivariant p (m.observe s.1) m.fixedAtom s.2.1 s.2.2 m.observation (renameKeys p.inverse keys) []).mpr (h (renameKeys p.inverse keys))
    have hk : renameKeys p (renameKeys p.inverse keys) = keys := by
      funext i
      exact p.right (keys i)
    rw [hk] at hp
    exact hp

def reduced : System (Quotient (orbits sizes C M S V A)) where
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
      refine ⟨rename p t, ?_, (project_rename p t).trans ht⟩
      have h := m.next_rename p x t hn
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

theorem deadlock_preserved (s : State C M S (Key sizes) V A) :
    (¬ ∃ t, m.concrete.next s t) ↔ (¬ ∃ a, m.reduced.next (project s) a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s a).mp ha
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨project t, (m.certificate.next s (project t)).mpr ⟨t, ht, rfl⟩⟩

theorem orbit_key_equivalent (s t : State C M S (Key sizes) V A) :
    project s = project t ↔ Orbit s t := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound (show (orbits sizes C M S V A).r s t from h)
end Model
end
end TlxOptimization.KeyedRule
