/- Certified composition of in-place threshold-counter saturation
(`ThresholdCounterCertificate.lean`) with generic recursive equivariant symmetry
(`EquivSymCertificate.lean`, `OrbitQuotient.lean`) over one shared concrete
source model via `TlxOptimization.compose` and `TlxOptimization.composeConstrained`.

Retained state `C` is `EquivRule.State CoreVar sizes A`; natural-number counters
are indexed by `Fin slotCount`, where symmetric-map counter slots are permuted by
`GroupPerm` and carry kernel-checked uniform caps (`capUniform : by decide`).
All counter tests, transfers, initial seeds, observations, constraints, and
action checks lower into explicit `EquivRule` formulas and expressions, so
equivariance of the projected system and commutation of `saturate` with
`GroupPerm` are proved in Lean with zero unproved bridge premises. -/
set_option autoImplicit false
namespace TlxOptimization.ThresholdSymRule
open TlxOptimization ThresholdCounterRule EquivRule
noncomputable section

def foldTestConj {k : Nat} {cap : Fin k → Nat} : List (Test cap) → Test cap
  | [] => .pure True
  | t :: ts => .conj t (foldTestConj ts)

def foldTestDisj {k : Nat} {cap : Fin k → Nat} : List (Test cap) → Test cap
  | [] => .pure False
  | t :: ts => .disj t (foldTestDisj ts)

theorem foldTestConj_eval {k : Nat} {cap : Fin k → Nat} (n : Fin k → Nat) :
    ∀ ts : List (Test cap), (foldTestConj ts).eval n ↔ ∀ t ∈ ts, t.eval n
  | [] => by simp [foldTestConj, Test.eval]
  | t :: ts => by
    simp only [foldTestConj, Test.eval, foldTestConj_eval n ts, List.mem_cons, forall_eq_or_imp]

theorem foldTestDisj_eval {k : Nat} {cap : Fin k → Nat} (n : Fin k → Nat) :
    ∀ ts : List (Test cap), (foldTestDisj ts).eval n ↔ ∃ t ∈ ts, t.eval n
  | [] => by simp [foldTestDisj, Test.eval]
  | t :: ts => by
    simp only [foldTestDisj, Test.eval, foldTestDisj_eval n ts, List.mem_cons, exists_eq_or_imp]

inductive SlotEntry (d : Nat) (slotCount : Nat) where
  | fixedKey (k : Fin slotCount) (atomId : Nat)
  | symGroup (off : Nat) (g : Fin d)

inductive SymTest (d : Nat) {slotCount : Nat}
    (cap : Fin slotCount → Nat) (CoreVar : Type) where
  | pure (f : Form d CoreVar)
  | cmpScalar (k : Fin slotCount) (op : Cmp) (thresh : Nat) (within : op.reqCap thresh ≤ cap k)
  | cmpMap (entries : List (SlotEntry d slotCount)) (keyExpr : EquivRule.Expr d CoreVar)
      (op : Cmp) (thresh : Nat)
  | neg (t : SymTest d cap CoreVar)
  | conj (t1 t2 : SymTest d cap CoreVar)
  | disj (t1 t2 : SymTest d cap CoreVar)
  | allGroup (g : Fin d) (body : SymTest d cap CoreVar)
  | someGroup (g : Fin d) (body : SymTest d cap CoreVar)
  | allFixed (atomIds : List Nat) (body : SymTest d cap CoreVar)
  | someFixed (atomIds : List Nat) (body : SymTest d cap CoreVar)

inductive SymSeed (d : Nat) (CoreVar : Type) where
  | const (n : Nat)
  | ite (cond : Form d CoreVar) (yes no : SymSeed d CoreVar)

inductive SymTransfer (d : Nat) {slotCount : Nat}
    (cap : Fin slotCount → Nat) (CoreVar : Type) where
  | keep
  | reset (r : Nat)
  | add (delta : Nat)
  | ite (cond : SymTest d cap CoreVar) (yes no : SymTransfer d cap CoreVar)
  | ifKeyEq (keyExpr : EquivRule.Expr d CoreVar) (yes no : SymTransfer d cap CoreVar)

def allFin (n : Nat) (p : Fin n → Bool) : Bool :=
  (List.finRange n).all p

theorem allFin_iff {n : Nat} {p : Fin n → Bool} :
    allFin n p = true ↔ ∀ i : Fin n, p i = true := by
  simp [allFin]

def slotInfoMatches {d : Nat} {sizes : Fin d → Nat}
    (v : Option (Nat × Sigma (fun g : Fin d => Fin (sizes g))))
    (off : Nat) (g : Fin d) (j : Fin (sizes g)) : Bool :=
  match v with
  | some (off', ⟨g', j'⟩) => (off' == off) && (g'.val == g.val) && (j'.val == j.val)
  | none => false

theorem slotInfoMatches_eq {d : Nat} {sizes : Fin d → Nat}
    {v : Option (Nat × Sigma (fun g : Fin d => Fin (sizes g)))}
    {off : Nat} {g : Fin d} {j : Fin (sizes g)}
    (h : slotInfoMatches v off g j = true) :
    v = some (off, ⟨g, j⟩) := by
  cases v with
  | none => simp [slotInfoMatches] at h
  | some val =>
    rcases val with ⟨off', ⟨g', j'⟩⟩
    simp only [slotInfoMatches, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨rfl, hg⟩, hj⟩
    have hg' : g' = g := Fin.ext hg
    subst hg'
    have hj' : j' = j := Fin.ext hj
    subst hj'
    rfl

def entryValidB {d : Nat} {sizes : Fin d → Nat} {slotCount : Nat}
    (slotInfo : Fin slotCount → Option (Nat × Sigma (fun g : Fin d => Fin (sizes g))))
    (cap : Fin slotCount → Nat) (op : Cmp) (thresh : Nat) :
    SlotEntry d slotCount → Bool
  | .fixedKey k _ => (slotInfo k).isNone && decide (op.reqCap thresh ≤ cap k)
  | .symGroup off g =>
      if h : off + sizes g ≤ slotCount then
        allFin (sizes g) (fun j =>
          let hlt : off + j.val < slotCount := Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt off) h
          slotInfoMatches (slotInfo ⟨off + j.val, hlt⟩) off g j &&
            decide (op.reqCap thresh ≤ cap ⟨off + j.val, hlt⟩))
      else false

def entryValid {d : Nat} {sizes : Fin d → Nat} {slotCount : Nat}
    (slotInfo : Fin slotCount → Option (Nat × Sigma (fun g : Fin d => Fin (sizes g))))
    (cap : Fin slotCount → Nat) (op : Cmp) (thresh : Nat) :
    SlotEntry d slotCount → Prop
  | .fixedKey k _ => slotInfo k = none ∧ op.reqCap thresh ≤ cap k
  | .symGroup off g =>
      if h : off + sizes g ≤ slotCount then
        ∀ j : Fin (sizes g),
          let hlt : off + j.val < slotCount := Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt off) h
          slotInfo ⟨off + j.val, hlt⟩ = some (off, ⟨g, j⟩) ∧ op.reqCap thresh ≤ cap ⟨off + j.val, hlt⟩
      else False

theorem entryValidB_sound {d : Nat} {sizes : Fin d → Nat} {slotCount : Nat}
    {slotInfo : Fin slotCount → Option (Nat × Sigma (fun g : Fin d => Fin (sizes g)))}
    {cap : Fin slotCount → Nat} {op : Cmp} {thresh : Nat} {e : SlotEntry d slotCount}
    (h : entryValidB slotInfo cap op thresh e = true) :
    entryValid slotInfo cap op thresh e := by
  cases e with
  | fixedKey k _ =>
    simp only [entryValidB, Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at h
    exact h
  | symGroup off g =>
    by_cases hle : off + sizes g ≤ slotCount
    · simp only [entryValidB, entryValid, hle, ↓reduceDIte] at h ⊢
      intro j
      have hj := allFin_iff.mp h j
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
      exact ⟨slotInfoMatches_eq hj.1, hj.2⟩
    · simp only [entryValidB, hle, ↓reduceDIte] at h
      cases h

def SymTest.validB {d : Nat} {sizes : Fin d → Nat} {slotCount : Nat} {CoreVar : Type}
    (slotInfo : Fin slotCount → Option (Nat × Sigma (fun g : Fin d => Fin (sizes g))))
    (cap : Fin slotCount → Nat) : SymTest d cap CoreVar → Bool
  | .pure _ => true
  | .cmpScalar k _ _ _ => (slotInfo k).isNone
  | .cmpMap entries _ op thresh => entries.all (entryValidB slotInfo cap op thresh)
  | .neg t => t.validB slotInfo cap
  | .conj t1 t2 => t1.validB slotInfo cap && t2.validB slotInfo cap
  | .disj t1 t2 => t1.validB slotInfo cap && t2.validB slotInfo cap
  | .allGroup _ body => body.validB slotInfo cap
  | .someGroup _ body => body.validB slotInfo cap
  | .allFixed _ body => body.validB slotInfo cap
  | .someFixed _ body => body.validB slotInfo cap

def SymTest.valid {d : Nat} {sizes : Fin d → Nat} {slotCount : Nat} {CoreVar : Type}
    (slotInfo : Fin slotCount → Option (Nat × Sigma (fun g : Fin d => Fin (sizes g))))
    (cap : Fin slotCount → Nat) : SymTest d cap CoreVar → Prop
  | .pure _ => True
  | .cmpScalar k _ _ _ => slotInfo k = none
  | .cmpMap entries _ op thresh => ∀ e ∈ entries, entryValid slotInfo cap op thresh e
  | .neg t => t.valid slotInfo cap
  | .conj t1 t2 => t1.valid slotInfo cap ∧ t2.valid slotInfo cap
  | .disj t1 t2 => t1.valid slotInfo cap ∧ t2.valid slotInfo cap
  | .allGroup _ body => body.valid slotInfo cap
  | .someGroup _ body => body.valid slotInfo cap
  | .allFixed _ body => body.valid slotInfo cap
  | .someFixed _ body => body.valid slotInfo cap

theorem SymTest.validB_sound {d : Nat} {sizes : Fin d → Nat} {slotCount : Nat} {CoreVar : Type}
    {slotInfo : Fin slotCount → Option (Nat × Sigma (fun g : Fin d => Fin (sizes g)))}
    {cap : Fin slotCount → Nat} :
    ∀ (t : SymTest d cap CoreVar), t.validB slotInfo cap = true → t.valid slotInfo cap
  | .pure _, _ => trivial
  | .cmpScalar _ _ _ _, h => Option.isNone_iff_eq_none.mp h
  | .cmpMap _ _ _ _, h => fun e he => entryValidB_sound (List.all_eq_true.mp h e he)
  | .neg t, h => SymTest.validB_sound t h
  | .conj t1 t2, h =>
      let ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
      ⟨SymTest.validB_sound t1 h1, SymTest.validB_sound t2 h2⟩
  | .disj t1 t2, h =>
      let ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
      ⟨SymTest.validB_sound t1 h1, SymTest.validB_sound t2 h2⟩
  | .allGroup _ body, h => SymTest.validB_sound body h
  | .someGroup _ body, h => SymTest.validB_sound body h
  | .allFixed _ body, h => SymTest.validB_sound body h
  | .someFixed _ body, h => SymTest.validB_sound body h

def SymTransfer.validB {d : Nat} {sizes : Fin d → Nat} {slotCount : Nat} {CoreVar : Type}
    (slotInfo : Fin slotCount → Option (Nat × Sigma (fun g : Fin d => Fin (sizes g))))
    (cap : Fin slotCount → Nat) : SymTransfer d cap CoreVar → Bool
  | .keep => true
  | .reset _ => true
  | .add _ => true
  | .ite cond yes no => cond.validB slotInfo cap && yes.validB slotInfo cap && no.validB slotInfo cap
  | .ifKeyEq _ yes no => yes.validB slotInfo cap && no.validB slotInfo cap

def SymTransfer.valid {d : Nat} {sizes : Fin d → Nat} {slotCount : Nat} {CoreVar : Type}
    (slotInfo : Fin slotCount → Option (Nat × Sigma (fun g : Fin d => Fin (sizes g))))
    (cap : Fin slotCount → Nat) : SymTransfer d cap CoreVar → Prop
  | .keep => True
  | .reset _ => True
  | .add _ => True
  | .ite cond yes no => cond.valid slotInfo cap ∧ yes.valid slotInfo cap ∧ no.valid slotInfo cap
  | .ifKeyEq _ yes no => yes.valid slotInfo cap ∧ no.valid slotInfo cap

theorem SymTransfer.validB_sound {d : Nat} {sizes : Fin d → Nat} {slotCount : Nat} {CoreVar : Type}
    {slotInfo : Fin slotCount → Option (Nat × Sigma (fun g : Fin d => Fin (sizes g)))}
    {cap : Fin slotCount → Nat} :
    ∀ (tr : SymTransfer d cap CoreVar), tr.validB slotInfo cap = true → tr.valid slotInfo cap
  | .keep, _ => trivial
  | .reset _, _ => trivial
  | .add _, _ => trivial
  | .ite cond yes no, h => by
      simp only [SymTransfer.validB, Bool.and_eq_true] at h
      exact ⟨SymTest.validB_sound cond h.1.1, SymTransfer.validB_sound yes h.1.2, SymTransfer.validB_sound no h.2⟩
  | .ifKeyEq _ yes no, h => by
      simp only [SymTransfer.validB, Bool.and_eq_true] at h
      exact ⟨SymTransfer.validB_sound yes h.1, SymTransfer.validB_sound no h.2⟩

def slotBoundsB {d : Nat} {sizes : Fin d → Nat} {slotCount : Nat}
    (slotInfo : Fin slotCount → Option (Nat × Sigma (fun g : Fin d => Fin (sizes g)))) : Bool :=
  allFin slotCount (fun i =>
    match slotInfo i with
    | none => true
    | some (off, ⟨g, j⟩) => (i.val == off + j.val) && decide (off + sizes g ≤ slotCount))

def slotClosedB {d : Nat} {sizes : Fin d → Nat} {slotCount : Nat}
    (slotInfo : Fin slotCount → Option (Nat × Sigma (fun g : Fin d => Fin (sizes g)))) : Bool :=
  allFin slotCount (fun i =>
    match slotInfo i with
    | none => true
    | some (off, ⟨g, _⟩) =>
        allFin (sizes g) (fun j' =>
          if h : off + j'.val < slotCount then
            slotInfoMatches (slotInfo ⟨off + j'.val, h⟩) off g j'
          else true))

def capUniformB {d : Nat} {sizes : Fin d → Nat} {slotCount : Nat}
    (slotInfo : Fin slotCount → Option (Nat × Sigma (fun g : Fin d => Fin (sizes g))))
    (cap : Fin slotCount → Nat) : Bool :=
  allFin slotCount (fun i =>
    match slotInfo i with
    | none => true
    | some (off, ⟨g, _⟩) =>
        allFin (sizes g) (fun j' =>
          if h : off + j'.val < slotCount then cap ⟨off + j'.val, h⟩ == cap i else true))

def templateUniformB {d : Nat} {sizes : Fin d → Nat} {slotCount templateCount : Nat}
    (slotInfo : Fin slotCount → Option (Nat × Sigma (fun g : Fin d => Fin (sizes g))))
    (slotTemplate : Fin slotCount → Fin templateCount) : Bool :=
  allFin slotCount (fun i =>
    match slotInfo i with
    | none => true
    | some (off, ⟨g, _⟩) =>
        allFin (sizes g) (fun j' =>
          if h : off + j'.val < slotCount then (slotTemplate ⟨off + j'.val, h⟩).val == (slotTemplate i).val else true))

structure Model (d : Nat) (sizes : Fin d → Nat) (CoreVar : Type)
    (slotCount templateCount branchCount : Nat) (A : Type) [HasNatAtom A] where
  ops : AtomOps A
  cap : Fin slotCount → Nat
  slotInfo : Fin slotCount → Option (Nat × Sigma (fun g : Fin d => Fin (sizes g)))
  fixedSlotAtom : Fin slotCount → Nat
  slotTemplate : Fin slotCount → Fin templateCount
  slotBounds : slotBoundsB slotInfo = true
  slotClosed : slotClosedB slotInfo = true
  capUniform : capUniformB slotInfo cap = true
  templateUniform : templateUniformB slotInfo slotTemplate = true
  initValid : Fin branchCount → Bool
  initBounds : Fin branchCount → List (SetPred d CoreVar)
  initGuard : Fin branchCount → Form d CoreVar
  initSeed : Fin branchCount → Fin templateCount → SymSeed d CoreVar
  stepValid : Fin branchCount → Bool
  stepBounds : Fin branchCount → List (SetPred d CoreVar)
  stepGuard : Fin branchCount → SymTest d cap CoreVar
  stepTransfer : Fin branchCount → Fin templateCount → SymTransfer d cap CoreVar
  obsTest : SymTest d cap CoreVar
  initObsTest : SymTest d cap CoreVar := .pure (.truth true)
  constraintTest : SymTest d cap CoreVar := .pure (.truth true)
  actionConstraintForm : Form d CoreVar := .truth true
  actionObsForm : Form d CoreVar := .truth true
  stepGuardValid : allFin branchCount (fun b => (stepGuard b).validB slotInfo cap) = true
  stepTransferValid : allFin branchCount (fun b => allFin templateCount (fun t => (stepTransfer b t).validB slotInfo cap)) = true
  obsValid : obsTest.validB slotInfo cap = true
  initObsValid : initObsTest.validB slotInfo cap = true
  constraintValid : constraintTest.validB slotInfo cap = true

namespace Model
variable {d : Nat} {sizes : Fin d → Nat} {CoreVar : Type}
  {slotCount templateCount branchCount : Nat} {A : Type} [HasNatAtom A]
  (m : Model d sizes CoreVar slotCount templateCount branchCount A)

theorem slotBounds_prop (i : Fin slotCount) :
    match m.slotInfo i with
    | none => True
    | some (off, ⟨g, j⟩) => i.val = off + j.val ∧ off + sizes g ≤ slotCount := by
  have hi := allFin_iff.mp m.slotBounds i
  cases h : m.slotInfo i with
  | none => trivial
  | some val =>
    rcases val with ⟨off, ⟨g, j⟩⟩
    rw [h] at hi
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hi
    exact hi

theorem slotClosed_prop (i : Fin slotCount) :
    match m.slotInfo i with
    | none => True
    | some (off, ⟨g, _⟩) => ∀ j' : Fin (sizes g), (h : off + j'.val < slotCount) →
        m.slotInfo ⟨off + j'.val, h⟩ = some (off, ⟨g, j'⟩) := by
  have hi := allFin_iff.mp m.slotClosed i
  cases h : m.slotInfo i with
  | none => trivial
  | some val =>
    rcases val with ⟨off, ⟨g, j⟩⟩
    rw [h] at hi
    intro j' hlt
    have hj := allFin_iff.mp hi j'
    simp only [hlt, ↓reduceDIte] at hj
    exact slotInfoMatches_eq hj

theorem capUniform_prop (i : Fin slotCount) :
    match m.slotInfo i with
    | none => True
    | some (off, ⟨g, _⟩) => ∀ j' : Fin (sizes g), (h : off + j'.val < slotCount) →
        m.cap ⟨off + j'.val, h⟩ = m.cap i := by
  have hi := allFin_iff.mp m.capUniform i
  cases h : m.slotInfo i with
  | none => trivial
  | some val =>
    rcases val with ⟨off, ⟨g, j⟩⟩
    rw [h] at hi
    intro j' hlt
    have hj := allFin_iff.mp hi j'
    simp only [hlt, ↓reduceDIte, beq_iff_eq] at hj
    exact hj

theorem templateUniform_prop (i : Fin slotCount) :
    match m.slotInfo i with
    | none => True
    | some (off, ⟨g, _⟩) => ∀ j' : Fin (sizes g), (h : off + j'.val < slotCount) →
        m.slotTemplate ⟨off + j'.val, h⟩ = m.slotTemplate i := by
  have hi := allFin_iff.mp m.templateUniform i
  cases h : m.slotInfo i with
  | none => trivial
  | some val =>
    rcases val with ⟨off, ⟨g, j⟩⟩
    rw [h] at hi
    intro j' hlt
    have hj := allFin_iff.mp hi j'
    simp only [hlt, ↓reduceDIte, beq_iff_eq] at hj
    exact Fin.ext hj

theorem stepGuardValid_prop (b : Fin branchCount) : (m.stepGuard b).valid m.slotInfo m.cap :=
  SymTest.validB_sound _ (allFin_iff.mp m.stepGuardValid b)

theorem stepTransferValid_prop (b : Fin branchCount) (t : Fin templateCount) :
    (m.stepTransfer b t).valid m.slotInfo m.cap :=
  SymTransfer.validB_sound _ (allFin_iff.mp (allFin_iff.mp m.stepTransferValid b) t)

theorem obsValid_prop : m.obsTest.valid m.slotInfo m.cap := SymTest.validB_sound _ m.obsValid
theorem initObsValid_prop : m.initObsTest.valid m.slotInfo m.cap := SymTest.validB_sound _ m.initObsValid
theorem constraintValid_prop : m.constraintTest.valid m.slotInfo m.cap := SymTest.validB_sound _ m.constraintValid

abbrev Core (_m : Model d sizes CoreVar slotCount templateCount branchCount A) :=
  EquivRule.State CoreVar sizes A
abbrev TState (_m : Model d sizes CoreVar slotCount templateCount branchCount A) :=
  EquivRule.State CoreVar sizes A × (Fin slotCount → Nat)
abbrev Witness (_m : Model d sizes CoreVar slotCount templateCount branchCount A) :=
  Fin branchCount × List (Val sizes A)

def permSlot (p : GroupPerm sizes) (i : Fin slotCount) : Fin slotCount :=
  match h : m.slotInfo i with
  | none => i
  | some (off, ⟨g, j⟩) =>
    ⟨off + ((p g).toFun j).val, by
      have hb := m.slotBounds_prop i
      rw [h] at hb
      have hj := ((p g).toFun j).isLt
      omega⟩

theorem permSlot_none (p : GroupPerm sizes) (i : Fin slotCount) (h : m.slotInfo i = none) :
    m.permSlot p i = i := by
  unfold permSlot
  split
  · rfl
  · rename_i h'
    rw [h] at h'
    cases h'

theorem permSlot_some (p : GroupPerm sizes) (i : Fin slotCount) {off : Nat} {g : Fin d} {j : Fin (sizes g)}
    (h : m.slotInfo i = some (off, ⟨g, j⟩)) :
    (m.permSlot p i).val = off + ((p g).toFun j).val ∧
      m.slotInfo (m.permSlot p i) = some (off, ⟨g, (p g).toFun j⟩) := by
  unfold permSlot
  split
  · rename_i h'; rw [h] at h'; cases h'
  · rename_i off' g' j' h'
    rw [h] at h'
    cases h'
    have hc := m.slotClosed_prop i
    rw [h] at hc
    exact ⟨rfl, hc ((p g).toFun j) _⟩

theorem permSlot_identity (i : Fin slotCount) :
    m.permSlot GroupPerm.identity i = i := by
  cases h : m.slotInfo i with
  | none => exact m.permSlot_none GroupPerm.identity i h
  | some val =>
    rcases val with ⟨off, ⟨g, j⟩⟩
    have hb := m.slotBounds_prop i
    rw [h] at hb
    have hp := (m.permSlot_some GroupPerm.identity i h).1
    exact Fin.ext (hp.trans hb.1.symm)

theorem permSlot_then (p q : GroupPerm sizes) (i : Fin slotCount) :
    m.permSlot (p.then q) i = m.permSlot q (m.permSlot p i) := by
  cases h : m.slotInfo i with
  | none =>
    rw [m.permSlot_none (p.then q) i h, m.permSlot_none p i h, m.permSlot_none q i h]
  | some val =>
    rcases val with ⟨off, ⟨g, j⟩⟩
    have hp := m.permSlot_some p i h
    have hq := m.permSlot_some q (m.permSlot p i) hp.2
    have hpq := m.permSlot_some (p.then q) i h
    exact Fin.ext (hpq.1.trans hq.1.symm)

theorem permSlot_left (p : GroupPerm sizes) (i : Fin slotCount) :
    m.permSlot p.inverse (m.permSlot p i) = i := by
  rw [← m.permSlot_then p p.inverse i, GroupPerm.then_inverse]
  exact m.permSlot_identity i

theorem permSlot_right (p : GroupPerm sizes) (i : Fin slotCount) :
    m.permSlot p (m.permSlot p.inverse i) = i := by
  have hinv : p.inverse.then p = GroupPerm.identity := by
    funext g
    have hr : (fun k => (p g).toFun ((p g).invFun k)) = id := funext (p g).right
    unfold GroupPerm.then GroupPerm.inverse GroupPerm.identity Permutation.then Permutation.inverse Permutation.identity
    simp only [hr]
  rw [← m.permSlot_then p.inverse p i, hinv]
  exact m.permSlot_identity i

theorem cap_permSlot (p : GroupPerm sizes) (i : Fin slotCount) :
    m.cap (m.permSlot p i) = m.cap i := by
  cases h : m.slotInfo i with
  | none => rw [m.permSlot_none p i h]
  | some val =>
    rcases val with ⟨off, ⟨g, j⟩⟩
    have hu := m.capUniform_prop i
    rw [h] at hu
    have hp := m.permSlot_some p i h
    have hfin : m.permSlot p i = ⟨off + ((p g).toFun j).val, by rw [← hp.1]; exact (m.permSlot p i).isLt⟩ :=
      Fin.ext hp.1
    rw [hfin]
    exact hu ((p g).toFun j) _

theorem template_permSlot (p : GroupPerm sizes) (i : Fin slotCount) :
    m.slotTemplate (m.permSlot p i) = m.slotTemplate i := by
  cases h : m.slotInfo i with
  | none => rw [m.permSlot_none p i h]
  | some val =>
    rcases val with ⟨off, ⟨g, j⟩⟩
    have hu := m.templateUniform_prop i
    rw [h] at hu
    have hp := m.permSlot_some p i h
    have hfin : m.permSlot p i = ⟨off + ((p g).toFun j).val, by rw [← hp.1]; exact (m.permSlot p i).isLt⟩ :=
      Fin.ext hp.1
    rw [hfin]
    exact hu ((p g).toFun j) _

def slotKeyVal (i : Fin slotCount) : Val sizes A :=
  match m.slotInfo i with
  | none => Val.atom (m.ops.atomVal (m.fixedSlotAtom i))
  | some (_, ⟨g, j⟩) => Val.key ⟨g, j⟩

theorem slotKeyVal_permSlot (p : GroupPerm sizes) (i : Fin slotCount) :
    m.slotKeyVal (m.permSlot p i) = renameVal p (m.slotKeyVal i) := by
  unfold slotKeyVal
  cases h : m.slotInfo i with
  | none =>
    rw [m.permSlot_none p i h, h]
    rfl
  | some val =>
    rcases val with ⟨off, ⟨g, j⟩⟩
    rw [(m.permSlot_some p i h).2]
    rfl

def renameCounters (p : GroupPerm sizes) (n : Fin slotCount → Nat) : Fin slotCount → Nat :=
  fun i => n (m.permSlot p.inverse i)

def renameTState (p : GroupPerm sizes) (s : m.TState) : m.TState :=
  (renameState p s.1, m.renameCounters p s.2)

def renameW (p : GroupPerm sizes) (w : m.Witness) : m.Witness :=
  (w.1, w.2.map (renameVal p))

theorem renameTState_identity (s : m.TState) :
    m.renameTState GroupPerm.identity s = s := by
  apply Prod.ext
  · exact renameState_identity s.1
  · funext i
    change s.2 (m.permSlot GroupPerm.identity.inverse i) = s.2 i
    have hi : GroupPerm.identity.inverse = (GroupPerm.identity : GroupPerm sizes) := rfl
    rw [hi, m.permSlot_identity]

theorem renameTState_then (p q : GroupPerm sizes) (s : m.TState) :
    m.renameTState (p.then q) s = m.renameTState q (m.renameTState p s) := by
  apply Prod.ext
  · exact renameState_then p q s.1
  · funext i
    change s.2 (m.permSlot (p.then q).inverse i) = s.2 (m.permSlot p.inverse (m.permSlot q.inverse i))
    have hinv : (p.then q).inverse = q.inverse.then p.inverse := rfl
    rw [hinv, m.permSlot_then]

theorem renameTState_inverse (p : GroupPerm sizes) (s : m.TState) :
    m.renameTState p.inverse (m.renameTState p s) = s := by
  rw [← m.renameTState_then p p.inverse s, GroupPerm.then_inverse]
  exact m.renameTState_identity s

theorem saturate_rename (p : GroupPerm sizes) (n : Fin slotCount → Nat) :
    saturate m.cap (m.renameCounters p n) = m.renameCounters p (saturate m.cap n) := by
  funext i
  simp only [saturate, renameCounters, m.cap_permSlot p.inverse i]

def evalEntryTest (kv : Val sizes A)
    (op : Cmp) (thresh : Nat) (e : SlotEntry d slotCount)
    (hv : entryValid m.slotInfo m.cap op thresh e) : Test m.cap :=
  match e, hv with
  | .fixedKey k atomId, hv =>
      .conj (.pure (kv = Val.atom (m.ops.atomVal atomId))) (.cmp k op thresh hv.2)
  | .symGroup off g, hv =>
      if h : off + sizes g ≤ slotCount then
        have hv' : ∀ j : Fin (sizes g),
            let hlt : off + j.val < slotCount := Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt off) h
            m.slotInfo ⟨off + j.val, hlt⟩ = some (off, ⟨g, j⟩) ∧ op.reqCap thresh ≤ m.cap ⟨off + j.val, hlt⟩ := by
          simpa only [entryValid, h, ↓reduceDIte] using hv
        foldTestDisj ((List.finRange (sizes g)).map (fun (j : Fin (sizes g)) =>
          let hlt : off + j.val < slotCount := Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt off) h
          let slot : Fin slotCount := ⟨off + j.val, hlt⟩
          .conj (.pure (kv = Val.key ⟨g, j⟩)) (.cmp slot op thresh (hv' j).2)))
      else False.elim (by simp only [entryValid, h, ↓reduceDIte] at hv)

theorem evalEntryTest_equivariant (p : GroupPerm sizes)
    (kv : Val sizes A) (op : Cmp) (thresh : Nat) (e : SlotEntry d slotCount)
    (hv : entryValid m.slotInfo m.cap op thresh e) (n : Fin slotCount → Nat) :
    (m.evalEntryTest (renameVal p kv) op thresh e hv).eval (m.renameCounters p n) ↔
      (m.evalEntryTest kv op thresh e hv).eval n := by
  cases e with
  | fixedKey k atomId =>
    simp only [evalEntryTest, Test.eval, renameCounters, m.permSlot_none p.inverse k hv.1]
    have hkv : (renameVal p kv = Val.atom (m.ops.atomVal atomId)) ↔ (kv = Val.atom (m.ops.atomVal atomId)) := by
      rw [← Val.rename_atom p (m.ops.atomVal atomId)]
      exact renameVal_injective p
    exact and_congr hkv Iff.rfl
  | symGroup off g =>
    by_cases h : off + sizes g ≤ slotCount
    · have hv' : ∀ j : Fin (sizes g),
          let hlt : off + j.val < slotCount := Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt off) h
          m.slotInfo ⟨off + j.val, hlt⟩ = some (off, ⟨g, j⟩) ∧ op.reqCap thresh ≤ m.cap ⟨off + j.val, hlt⟩ := by
        simpa only [entryValid, h, ↓reduceDIte] using hv
      simp only [evalEntryTest, h, ↓reduceDIte, foldTestDisj_eval, List.mem_map, List.mem_finRange, true_and]
      constructor
      · rintro ⟨_, ⟨j, rfl⟩, hkv, hcmp⟩
        refine ⟨_, ⟨(p g).invFun j, rfl⟩, ?_, ?_⟩
        · simp only [Test.eval] at hkv ⊢
          have := congrArg (renameVal p.inverse) hkv
          simpa only [renameVal_inverse, Val.rename_key, GroupPerm.toFun, GroupPerm.inverse, Permutation.inverse] using this
        · simp only [Test.eval, renameCounters] at hcmp ⊢
          have hj := (hv' j).1
          have hperm := m.permSlot_some p.inverse ⟨off + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt off) h⟩ hj
          have hfin : m.permSlot p.inverse ⟨off + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt off) h⟩ =
              ⟨off + ((p g).invFun j).val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left ((p g).invFun j).isLt off) h⟩ := Fin.ext hperm.1
          rwa [hfin] at hcmp
      · rintro ⟨_, ⟨j, rfl⟩, hkv, hcmp⟩
        refine ⟨_, ⟨(p g).toFun j, rfl⟩, ?_, ?_⟩
        · simp only [Test.eval] at hkv ⊢
          rw [hkv, Val.rename_key]; rfl
        · simp only [Test.eval, renameCounters] at hcmp ⊢
          have hj := (hv' ((p g).toFun j)).1
          have hperm := m.permSlot_some p.inverse ⟨off + ((p g).toFun j).val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left ((p g).toFun j).isLt off) h⟩ hj
          have hfin : m.permSlot p.inverse ⟨off + ((p g).toFun j).val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left ((p g).toFun j).isLt off) h⟩ =
              ⟨off + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt off) h⟩ := by
            apply Fin.ext
            have := hperm.1
            simpa only [GroupPerm.inverse, Permutation.inverse, (p g).left] using this
          rwa [hfin]
    · exact False.elim (by simp only [entryValid, h, ↓reduceDIte] at hv)

def evalSymTest (c c' : m.Core) (env : Env sizes A) :
    (t : SymTest d m.cap CoreVar) → t.valid m.slotInfo m.cap → Test m.cap
  | .pure f, _ => .pure (evalForm m.ops c c' env f)
  | .cmpScalar k op thresh within, _ => .cmp k op thresh within
  | .cmpMap entries keyExpr op thresh, hv =>
      let kv := evalExpr m.ops c c' env keyExpr
      foldTestDisj (entries.attach.map (fun ⟨e, he⟩ => m.evalEntryTest kv op thresh e (hv e he)))
  | .neg t, hv => .neg (evalSymTest c c' env t hv)
  | .conj t1 t2, hv => .conj (evalSymTest c c' env t1 hv.1) (evalSymTest c c' env t2 hv.2)
  | .disj t1 t2, hv => .disj (evalSymTest c c' env t1 hv.1) (evalSymTest c c' env t2 hv.2)
  | .allGroup g body, hv =>
      foldTestConj ((List.finRange (sizes g)).map (fun j => evalSymTest c c' (push env (Val.key ⟨g, j⟩)) body hv))
  | .someGroup g body, hv =>
      foldTestDisj ((List.finRange (sizes g)).map (fun j => evalSymTest c c' (push env (Val.key ⟨g, j⟩)) body hv))
  | .allFixed atomIds body, hv =>
      foldTestConj (atomIds.map (fun aid => evalSymTest c c' (push env (Val.atom (m.ops.atomVal aid))) body hv))
  | .someFixed atomIds body, hv =>
      foldTestDisj (atomIds.map (fun aid => evalSymTest c c' (push env (Val.atom (m.ops.atomVal aid))) body hv))

theorem evalSymTest_equivariant (p : GroupPerm sizes) (c c' : m.Core) (n : Fin slotCount → Nat) :
    ∀ (t : SymTest d m.cap CoreVar) (hv : t.valid m.slotInfo m.cap) (env : Env sizes A),
      (m.evalSymTest (renameState p c) (renameState p c') (renameEnv p env) t hv).eval (m.renameCounters p n) ↔
        (m.evalSymTest c c' env t hv).eval n
  | .pure f, _, env => evalForm_equivariant p m.ops c c' env f
  | .cmpScalar k op thresh within, hv, _ => by
      simp only [evalSymTest, Test.eval, renameCounters, m.permSlot_none p.inverse k hv]
  | .cmpMap entries keyExpr op thresh, hv, env => by
      simp only [evalSymTest, foldTestDisj_eval, List.mem_map, List.mem_attach, true_and, Subtype.exists]
      rw [evalExpr_equivariant]
      constructor
      · rintro ⟨_, ⟨e, he, rfl⟩, h⟩
        exact ⟨_, ⟨e, he, rfl⟩, (m.evalEntryTest_equivariant p _ op thresh e (hv e he) n).mp h⟩
      · rintro ⟨_, ⟨e, he, rfl⟩, h⟩
        exact ⟨_, ⟨e, he, rfl⟩, (m.evalEntryTest_equivariant p _ op thresh e (hv e he) n).mpr h⟩
  | .neg t, hv, env => not_congr (evalSymTest_equivariant p c c' n t hv env)
  | .conj t1 t2, hv, env =>
      and_congr (evalSymTest_equivariant p c c' n t1 hv.1 env) (evalSymTest_equivariant p c c' n t2 hv.2 env)
  | .disj t1 t2, hv, env =>
      or_congr (evalSymTest_equivariant p c c' n t1 hv.1 env) (evalSymTest_equivariant p c c' n t2 hv.2 env)
  | .allGroup g body, hv, env => by
      simp only [evalSymTest, foldTestConj_eval, List.mem_map, List.mem_finRange, true_and]
      constructor
      · intro h
        rintro _ ⟨j, rfl⟩
        have h' := h _ ⟨(p g).toFun j, rfl⟩
        have hpush : push (renameEnv p env) (Val.key ⟨g, (p g).toFun j⟩) = renameEnv p (push env (Val.key ⟨g, j⟩)) := by
          rw [renameEnv_push, Val.rename_key]; rfl
        rw [hpush] at h'
        exact (evalSymTest_equivariant p c c' n body hv (push env (Val.key ⟨g, j⟩))).mp h'
      · intro h
        rintro _ ⟨j, rfl⟩
        have h' := h _ ⟨(p g).invFun j, rfl⟩
        have hpush : push (renameEnv p env) (Val.key ⟨g, j⟩) = renameEnv p (push env (Val.key ⟨g, (p g).invFun j⟩)) := by
          rw [renameEnv_push]; simp only [Val.rename_key, GroupPerm.toFun, (p g).right]
        rw [hpush]
        exact (evalSymTest_equivariant p c c' n body hv (push env (Val.key ⟨g, (p g).invFun j⟩))).mpr h'
  | .someGroup g body, hv, env => by
      simp only [evalSymTest, foldTestDisj_eval, List.mem_map, List.mem_finRange, true_and]
      constructor
      · rintro ⟨_, ⟨j, rfl⟩, h⟩
        refine ⟨_, ⟨(p g).invFun j, rfl⟩, ?_⟩
        have hpush : push (renameEnv p env) (Val.key ⟨g, j⟩) = renameEnv p (push env (Val.key ⟨g, (p g).invFun j⟩)) := by
          rw [renameEnv_push]; simp only [Val.rename_key, GroupPerm.toFun, (p g).right]
        rw [hpush] at h
        exact (evalSymTest_equivariant p c c' n body hv (push env (Val.key ⟨g, (p g).invFun j⟩))).mp h
      · rintro ⟨_, ⟨j, rfl⟩, h⟩
        refine ⟨_, ⟨(p g).toFun j, rfl⟩, ?_⟩
        have hpush : push (renameEnv p env) (Val.key ⟨g, (p g).toFun j⟩) = renameEnv p (push env (Val.key ⟨g, j⟩)) := by
          rw [renameEnv_push, Val.rename_key]; rfl
        rw [hpush]
        exact (evalSymTest_equivariant p c c' n body hv (push env (Val.key ⟨g, j⟩))).mpr h
  | .allFixed atomIds body, hv, env => by
      simp only [evalSymTest, foldTestConj_eval, List.mem_map]
      constructor
      · intro h
        rintro _ ⟨aid, haid, rfl⟩
        have h' := h _ ⟨aid, haid, rfl⟩
        have hpush : push (renameEnv p env) (Val.atom (m.ops.atomVal aid)) =
            renameEnv p (push env (Val.atom (m.ops.atomVal aid))) := by
          rw [renameEnv_push, Val.rename_atom]
        rw [hpush] at h'
        exact (evalSymTest_equivariant p c c' n body hv _).mp h'
      · intro h
        rintro _ ⟨aid, haid, rfl⟩
        have h' := h _ ⟨aid, haid, rfl⟩
        have hpush : push (renameEnv p env) (Val.atom (m.ops.atomVal aid)) =
            renameEnv p (push env (Val.atom (m.ops.atomVal aid))) := by
          rw [renameEnv_push, Val.rename_atom]
        rw [hpush]
        exact (evalSymTest_equivariant p c c' n body hv _).mpr h'
  | .someFixed atomIds body, hv, env => by
      simp only [evalSymTest, foldTestDisj_eval, List.mem_map]
      constructor
      · rintro ⟨_, ⟨aid, haid, rfl⟩, h⟩
        refine ⟨_, ⟨aid, haid, rfl⟩, ?_⟩
        have hpush : push (renameEnv p env) (Val.atom (m.ops.atomVal aid)) =
            renameEnv p (push env (Val.atom (m.ops.atomVal aid))) := by
          rw [renameEnv_push, Val.rename_atom]
        rw [hpush] at h
        exact (evalSymTest_equivariant p c c' n body hv _).mp h
      · rintro ⟨_, ⟨aid, haid, rfl⟩, h⟩
        refine ⟨_, ⟨aid, haid, rfl⟩, ?_⟩
        have hpush : push (renameEnv p env) (Val.atom (m.ops.atomVal aid)) =
            renameEnv p (push env (Val.atom (m.ops.atomVal aid))) := by
          rw [renameEnv_push, Val.rename_atom]
        rw [hpush]
        exact (evalSymTest_equivariant p c c' n body hv _).mpr h

def evalSymSeed (c : m.Core) (env : Env sizes A) : SymSeed d CoreVar → Nat
  | .const n => n
  | .ite cond yes no =>
      @_root_.ite Nat (evalForm m.ops c c env cond) (Classical.propDecidable _)
        (evalSymSeed c env yes) (evalSymSeed c env no)

def evalSymTransfer (c c' : m.Core) (env : Env sizes A) (slotKey : Val sizes A) :
    (tr : SymTransfer d m.cap CoreVar) → tr.valid m.slotInfo m.cap → Transfer m.cap
  | .keep, _ => .keep
  | .reset r, _ => .reset r
  | .add delta, _ => .add delta
  | .ite cond yes no, hv =>
      .ite (m.evalSymTest c c' env cond hv.1)
        (evalSymTransfer c c' env slotKey yes hv.2.1)
        (evalSymTransfer c c' env slotKey no hv.2.2)
  | .ifKeyEq keyExpr yes no, hv =>
      .ite (.pure (evalExpr m.ops c c' env keyExpr = slotKey))
        (evalSymTransfer c c' env slotKey yes hv.1)
        (evalSymTransfer c c' env slotKey no hv.2)

theorem evalSymTransfer_reduced_equivariant (p : GroupPerm sizes) (c c' : m.Core) (env : Env sizes A)
    (a : Fin slotCount → Nat) (i : Fin slotCount) :
    ∀ (tr : SymTransfer d m.cap CoreVar) (hv : tr.valid m.slotInfo m.cap),
      (m.evalSymTransfer (renameState p c) (renameState p c') (renameEnv p env) (m.slotKeyVal i) tr hv).evalReduced
          (m.renameCounters p a) i =
        (m.evalSymTransfer c c' env (m.slotKeyVal (m.permSlot p.inverse i)) tr hv).evalReduced
          a (m.permSlot p.inverse i)
  | .keep, _ => rfl
  | .reset r, _ => by
      simp only [evalSymTransfer, Transfer.evalReduced, m.cap_permSlot p.inverse i]
  | .add delta, _ => by
      simp only [evalSymTransfer, Transfer.evalReduced, renameCounters, m.cap_permSlot p.inverse i]
  | .ite cond yes no, hv => by
      simp only [evalSymTransfer, Transfer.evalReduced]
      by_cases hc : (m.evalSymTest c c' env cond hv.1).eval a
      · have hc' : (m.evalSymTest (renameState p c) (renameState p c') (renameEnv p env) cond hv.1).eval (m.renameCounters p a) :=
          (m.evalSymTest_equivariant p c c' a cond hv.1 env).mpr hc
        simp only [hc, hc', ↓reduceIte]
        exact evalSymTransfer_reduced_equivariant p c c' env a i yes hv.2.1
      · have hc' : ¬ (m.evalSymTest (renameState p c) (renameState p c') (renameEnv p env) cond hv.1).eval (m.renameCounters p a) :=
          fun h => hc ((m.evalSymTest_equivariant p c c' a cond hv.1 env).mp h)
        simp only [hc, hc', ↓reduceIte]
        exact evalSymTransfer_reduced_equivariant p c c' env a i no hv.2.2
  | .ifKeyEq keyExpr yes no, hv => by
      simp only [evalSymTransfer, Transfer.evalReduced, Test.eval]
      have hkey : (evalExpr m.ops (renameState p c) (renameState p c') (renameEnv p env) keyExpr = m.slotKeyVal i) ↔
          (evalExpr m.ops c c' env keyExpr = m.slotKeyVal (m.permSlot p.inverse i)) := by
        rw [evalExpr_equivariant, m.slotKeyVal_permSlot p.inverse i]
        constructor
        · intro h
          have := congrArg (renameVal p.inverse) h
          simpa only [renameVal_inverse] using this
        · intro h
          have := congrArg (renameVal p) h
          simpa only [renameVal_right] using this
      by_cases hk : evalExpr m.ops c c' env keyExpr = m.slotKeyVal (m.permSlot p.inverse i)
      · have hk' : evalExpr m.ops (renameState p c) (renameState p c') (renameEnv p env) keyExpr = m.slotKeyVal i :=
          hkey.mpr hk
        simp only [hk, hk', ↓reduceIte]
        exact evalSymTransfer_reduced_equivariant p c c' env a i yes hv.1
      · have hk' : evalExpr m.ops (renameState p c) (renameState p c') (renameEnv p env) keyExpr ≠ m.slotKeyVal i :=
          fun h => hk (hkey.mp h)
        simp only [hk, hk', ↓reduceIte]
        exact evalSymTransfer_reduced_equivariant p c c' env a i no hv.2

def thresholdModel : ThresholdCounterRule.Model m.Core m.Witness slotCount where
  cap := m.cap
  initial c w :=
    m.initValid w.1 = true ∧
      evalBounds m.ops c c emptyEnv (m.initBounds w.1) w.2 ∧
      evalForm m.ops c c (pushList emptyEnv w.2) (m.initGuard w.1)
  seed c w i := m.evalSymSeed c (pushList emptyEnv w.2) (m.initSeed w.1 (m.slotTemplate i))
  guard c d w :=
    if m.stepValid w.1 then
      .conj (.pure (evalBounds m.ops c d emptyEnv (m.stepBounds w.1) w.2))
        (m.evalSymTest c d (pushList emptyEnv w.2) (m.stepGuard w.1) (m.stepGuardValid_prop w.1))
    else .pure False
  transfer c d w i :=
    m.evalSymTransfer c d (pushList emptyEnv w.2) (m.slotKeyVal i)
      (m.stepTransfer w.1 (m.slotTemplate i)) (m.stepTransferValid_prop w.1 (m.slotTemplate i))
  observe c := m.evalSymTest c c emptyEnv m.obsTest m.obsValid_prop
  initObserve c := m.evalSymTest c c emptyEnv m.initObsTest m.initObsValid_prop
  constraint c := m.evalSymTest c c emptyEnv m.constraintTest m.constraintValid_prop
  actionConstraint c d := evalForm m.ops c d emptyEnv m.actionConstraintForm
  actionObserve c d := evalForm m.ops c d emptyEnv m.actionObsForm

-- Step 1: exact ThresholdCounterRule systems and certificates (definitionally connected).
def concrete : System m.TState := m.thresholdModel.concrete
def intermediate : System m.TState := m.thresholdModel.reduced
def thresholdProject (s : m.TState) : m.TState := m.thresholdModel.project s

theorem threshold_certificate : Certificate m.concrete m.intermediate m.thresholdProject :=
  m.thresholdModel.certificate

def constrainedConcrete : ConstrainedSystem m.TState := m.thresholdModel.constrainedConcrete
def constrainedIntermediate : ConstrainedSystem m.TState := m.thresholdModel.constrainedReduced

theorem threshold_constrained_certificate :
    ConstrainedCertificate m.constrainedConcrete m.constrainedIntermediate m.thresholdProject :=
  m.thresholdModel.constrained_certificate

-- Equivariance of thresholdProject and m.intermediate.
theorem thresholdProject_rename (p : GroupPerm sizes) (s : m.TState) :
    m.thresholdProject (m.renameTState p s) = m.renameTState p (m.thresholdProject s) := by
  apply Prod.ext
  · rfl
  · exact m.saturate_rename p s.2

theorem template_transfer_eq (c c' : m.Core) (env : Env sizes A) (sk : Val sizes A)
    (b : Fin branchCount) {t1 t2 : Fin templateCount} (ht : t1 = t2) :
    m.evalSymTransfer c c' env sk (m.stepTransfer b t1) (m.stepTransferValid_prop b t1) =
      m.evalSymTransfer c c' env sk (m.stepTransfer b t2) (m.stepTransferValid_prop b t2) := by
  subst ht
  rfl

theorem intermediate_next_rename (p : GroupPerm sizes) (a b : m.TState)
    (h : m.intermediate.next a b) :
    m.intermediate.next (m.renameTState p a) (m.renameTState p b) := by
  obtain ⟨w, hg, hstep⟩ := h
  refine ⟨m.renameW p w, ?_, ?_⟩
  · dsimp only [thresholdModel, renameTState, renameW] at hg ⊢
    cases hval : m.stepValid w.1 with
    | false =>
      rw [hval] at hg
      exact False.elim hg
    | true =>
      rw [hval] at hg
      simp only [↓reduceIte, Test.eval] at hg ⊢
      constructor
      · have hb := evalBounds_equivariant p m.ops a.1 b.1 emptyEnv (m.stepBounds w.1) w.2
        rw [renameEnv_empty] at hb
        exact hb.mpr hg.1
      · have ht := m.evalSymTest_equivariant p a.1 b.1 a.2 (m.stepGuard w.1) (m.stepGuardValid_prop w.1) (pushList emptyEnv w.2)
        rw [renameEnv_pushList, renameEnv_empty] at ht
        exact ht.mpr hg.2
  · apply Prod.ext
    · rfl
    · funext i
      change (m.renameCounters p b.2) i =
        (m.evalSymTransfer (renameState p a.1) (renameState p b.1) (pushList emptyEnv (w.2.map (renameVal p)))
          (m.slotKeyVal i) (m.stepTransfer w.1 (m.slotTemplate i)) (m.stepTransferValid_prop w.1 (m.slotTemplate i))).evalReduced
          (m.renameCounters p a.2) i
      have hb : b.2 (m.permSlot p.inverse i) =
          (m.evalSymTransfer a.1 b.1 (pushList emptyEnv w.2) (m.slotKeyVal (m.permSlot p.inverse i))
            (m.stepTransfer w.1 (m.slotTemplate (m.permSlot p.inverse i)))
            (m.stepTransferValid_prop w.1 (m.slotTemplate (m.permSlot p.inverse i)))).evalReduced
            a.2 (m.permSlot p.inverse i) :=
        congrFun (congrArg Prod.snd hstep) (m.permSlot p.inverse i)
      rw [renameCounters, hb]
      have htr := m.evalSymTransfer_reduced_equivariant p a.1 b.1 (pushList emptyEnv w.2) a.2 i
        (m.stepTransfer w.1 (m.slotTemplate i)) (m.stepTransferValid_prop w.1 (m.slotTemplate i))
      rw [renameEnv_pushList, renameEnv_empty] at htr
      rw [htr]
      rw [m.template_transfer_eq a.1 b.1 (pushList emptyEnv w.2) (m.slotKeyVal (m.permSlot p.inverse i)) w.1
        (m.template_permSlot p.inverse i)]

theorem intermediate_safe_rename (p : GroupPerm sizes) (a : m.TState) :
    m.intermediate.safe (m.renameTState p a) ↔ m.intermediate.safe a := by
  have h := m.evalSymTest_equivariant p a.1 a.1 a.2 m.obsTest m.obsValid_prop emptyEnv
  rwa [renameEnv_empty] at h

theorem intermediate_initSafe_rename (p : GroupPerm sizes) (a : m.TState) :
    m.constrainedIntermediate.initSafe (m.renameTState p a) ↔ m.constrainedIntermediate.initSafe a := by
  have h := m.evalSymTest_equivariant p a.1 a.1 a.2 m.initObsTest m.initObsValid_prop emptyEnv
  rwa [renameEnv_empty] at h

theorem intermediate_constraint_rename (p : GroupPerm sizes) (a : m.TState) :
    m.constrainedIntermediate.constraint (m.renameTState p a) ↔ m.constrainedIntermediate.constraint a := by
  have h := m.evalSymTest_equivariant p a.1 a.1 a.2 m.constraintTest m.constraintValid_prop emptyEnv
  rwa [renameEnv_empty] at h

theorem intermediate_actionConstraint_rename (p : GroupPerm sizes) (a b : m.TState) :
    m.constrainedIntermediate.actionConstraint (m.renameTState p a) (m.renameTState p b) ↔
      m.constrainedIntermediate.actionConstraint a b := by
  have h := evalForm_equivariant p m.ops a.1 b.1 emptyEnv m.actionConstraintForm
  rwa [renameEnv_empty] at h

theorem intermediate_actionSafe_rename (p : GroupPerm sizes) (a b : m.TState) :
    m.constrainedIntermediate.actionSafe (m.renameTState p a) (m.renameTState p b) ↔
      m.constrainedIntermediate.actionSafe a b := by
  have h := evalForm_equivariant p m.ops a.1 b.1 emptyEnv m.actionObsForm
  rwa [renameEnv_empty] at h

-- Step 2: Symmetry quotient on the exact ThresholdCounterRule projected system `m.intermediate`.
def orbitQuotient : OrbitQuotient sizes m.TState where
  system := m.constrainedIntermediate
  rename := m.renameTState
  rename_identity := m.renameTState_identity
  rename_then := m.renameTState_then
  rename_inverse := m.renameTState_inverse
  next_rename := m.intermediate_next_rename
  safe_rename := m.intermediate_safe_rename
  initSafe_rename := m.intermediate_initSafe_rename
  constraint_rename := m.intermediate_constraint_rename
  actionConstraint_rename := m.intermediate_actionConstraint_rename
  actionSafe_rename := m.intermediate_actionSafe_rename

def ThresholdOrbit (a b : m.TState) : Prop :=
  m.orbitQuotient.Orbit a b

def thresholdOrbits : Setoid m.TState :=
  m.orbitQuotient.setoid

def symProject (a : m.TState) : Quotient m.thresholdOrbits :=
  m.orbitQuotient.symProject a

def reduced : System (Quotient m.thresholdOrbits) :=
  m.orbitQuotient.reduced

theorem symmetry_certificate : Certificate m.intermediate m.reduced m.symProject :=
  m.orbitQuotient.symmetry_certificate

def project (s : m.TState) : Quotient m.thresholdOrbits :=
  m.symProject (m.thresholdProject s)

theorem certificate : Certificate m.concrete m.reduced m.project :=
  compose (p := m.thresholdProject) (q := m.symProject) m.threshold_certificate m.symmetry_certificate

theorem orbit_key_equivalent (s t : m.TState) :
    m.project s = m.project t ↔ m.ThresholdOrbit (m.thresholdProject s) (m.thresholdProject t) := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound (show m.thresholdOrbits.r (m.thresholdProject s) (m.thresholdProject t) from h)

theorem optimization_correct :
    (∀ s, Reachable m.concrete s → m.concrete.safe s) ↔
    (∀ q, Reachable m.reduced q → m.reduced.safe q) := safety_iff m.certificate

theorem specification_correct :
    (∀ s, Reachable (withStuttering m.concrete) s → m.concrete.safe s) ↔
    (∀ q, Reachable (withStuttering m.reduced) q → m.reduced.safe q) := by
  simpa only [stuttering_reachable_iff] using m.optimization_correct

theorem counterexample_lifts {q} (hq : Reachable m.reduced q) (bad : ¬ m.reduced.safe q) :
    ∃ s, Reachable m.concrete s ∧ m.project s = q ∧ ¬ m.concrete.safe s := by
  obtain ⟨s, hs, he⟩ := reachable_backward m.certificate hq
  refine ⟨s, hs, he, ?_⟩
  intro good
  apply bad
  rw [← he]
  exact (m.certificate.observe s).mp good

theorem deadlock_preserved (s : m.TState) :
    (¬ ∃ t, m.concrete.next s t) ↔ (¬ ∃ q, m.reduced.next (m.project s) q) := by
  constructor
  · intro noStep ⟨q, hq⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s q).mp hq
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨m.project t, (m.certificate.next s (m.project t)).mpr ⟨t, ht, rfl⟩⟩

def constrainedReduced : ConstrainedSystem (Quotient m.thresholdOrbits) :=
  m.orbitQuotient.constrainedReduced

theorem symmetry_constrained_certificate :
    ConstrainedCertificate m.constrainedIntermediate m.constrainedReduced m.symProject :=
  m.orbitQuotient.symmetry_constrained_certificate

theorem constrained_certificate :
    ConstrainedCertificate m.constrainedConcrete m.constrainedReduced m.project :=
  composeConstrained (p := m.thresholdProject) (q := m.symProject)
    m.threshold_constrained_certificate m.symmetry_constrained_certificate

end Model
end
end TlxOptimization.ThresholdSymRule
