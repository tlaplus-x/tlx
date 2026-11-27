/- Certified composition of phase-dependent field masking (`FieldCertificate.lean`)
with generic recursive equivariant symmetry (`EquivSymCertificate.lean`) over one
shared concrete source model via `TlxOptimization.compose` and
`TlxOptimization.composeConstrained`.

Every transition guard, field write, initial seed, sentinel, observation,
constraint, and action check is explicit `EquivRule` IR over the shared
`FieldRule.State` (with `V = EquivRule.Val`), so equivariance of the projected
system and commutation of `FieldRule.mask` with `GroupPerm` are proved in Lean
with zero unproved bridge premises. -/
set_option autoImplicit false
namespace TlxOptimization.FieldSymRule
open TlxOptimization FieldRule EquivRule
noncomputable section

abbrev KeyElem {d : Nat} (sizes : Fin d → Nat) (fixedCount : Nat) (mask : GroupMask d) :=
  Sum (Fin fixedCount) { k : EquivRule.Key sizes // mask k.1 = true }

def renameKeyElem {d : Nat} {sizes : Fin d → Nat} {fixedCount : Nat} {mask : GroupMask d}
    (p : GroupPerm sizes) : KeyElem sizes fixedCount mask → KeyElem sizes fixedCount mask
  | .inl i => .inl i
  | .inr ⟨k, hk⟩ => .inr ⟨p.toFun k, hk⟩

theorem renameKeyElem_identity {d : Nat} {sizes : Fin d → Nat} {fixedCount : Nat} {mask : GroupMask d}
    (k : KeyElem sizes fixedCount mask) :
    renameKeyElem GroupPerm.identity k = k := by
  cases k with
  | inl _ => rfl
  | inr kv =>
    cases kv with
    | mk k hk =>
      cases k with
      | mk g i => rfl

theorem renameKeyElem_then {d : Nat} {sizes : Fin d → Nat} {fixedCount : Nat} {mask : GroupMask d}
    (p q : GroupPerm sizes) (k : KeyElem sizes fixedCount mask) :
    renameKeyElem (p.then q) k = renameKeyElem q (renameKeyElem p k) := by
  cases k with
  | inl _ => rfl
  | inr kv =>
    cases kv with
    | mk k hk =>
      cases k with
      | mk g i => rfl

theorem renameKeyElem_left {d : Nat} {sizes : Fin d → Nat} {fixedCount : Nat} {mask : GroupMask d}
    (p : GroupPerm sizes) (k : KeyElem sizes fixedCount mask) :
    renameKeyElem p.inverse (renameKeyElem p k) = k := by
  cases k with
  | inl _ => rfl
  | inr kv =>
    cases kv with
    | mk k hk =>
      cases k with
      | mk g i =>
        simp only [renameKeyElem, GroupPerm.toFun, GroupPerm.inverse, Permutation.inverse, (p g).left]

theorem renameKeyElem_right {d : Nat} {sizes : Fin d → Nat} {fixedCount : Nat} {mask : GroupMask d}
    (p : GroupPerm sizes) (k : KeyElem sizes fixedCount mask) :
    renameKeyElem p (renameKeyElem p.inverse k) = k := by
  cases k with
  | inl _ => rfl
  | inr kv =>
    cases kv with
    | mk k hk =>
      cases k with
      | mk g i =>
        simp only [renameKeyElem, GroupPerm.toFun, GroupPerm.inverse, Permutation.inverse, (p g).right]

theorem renameKeyElem_injective {d : Nat} {sizes : Fin d → Nat} {fixedCount : Nat} {mask : GroupMask d}
    (p : GroupPerm sizes) {x y : KeyElem sizes fixedCount mask} :
    renameKeyElem p x = renameKeyElem p y ↔ x = y := by
  constructor
  · intro h
    have := congrArg (renameKeyElem p.inverse) h
    simpa only [renameKeyElem_left] using this
  · intro h; exact congrArg (renameKeyElem p) h

def keyElemToVal {d : Nat} {sizes : Fin d → Nat} {fixedCount : Nat} {mask : GroupMask d}
    {A : Type} [HasNatAtom A] (fixedAtom : Fin fixedCount → A) :
    KeyElem sizes fixedCount mask → Val sizes A
  | .inl i => Val.atom (fixedAtom i)
  | .inr ⟨k, _⟩ => Val.key k

theorem keyElemToVal_rename {d : Nat} {sizes : Fin d → Nat} {fixedCount : Nat} {mask : GroupMask d}
    {A : Type} [HasNatAtom A] (fixedAtom : Fin fixedCount → A)
    (p : GroupPerm sizes) (k : KeyElem sizes fixedCount mask) :
    keyElemToVal fixedAtom (renameKeyElem p k) = renameVal p (keyElemToVal fixedAtom k) := by
  cases k with
  | inl _ => rfl
  | inr kv =>
    cases kv with
    | mk k _ => rfl

def allKeyElems {d : Nat} (sizes : Fin d → Nat) (fixedCount : Nat) (mask : GroupMask d) :
    List (KeyElem sizes fixedCount mask) :=
  (List.finRange fixedCount).map Sum.inl ++
  (List.finRange d).flatMap (fun g =>
    if h : mask g = true then
      (List.finRange (sizes g)).map (fun i => Sum.inr ⟨⟨g, i⟩, h⟩)
    else [])

theorem mem_allKeyElems {d : Nat} {sizes : Fin d → Nat} {fixedCount : Nat} {mask : GroupMask d}
    (k : KeyElem sizes fixedCount mask) :
    k ∈ allKeyElems sizes fixedCount mask := by
  unfold allKeyElems
  rw [List.mem_append]
  cases k with
  | inl i =>
    left
    exact List.mem_map_of_mem (List.mem_finRange i)
  | inr kv =>
    rcases kv with ⟨⟨g, i⟩, hk⟩
    right
    rw [List.mem_flatMap]
    refine ⟨g, List.mem_finRange g, ?_⟩
    simp only [hk, ↓reduceDIte]
    exact List.mem_map_of_mem (List.mem_finRange i)

theorem Val.fn_map_keyElem_rename {d : Nat} {sizes : Fin d → Nat} {fixedCount : Nat} {mask : GroupMask d}
    {A : Type} [HasNatAtom A] (fixedAtom : Fin fixedCount → A)
    (p : GroupPerm sizes) (g : KeyElem sizes fixedCount mask → Val sizes A) :
    renameVal p (Val.fn ((allKeyElems sizes fixedCount mask).map (fun k => (keyElemToVal fixedAtom k, g k)))) =
      Val.fn ((allKeyElems sizes fixedCount mask).map (fun k => (keyElemToVal fixedAtom k, renameVal p (g (renameKeyElem p.inverse k))))) := by
  rw [Val.rename_fn, List.map_map, Val.fn_eq_iff]
  intro kv
  simp only [List.mem_map, Function.comp_def]
  constructor
  · rintro ⟨k, _, rfl⟩
    refine ⟨renameKeyElem p k, mem_allKeyElems _, ?_⟩
    simp only [keyElemToVal_rename, renameKeyElem_left]
  · rintro ⟨k, _, rfl⟩
    refine ⟨renameKeyElem p.inverse k, mem_allKeyElems _, ?_⟩
    simp only [← keyElemToVal_rename, renameKeyElem_right]

inductive VarRole (CoreVar F : Type) where
  | core (cv : CoreVar)
  | recordMap (isKeyed : Bool) (ctrlFieldAtom : Nat) (fieldAtom : F → Nat)
  | controlVar (isKeyed : Bool)
  | companionVar (isKeyed : Bool) (field : F)

def emptyCoreState {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A] :
    EquivRule.State Empty sizes A :=
  fun e => nomatch e

theorem emptyCoreState_rename {d : Nat} {sizes : Fin d → Nat} {A : Type} [HasNatAtom A]
    (p : GroupPerm sizes) :
    renameState p (emptyCoreState (sizes := sizes) (A := A)) = emptyCoreState := by
  funext e
  exact nomatch e

structure Model (d : Nat) (sizes : Fin d → Nat) (fixedCount : Nat) (mask : GroupMask d)
    (CoreVar FullVar : Type) (phaseCount fieldCount branchCount : Nat) (A : Type) [HasNatAtom A] where
  ops : AtomOps A
  fixedAtom : Fin fixedCount → A
  defaultKey : KeyElem sizes fixedCount mask
  phaseAtom : Fin phaseCount → Nat
  varRole : FullVar → VarRole CoreVar (Fin fieldCount)
  sentinelExpr : Fin fieldCount → EquivRule.Expr d Empty
  live : Fin phaseCount → Fin fieldCount → Bool
  source : Fin branchCount → Fin phaseCount
  target : Fin branchCount → Fin phaseCount
  readsActor : Fin branchCount → Fin fieldCount → Bool
  readsGlobal : Fin branchCount → Fin fieldCount → Bool
  writes : Fin branchCount → Fin fieldCount → Bool
  observed : Fin phaseCount → Fin fieldCount → Bool
  actorLive : ∀ b f, readsActor b f = true → live (source b) f = true
  globalLive : ∀ b p f, readsGlobal b f = true → live p f = true
  frameLive : ∀ b f, live (target b) f = true → writes b f = false → live (source b) f = true
  observedLive : ∀ p f, observed p f = true → live p f = true
  seedValid : Fin branchCount → Bool
  seedBounds : Fin branchCount → List (SetPred d FullVar)
  seedGuard : Fin branchCount → Form d FullVar
  seedPhase : Fin branchCount → Fin phaseCount
  seedValueExpr : Fin branchCount → Fin fieldCount → EquivRule.Expr d FullVar
  stepValid : Fin branchCount → Bool
  stepHasActor : Fin branchCount → Bool
  stepBounds : Fin branchCount → List (SetPred d FullVar)
  stepGuard : Fin branchCount → Form d FullVar
  stepValueExpr : Fin branchCount → Fin fieldCount → EquivRule.Expr d FullVar
  obsForm : Form d FullVar
  initObsForm : Form d FullVar := .truth true
  constraintForm : Form d FullVar := .truth true
  actionConstraintForm : Form d FullVar := .truth true
  actionObsForm : Form d FullVar := .truth true
  -- When scalar (non-keyed), `defaultKey` must be a fixed key so it is invariant under `GroupPerm`.
  defaultKeyFixed : ∀ p : GroupPerm sizes,
    (∀ v, match varRole v with
      | .recordMap false _ _ | .controlVar false | .companionVar false _ =>
          renameKeyElem p defaultKey = defaultKey
      | _ => True)

namespace Model
variable {d : Nat} {sizes : Fin d → Nat} {fixedCount : Nat} {mask : GroupMask d}
  {CoreVar FullVar : Type} {phaseCount fieldCount branchCount : Nat} {A : Type} [HasNatAtom A]
  (m : Model d sizes fixedCount mask CoreVar FullVar phaseCount fieldCount branchCount A)

abbrev K (_m : Model d sizes fixedCount mask CoreVar FullVar phaseCount fieldCount branchCount A) :=
  KeyElem sizes fixedCount mask
abbrev Core (_m : Model d sizes fixedCount mask CoreVar FullVar phaseCount fieldCount branchCount A) :=
  EquivRule.State CoreVar sizes A
abbrev FState (_m : Model d sizes fixedCount mask CoreVar FullVar phaseCount fieldCount branchCount A) :=
  FieldRule.State (EquivRule.State CoreVar sizes A) (KeyElem sizes fixedCount mask)
    (Fin phaseCount) (Fin fieldCount) (Val sizes A)
abbrev Witness (_m : Model d sizes fixedCount mask CoreVar FullVar phaseCount fieldCount branchCount A) :=
  KeyElem sizes fixedCount mask × List (Val sizes A)

def missing (f : Fin fieldCount) : Val sizes A :=
  evalExpr m.ops emptyCoreState emptyCoreState emptyEnv (m.sentinelExpr f)

theorem missing_rename (p : GroupPerm sizes) (f : Fin fieldCount) :
    renameVal p (m.missing f) = m.missing f := by
  unfold missing
  have h := evalExpr_equivariant p m.ops emptyCoreState emptyCoreState emptyEnv (m.sentinelExpr f)
  rw [emptyCoreState_rename, renameEnv_empty] at h
  exact h.symm

def phaseVal (ph : Fin phaseCount) : Val sizes A :=
  Val.atom (m.ops.atomVal (m.phaseAtom ph))

def recordVal (ctrlFieldAtom : Nat) (fieldAtom : Fin fieldCount → Nat)
    (ph : Fin phaseCount) (vals : Fin fieldCount → Val sizes A) : Val sizes A :=
  Val.fn ((Val.atom (m.ops.atomVal ctrlFieldAtom), m.phaseVal ph) ::
    (List.finRange fieldCount).map (fun f => (Val.atom (m.ops.atomVal (fieldAtom f)), vals f)))

theorem recordVal_rename (p : GroupPerm sizes) (ctrlFieldAtom : Nat) (fieldAtom : Fin fieldCount → Nat)
    (ph : Fin phaseCount) (vals : Fin fieldCount → Val sizes A) :
    renameVal p (m.recordVal ctrlFieldAtom fieldAtom ph vals) =
      m.recordVal ctrlFieldAtom fieldAtom ph (fun f => renameVal p (vals f)) := by
  unfold recordVal phaseVal
  rw [Val.rename_fn, List.map_cons, List.map_map]
  rfl

def toEquivState (c : m.Core) (ph : m.K → Fin phaseCount) (vals : m.K → Fin fieldCount → Val sizes A) :
    EquivRule.State FullVar sizes A :=
  fun v => match m.varRole v with
    | .core cv => c cv
    | .recordMap false ctrlF fAtom =>
        m.recordVal ctrlF fAtom (ph m.defaultKey) (vals m.defaultKey)
    | .recordMap true ctrlF fAtom =>
        Val.fn ((allKeyElems sizes fixedCount mask).map (fun k =>
          (keyElemToVal m.fixedAtom k, m.recordVal ctrlF fAtom (ph k) (vals k))))
    | .controlVar false => m.phaseVal (ph m.defaultKey)
    | .controlVar true =>
        Val.fn ((allKeyElems sizes fixedCount mask).map (fun k =>
          (keyElemToVal m.fixedAtom k, m.phaseVal (ph k))))
    | .companionVar false f => vals m.defaultKey f
    | .companionVar true f =>
        Val.fn ((allKeyElems sizes fixedCount mask).map (fun k =>
          (keyElemToVal m.fixedAtom k, vals k f)))

def renamePh (p : GroupPerm sizes) (ph : m.K → Fin phaseCount) : m.K → Fin phaseCount :=
  fun k => ph (renameKeyElem p.inverse k)

def renameVals (p : GroupPerm sizes) (vals : m.K → Fin fieldCount → Val sizes A) :
    m.K → Fin fieldCount → Val sizes A :=
  fun k f => renameVal p (vals (renameKeyElem p.inverse k) f)

def renameFieldState (p : GroupPerm sizes) (s : m.FState) : m.FState :=
  (renameState p s.1, (m.renamePh p s.2.1, m.renameVals p s.2.2))

def renameW (p : GroupPerm sizes) (w : m.Witness) : m.Witness :=
  (renameKeyElem p w.1, w.2.map (renameVal p))

theorem renameFieldState_identity (s : m.FState) :
    m.renameFieldState GroupPerm.identity s = s := by
  apply Prod.ext
  · exact renameState_identity s.1
  · apply Prod.ext
    · funext k; exact congrArg s.2.1 (renameKeyElem_identity k)
    · funext k f
      change renameVal GroupPerm.identity (s.2.2 (renameKeyElem GroupPerm.identity.inverse k) f) = s.2.2 k f
      have hk : renameKeyElem GroupPerm.identity.inverse k = k := by
        cases k with
        | inl _ => rfl
        | inr kv => cases kv with | mk k _ => cases k with | mk _ _ => rfl
      rw [hk, renameVal_identity]

theorem renameFieldState_then (p q : GroupPerm sizes) (s : m.FState) :
    m.renameFieldState (p.then q) s = m.renameFieldState q (m.renameFieldState p s) := by
  apply Prod.ext
  · exact renameState_then p q s.1
  · apply Prod.ext
    · funext k
      change s.2.1 (renameKeyElem (p.then q).inverse k) =
        s.2.1 (renameKeyElem p.inverse (renameKeyElem q.inverse k))
      have hk : renameKeyElem (p.then q).inverse k = renameKeyElem p.inverse (renameKeyElem q.inverse k) := by
        cases k with
        | inl _ => rfl
        | inr kv => cases kv with | mk k _ => cases k with | mk _ _ => rfl
      rw [hk]
    · funext k f
      change renameVal (p.then q) (s.2.2 (renameKeyElem (p.then q).inverse k) f) =
        renameVal q (renameVal p (s.2.2 (renameKeyElem p.inverse (renameKeyElem q.inverse k)) f))
      have hk : renameKeyElem (p.then q).inverse k = renameKeyElem p.inverse (renameKeyElem q.inverse k) := by
        cases k with
        | inl _ => rfl
        | inr kv => cases kv with | mk k _ => cases k with | mk _ _ => rfl
      rw [hk, renameVal_then]

theorem renameFieldState_inverse (p : GroupPerm sizes) (s : m.FState) :
    m.renameFieldState p.inverse (m.renameFieldState p s) = s := by
  rw [← m.renameFieldState_then p p.inverse s, GroupPerm.then_inverse]
  exact m.renameFieldState_identity s

theorem toEquivState_rename (p : GroupPerm sizes) (c : m.Core) (ph : m.K → Fin phaseCount)
    (vals : m.K → Fin fieldCount → Val sizes A) :
    m.toEquivState (renameState p c) (m.renamePh p ph) (m.renameVals p vals) =
      renameState p (m.toEquivState c ph vals) := by
  funext v
  have hfix := m.defaultKeyFixed p.inverse v
  unfold toEquivState renameState
  cases hrole : m.varRole v with
  | core cv =>
    simp only [hrole]
  | recordMap isKeyed ctrlF fAtom =>
    rw [hrole] at hfix
    cases isKeyed with
    | false =>
      simp only [hrole, renamePh, hfix, m.recordVal_rename]
      congr 1
      funext f
      simp only [renameVals, hfix]
    | true =>
      simp only [hrole, renamePh]
      rw [Val.fn_map_keyElem_rename]
      congr 1
      apply List.map_congr_left
      intro k _
      exact congrArg (fun x => (keyElemToVal m.fixedAtom k, x)) (m.recordVal_rename p ctrlF fAtom _ _).symm
  | controlVar isKeyed =>
    rw [hrole] at hfix
    cases isKeyed with
    | false =>
      simp only [hrole, renamePh, phaseVal, hfix, Val.rename_atom]
    | true =>
      simp only [hrole, renamePh]
      exact (Val.fn_map_keyElem_rename m.fixedAtom p (fun k => m.phaseVal (ph k))).symm
  | companionVar isKeyed f =>
    rw [hrole] at hfix
    cases isKeyed with
    | false =>
      simp only [hrole, renameVals, hfix]
    | true =>
      simp only [hrole, renameVals]
      exact (Val.fn_map_keyElem_rename m.fixedAtom p (fun k => vals k f)).symm

def stepBaseEnv (b : Fin branchCount) (a : m.K) : Env sizes A :=
  if m.stepHasActor b then push emptyEnv (keyElemToVal m.fixedAtom a) else emptyEnv

theorem stepBaseEnv_rename (p : GroupPerm sizes) (b : Fin branchCount) (a : m.K) :
    m.stepBaseEnv b (renameKeyElem p a) = renameEnv p (m.stepBaseEnv b a) := by
  unfold stepBaseEnv
  cases m.stepHasActor b with
  | false => exact (renameEnv_empty p).symm
  | true =>
    simp only [↓reduceIte, keyElemToVal_rename, renameEnv_push, renameEnv_empty]

def fieldModel :
    FieldRule.Model m.Core m.K (Fin phaseCount) (Fin fieldCount) (Val sizes A) (Fin branchCount) m.Witness where
  missing := m.missing
  live := m.live
  source := m.source
  target := m.target
  readsActor := m.readsActor
  readsGlobal := m.readsGlobal
  writes := m.writes
  observed := m.observed
  actorLive := m.actorLive
  globalLive := m.globalLive
  frameLive := m.frameLive
  observedLive := m.observedLive
  actor _ w := w.1
  initial c b w :=
    let sInit := m.toEquivState c (fun _ => m.seedPhase b) (fun _ f => m.missing f)
    m.seedValid b = true ∧
      evalBounds m.ops sInit sInit emptyEnv (m.seedBounds b) w.2 ∧
      evalForm m.ops sInit sInit (pushList emptyEnv w.2) (m.seedGuard b)
  seedPhase _ b _ _ := m.seedPhase b
  seedValue c b w k f :=
    let sInit := m.toEquivState c (fun _ => m.seedPhase b) (fun _ f => m.missing f)
    evalExpr m.ops sInit sInit (push (pushList emptyEnv w.2) (keyElemToVal m.fixedAtom k)) (m.seedValueExpr b f)
  guard b c d w ph input :=
    let sIn := m.toEquivState c ph input
    let tIn := m.toEquivState d ph input
    let baseEnv := m.stepBaseEnv b w.1
    m.stepValid b = true ∧
      evalBounds m.ops sIn tIn baseEnv (m.stepBounds b) w.2 ∧
      evalForm m.ops sIn tIn (pushList baseEnv w.2) (m.stepGuard b)
  value b c d w ph input f :=
    let sIn := m.toEquivState c ph input
    let tIn := m.toEquivState d ph input
    let baseEnv := m.stepBaseEnv b w.1
    evalExpr m.ops sIn tIn (pushList baseEnv w.2) (m.stepValueExpr b f)
  observe c ph input :=
    let sObs := m.toEquivState c ph input
    evalForm m.ops sObs sObs emptyEnv m.obsForm
  initObserve c ph input :=
    let sObs := m.toEquivState c ph input
    evalForm m.ops sObs sObs emptyEnv m.initObsForm
  constraint c ph input :=
    let sObs := m.toEquivState c ph input
    evalForm m.ops sObs sObs emptyEnv m.constraintForm
  actionConstraint c d p q input input' :=
    let sObs := m.toEquivState c p input
    let tObs := m.toEquivState d q input'
    evalForm m.ops sObs tObs emptyEnv m.actionConstraintForm
  actionObserve c d p q input input' :=
    let sObs := m.toEquivState c p input
    let tObs := m.toEquivState d q input'
    evalForm m.ops sObs tObs emptyEnv m.actionObsForm

-- Step 1: exact FieldRule systems and certificates (definitionally connected).
def concrete : System m.FState := m.fieldModel.concrete
def intermediate : System m.FState := m.fieldModel.reduced
def fieldProject (s : m.FState) : m.FState := m.fieldModel.project s

theorem field_certificate : Certificate m.concrete m.intermediate m.fieldProject :=
  m.fieldModel.certificate

def constrainedConcrete : ConstrainedSystem m.FState := m.fieldModel.constrainedConcrete
def constrainedIntermediate : ConstrainedSystem m.FState := m.fieldModel.constrainedReduced

theorem field_constrained_certificate :
    ConstrainedCertificate m.constrainedConcrete m.constrainedIntermediate m.fieldProject :=
  m.fieldModel.constrained_certificate

-- Equivariance of FieldRule.mask, reads, observations, enabled, advance, and intermediate system.
theorem fieldProject_rename (p : GroupPerm sizes) (s : m.FState) :
    m.fieldProject (m.renameFieldState p s) = m.renameFieldState p (m.fieldProject s) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · funext k f
      change (if m.live (s.2.1 (renameKeyElem p.inverse k)) f then
          renameVal p (s.2.2 (renameKeyElem p.inverse k) f) else m.missing f) =
        renameVal p (if m.live (s.2.1 (renameKeyElem p.inverse k)) f then
          s.2.2 (renameKeyElem p.inverse k) f else m.missing f)
      cases m.live (s.2.1 (renameKeyElem p.inverse k)) f with
      | true => rfl
      | false => exact (m.missing_rename p f).symm

theorem reads_rename (p : GroupPerm sizes) (b : Fin branchCount) (a : m.K)
    (v : m.K → Fin fieldCount → Val sizes A) :
    m.fieldModel.reads b (renameKeyElem p a) (m.renameVals p v) =
      m.renameVals p (m.fieldModel.reads b a v) := by
  classical
  funext k f
  unfold FieldRule.Model.reads renameVals
  dsimp only [fieldModel]
  by_cases hk : renameKeyElem p.inverse k = a
  · have hk' : k = renameKeyElem p a := by rw [← hk, renameKeyElem_right]
    subst hk'
    simp only [renameKeyElem_left, decide_true, Bool.true_and]
    by_cases h : (m.readsGlobal b f || m.readsActor b f) = true
    · simp only [h, ↓reduceIte]
    · simp only [h]
      exact (m.missing_rename p f).symm
  · have hk' : k ≠ renameKeyElem p a := fun h => hk (by rw [h, renameKeyElem_left])
    simp only [hk, hk', decide_false, Bool.false_and, Bool.or_false]
    by_cases h : m.readsGlobal b f = true
    · simp only [h, ↓reduceIte]
    · simp only [h]
      exact (m.missing_rename p f).symm

theorem observations_rename (p : GroupPerm sizes) (ph : m.K → Fin phaseCount)
    (v : m.K → Fin fieldCount → Val sizes A) :
    m.fieldModel.observations (m.renamePh p ph) (m.renameVals p v) =
      m.renameVals p (m.fieldModel.observations ph v) := by
  funext k f
  unfold FieldRule.Model.observations renamePh renameVals
  dsimp only [fieldModel]
  by_cases hobs : m.observed (ph (renameKeyElem p.inverse k)) f = true
  · simp only [hobs, ↓reduceIte]
  · simp only [hobs]
    exact (m.missing_rename p f).symm

theorem enabled_rename (p : GroupPerm sizes) (s : m.FState) (c' : m.Core)
    (b : Fin branchCount) (w : m.Witness) :
    m.fieldModel.enabled (m.renameFieldState p s) (renameState p c') b (m.renameW p w) ↔
      m.fieldModel.enabled s c' b w := by
  unfold FieldRule.Model.enabled
  dsimp only [fieldModel, renameFieldState, renameW, renamePh]
  rw [renameKeyElem_left]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  have hreads : m.fieldModel.reads b (renameKeyElem p w.1) (m.renameVals p s.2.2) =
      m.renameVals p (m.fieldModel.reads b w.1 s.2.2) := m.reads_rename p b w.1 s.2.2
  change (evalBounds m.ops (m.toEquivState (renameState p s.1) (m.renamePh p s.2.1) (m.fieldModel.reads b (renameKeyElem p w.1) (m.renameVals p s.2.2)))
      (m.toEquivState (renameState p c') (m.renamePh p s.2.1) (m.fieldModel.reads b (renameKeyElem p w.1) (m.renameVals p s.2.2)))
      (m.stepBaseEnv b (renameKeyElem p w.1)) (m.stepBounds b) (w.2.map (renameVal p)) ∧
    evalForm m.ops (m.toEquivState (renameState p s.1) (m.renamePh p s.2.1) (m.fieldModel.reads b (renameKeyElem p w.1) (m.renameVals p s.2.2)))
      (m.toEquivState (renameState p c') (m.renamePh p s.2.1) (m.fieldModel.reads b (renameKeyElem p w.1) (m.renameVals p s.2.2)))
      (pushList (m.stepBaseEnv b (renameKeyElem p w.1)) (w.2.map (renameVal p))) (m.stepGuard b)) ↔ _
  rw [hreads, m.toEquivState_rename, m.toEquivState_rename, m.stepBaseEnv_rename]
  apply and_congr
  · exact evalBounds_equivariant p m.ops _ _ (m.stepBaseEnv b w.1) (m.stepBounds b) w.2
  · rw [← renameEnv_pushList]
    exact evalForm_equivariant p m.ops _ _ (pushList (m.stepBaseEnv b w.1) w.2) (m.stepGuard b)

theorem advance_rename (p : GroupPerm sizes) (s : m.FState) (c' : m.Core)
    (b : Fin branchCount) (w : m.Witness) :
    m.fieldModel.advance (m.renameFieldState p s) (renameState p c') b (m.renameW p w) =
      m.renameFieldState p (m.fieldModel.advance s c' b w) := by
  classical
  unfold FieldRule.Model.advance
  dsimp only [renameFieldState, renameW]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext k
      dsimp only
      unfold renamePh
      have hact : ∀ x, m.fieldModel.actor b x = x.1 := fun _ => rfl
      rw [hact, hact]
      by_cases hk : renameKeyElem p.inverse k = w.1
      · have hk' : k = renameKeyElem p w.1 := by rw [← hk, renameKeyElem_right]
        subst hk'
        simp only [renameKeyElem_left, ↓reduceIte]
      · have hk' : k ≠ renameKeyElem p w.1 := fun h => hk (by rw [h, renameKeyElem_left])
        simp only [hk, hk', ↓reduceIte]
    · funext k f
      dsimp only
      unfold renameVals
      dsimp only
      have hact : ∀ x, m.fieldModel.actor b x = x.1 := fun _ => rfl
      have hwr : m.fieldModel.writes b f = m.writes b f := rfl
      rw [hact, hact, hwr]
      by_cases hk : renameKeyElem p.inverse k = w.1
      · have hk' : k = renameKeyElem p w.1 := by rw [← hk, renameKeyElem_right]
        subst hk'
        by_cases hw : m.writes b f = true
        · simp only [renameKeyElem_left, hw, and_self, ↓reduceIte]
          change evalExpr m.ops
              (m.toEquivState (renameState p s.1) (m.renamePh p s.2.1)
                (m.fieldModel.reads b (renameKeyElem p w.1) (m.renameVals p s.2.2)))
              (m.toEquivState (renameState p c') (m.renamePh p s.2.1)
                (m.fieldModel.reads b (renameKeyElem p w.1) (m.renameVals p s.2.2)))
              (pushList (m.stepBaseEnv b (renameKeyElem p w.1)) (w.2.map (renameVal p)))
              (m.stepValueExpr b f) =
            renameVal p (evalExpr m.ops
              (m.toEquivState s.1 s.2.1 (m.fieldModel.reads b w.1 s.2.2))
              (m.toEquivState c' s.2.1 (m.fieldModel.reads b w.1 s.2.2))
              (pushList (m.stepBaseEnv b w.1) w.2) (m.stepValueExpr b f))
          rw [m.reads_rename, m.toEquivState_rename, m.toEquivState_rename, m.stepBaseEnv_rename, ← renameEnv_pushList]
          exact evalExpr_equivariant p m.ops _ _ (pushList (m.stepBaseEnv b w.1) w.2) (m.stepValueExpr b f)
        · simp only [renameKeyElem_left, hw, Bool.false_eq_true, and_false, ↓reduceIte]
      · have hk' : k ≠ renameKeyElem p w.1 := fun h => hk (by rw [h, renameKeyElem_left])
        simp only [hk, hk', false_and, ↓reduceIte]

theorem intermediate_next_rename (p : GroupPerm sizes) (a b : m.FState)
    (h : m.intermediate.next a b) :
    m.intermediate.next (m.renameFieldState p a) (m.renameFieldState p b) := by
  obtain ⟨br, w, hen, hstep⟩ := h
  refine ⟨br, m.renameW p w, (m.enabled_rename p a b.1 br w).mpr hen, ?_⟩
  change m.renameFieldState p b = m.fieldProject (m.fieldModel.advance (m.renameFieldState p a) (renameState p b.1) br (m.renameW p w))
  rw [m.advance_rename, m.fieldProject_rename]
  exact congrArg (m.renameFieldState p) hstep

theorem intermediate_safe_rename (p : GroupPerm sizes) (a : m.FState) :
    m.intermediate.safe (m.renameFieldState p a) ↔ m.intermediate.safe a := by
  change evalForm m.ops
      (m.toEquivState (renameState p a.1) (m.renamePh p a.2.1) (m.fieldModel.observations (m.renamePh p a.2.1) (m.renameVals p a.2.2)))
      (m.toEquivState (renameState p a.1) (m.renamePh p a.2.1) (m.fieldModel.observations (m.renamePh p a.2.1) (m.renameVals p a.2.2)))
      emptyEnv m.obsForm ↔
    evalForm m.ops (m.toEquivState a.1 a.2.1 (m.fieldModel.observations a.2.1 a.2.2))
      (m.toEquivState a.1 a.2.1 (m.fieldModel.observations a.2.1 a.2.2)) emptyEnv m.obsForm
  rw [m.observations_rename, m.toEquivState_rename]
  have h := evalForm_equivariant p m.ops (m.toEquivState a.1 a.2.1 (m.fieldModel.observations a.2.1 a.2.2))
    (m.toEquivState a.1 a.2.1 (m.fieldModel.observations a.2.1 a.2.2)) emptyEnv m.obsForm
  rwa [renameEnv_empty] at h

theorem intermediate_initSafe_rename (p : GroupPerm sizes) (a : m.FState) :
    m.constrainedIntermediate.initSafe (m.renameFieldState p a) ↔ m.constrainedIntermediate.initSafe a := by
  change evalForm m.ops
      (m.toEquivState (renameState p a.1) (m.renamePh p a.2.1) (m.fieldModel.observations (m.renamePh p a.2.1) (m.renameVals p a.2.2)))
      (m.toEquivState (renameState p a.1) (m.renamePh p a.2.1) (m.fieldModel.observations (m.renamePh p a.2.1) (m.renameVals p a.2.2)))
      emptyEnv m.initObsForm ↔
    evalForm m.ops (m.toEquivState a.1 a.2.1 (m.fieldModel.observations a.2.1 a.2.2))
      (m.toEquivState a.1 a.2.1 (m.fieldModel.observations a.2.1 a.2.2)) emptyEnv m.initObsForm
  rw [m.observations_rename, m.toEquivState_rename]
  have h := evalForm_equivariant p m.ops (m.toEquivState a.1 a.2.1 (m.fieldModel.observations a.2.1 a.2.2))
    (m.toEquivState a.1 a.2.1 (m.fieldModel.observations a.2.1 a.2.2)) emptyEnv m.initObsForm
  rwa [renameEnv_empty] at h

theorem intermediate_constraint_rename (p : GroupPerm sizes) (a : m.FState) :
    m.constrainedIntermediate.constraint (m.renameFieldState p a) ↔ m.constrainedIntermediate.constraint a := by
  change evalForm m.ops
      (m.toEquivState (renameState p a.1) (m.renamePh p a.2.1) (m.fieldModel.observations (m.renamePh p a.2.1) (m.renameVals p a.2.2)))
      (m.toEquivState (renameState p a.1) (m.renamePh p a.2.1) (m.fieldModel.observations (m.renamePh p a.2.1) (m.renameVals p a.2.2)))
      emptyEnv m.constraintForm ↔
    evalForm m.ops (m.toEquivState a.1 a.2.1 (m.fieldModel.observations a.2.1 a.2.2))
      (m.toEquivState a.1 a.2.1 (m.fieldModel.observations a.2.1 a.2.2)) emptyEnv m.constraintForm
  rw [m.observations_rename, m.toEquivState_rename]
  have h := evalForm_equivariant p m.ops (m.toEquivState a.1 a.2.1 (m.fieldModel.observations a.2.1 a.2.2))
    (m.toEquivState a.1 a.2.1 (m.fieldModel.observations a.2.1 a.2.2)) emptyEnv m.constraintForm
  rwa [renameEnv_empty] at h

theorem intermediate_actionConstraint_rename (p : GroupPerm sizes) (a b : m.FState) :
    m.constrainedIntermediate.actionConstraint (m.renameFieldState p a) (m.renameFieldState p b) ↔
      m.constrainedIntermediate.actionConstraint a b := by
  change evalForm m.ops
      (m.toEquivState (renameState p a.1) (m.renamePh p a.2.1) (m.fieldModel.observations (m.renamePh p a.2.1) (m.renameVals p a.2.2)))
      (m.toEquivState (renameState p b.1) (m.renamePh p b.2.1) (m.fieldModel.observations (m.renamePh p b.2.1) (m.renameVals p b.2.2)))
      emptyEnv m.actionConstraintForm ↔
    evalForm m.ops (m.toEquivState a.1 a.2.1 (m.fieldModel.observations a.2.1 a.2.2))
      (m.toEquivState b.1 b.2.1 (m.fieldModel.observations b.2.1 b.2.2)) emptyEnv m.actionConstraintForm
  rw [m.observations_rename, m.observations_rename, m.toEquivState_rename, m.toEquivState_rename]
  have h := evalForm_equivariant p m.ops
    (m.toEquivState a.1 a.2.1 (m.fieldModel.observations a.2.1 a.2.2))
    (m.toEquivState b.1 b.2.1 (m.fieldModel.observations b.2.1 b.2.2)) emptyEnv m.actionConstraintForm
  rwa [renameEnv_empty] at h

theorem intermediate_actionSafe_rename (p : GroupPerm sizes) (a b : m.FState) :
    m.constrainedIntermediate.actionSafe (m.renameFieldState p a) (m.renameFieldState p b) ↔
      m.constrainedIntermediate.actionSafe a b := by
  change evalForm m.ops
      (m.toEquivState (renameState p a.1) (m.renamePh p a.2.1) (m.fieldModel.observations (m.renamePh p a.2.1) (m.renameVals p a.2.2)))
      (m.toEquivState (renameState p b.1) (m.renamePh p b.2.1) (m.fieldModel.observations (m.renamePh p b.2.1) (m.renameVals p b.2.2)))
      emptyEnv m.actionObsForm ↔
    evalForm m.ops (m.toEquivState a.1 a.2.1 (m.fieldModel.observations a.2.1 a.2.2))
      (m.toEquivState b.1 b.2.1 (m.fieldModel.observations b.2.1 b.2.2)) emptyEnv m.actionObsForm
  rw [m.observations_rename, m.observations_rename, m.toEquivState_rename, m.toEquivState_rename]
  have h := evalForm_equivariant p m.ops
    (m.toEquivState a.1 a.2.1 (m.fieldModel.observations a.2.1 a.2.2))
    (m.toEquivState b.1 b.2.1 (m.fieldModel.observations b.2.1 b.2.2)) emptyEnv m.actionObsForm
  rwa [renameEnv_empty] at h

-- Step 2: Symmetry quotient on the exact FieldRule projected system `m.intermediate`.
def orbitQuotient : OrbitQuotient sizes m.FState where
  system := m.constrainedIntermediate
  rename := m.renameFieldState
  rename_identity := m.renameFieldState_identity
  rename_then := m.renameFieldState_then
  rename_inverse := m.renameFieldState_inverse
  next_rename := m.intermediate_next_rename
  safe_rename := m.intermediate_safe_rename
  initSafe_rename := m.intermediate_initSafe_rename
  constraint_rename := m.intermediate_constraint_rename
  actionConstraint_rename := m.intermediate_actionConstraint_rename
  actionSafe_rename := m.intermediate_actionSafe_rename

def FieldOrbit (a b : m.FState) : Prop :=
  m.orbitQuotient.Orbit a b

def fieldOrbits : Setoid m.FState :=
  m.orbitQuotient.setoid

def symProject (a : m.FState) : Quotient m.fieldOrbits :=
  m.orbitQuotient.symProject a

def reduced : System (Quotient m.fieldOrbits) :=
  m.orbitQuotient.reduced

theorem symmetry_certificate : Certificate m.intermediate m.reduced m.symProject :=
  m.orbitQuotient.symmetry_certificate

def project (s : m.FState) : Quotient m.fieldOrbits :=
  m.symProject (m.fieldProject s)

theorem certificate : Certificate m.concrete m.reduced m.project :=
  compose (p := m.fieldProject) (q := m.symProject) m.field_certificate m.symmetry_certificate

theorem orbit_key_equivalent (s t : m.FState) :
    m.project s = m.project t ↔ m.FieldOrbit (m.fieldProject s) (m.fieldProject t) := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound (show m.fieldOrbits.r (m.fieldProject s) (m.fieldProject t) from h)

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

theorem deadlock_preserved (s : m.FState) :
    (¬ ∃ t, m.concrete.next s t) ↔ (¬ ∃ q, m.reduced.next (m.project s) q) := by
  constructor
  · intro noStep ⟨q, hq⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s q).mp hq
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨m.project t, (m.certificate.next s (m.project t)).mpr ⟨t, ht, rfl⟩⟩

def constrainedReduced : ConstrainedSystem (Quotient m.fieldOrbits) :=
  m.orbitQuotient.constrainedReduced

theorem symmetry_constrained_certificate :
    ConstrainedCertificate m.constrainedIntermediate m.constrainedReduced m.symProject :=
  m.orbitQuotient.symmetry_constrained_certificate

theorem constrained_certificate :
    ConstrainedCertificate m.constrainedConcrete m.constrainedReduced m.project :=
  composeConstrained (p := m.fieldProject) (q := m.symProject)
    m.field_constrained_certificate m.symmetry_constrained_certificate

end Model
end
end TlxOptimization.FieldSymRule
