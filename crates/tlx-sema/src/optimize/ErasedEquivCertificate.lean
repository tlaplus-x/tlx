/- Certified composition of unobserved-variable erasure with generic recursive
equivariant symmetry (`EquivSymCertificate.lean`) over one shared source model.
Hidden initializations and updates share the exact branch choice and witness
list of the concrete system; retained formulas and observations cannot inspect
hidden state. -/
set_option autoImplicit false
namespace TlxOptimization.ErasedEquivRule
open TlxOptimization EquivRule
noncomputable section

structure Branch (d : Nat) (V : Type) where
  bounds : List (SetPred d V)
  body : Form d V

def evalBranchWithWitness {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A]
    (ops : AtomOps A) (s t : State V sizes A) (env : Env sizes A) :
    List (SetPred d V) → List (Val sizes A) → Form d V → Prop
  | [], [], body => evalForm ops s t env body
  | dom :: doms, w :: ws, body =>
      evalSetPred ops s t env dom w ∧ evalBranchWithWitness ops s t (push env w) doms ws body
  | _, _, _ => False

def branchToForm {d : Nat} {V : Type} : List (SetPred d V) → Form d V → Form d V
  | [], body => body
  | dom :: doms, body => .some dom (branchToForm doms body)

def branchesToForm {d : Nat} {V : Type} : List (Branch d V) → Form d V
  | [] => .truth false
  | b :: bs => .disj (branchToForm b.bounds b.body) (branchesToForm bs)

private theorem exists_witness_iff_branchToForm {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A]
    (ops : AtomOps A) (s t : State V sizes A) :
    ∀ (doms : List (SetPred d V)) (env : Env sizes A) (body : Form d V),
      (∃ ws : List (Val sizes A), evalBranchWithWitness ops s t env doms ws body) ↔
        evalForm ops s t env (branchToForm doms body)
  | [], env, body => by
    constructor
    · rintro ⟨ws, h⟩
      cases ws with
      | nil => exact h
      | cons _ _ => exact False.elim h
    · intro h
      exact ⟨[], h⟩
  | dom :: doms, env, body => by
    simp only [branchToForm, evalForm]
    constructor
    · rintro ⟨ws, h⟩
      cases ws with
      | nil => exact False.elim h
      | cons w ws' =>
        exact ⟨w, h.1, (exists_witness_iff_branchToForm ops s t doms (push env w) body).mp ⟨ws', h.2⟩⟩
    · rintro ⟨w, hw, hrest⟩
      obtain ⟨ws', hws'⟩ := (exists_witness_iff_branchToForm ops s t doms (push env w) body).mpr hrest
      exact ⟨w :: ws', hw, hws'⟩

private theorem exists_branch_iff_branchesToForm {d : Nat} {sizes : Fin d → Nat} {V A : Type} [HasNatAtom A]
    (ops : AtomOps A) (s t : State V sizes A) (env : Env sizes A) :
    ∀ (bs : List (Branch d V)),
      (∃ (b : Fin bs.length) (ws : List (Val sizes A)),
        evalBranchWithWitness ops s t env (bs[b.val]'b.isLt).bounds ws (bs[b.val]'b.isLt).body) ↔
        evalForm ops s t env (branchesToForm bs)
  | [] => by
    constructor
    · rintro ⟨b, _⟩
      exact Fin.elim0 b
    · intro h
      simp only [branchesToForm, evalForm] at h
      exact Bool.noConfusion h
  | b0 :: bs => by
    simp only [branchesToForm, evalForm]
    constructor
    · rintro ⟨b, ws, h⟩
      cases b using Fin.cases with
      | zero =>
        left
        exact (exists_witness_iff_branchToForm ops s t b0.bounds env b0.body).mp ⟨ws, h⟩
      | succ b' =>
        right
        exact (exists_branch_iff_branchesToForm ops s t env bs).mp ⟨b', ws, h⟩
    · rintro (h | h)
      · obtain ⟨ws, hws⟩ := (exists_witness_iff_branchToForm ops s t b0.bounds env b0.body).mpr h
        exact ⟨⟨0, Nat.zero_lt_succ _⟩, ws, hws⟩
      · obtain ⟨b', ws, hws⟩ := (exists_branch_iff_branchesToForm ops s t env bs).mpr h
        exact ⟨b'.succ, ws, hws⟩

structure Model (d : Nat) (sizes : Fin d → Nat) (V A H : Type) [HasNatAtom A] where
  ops : AtomOps A
  initBranches : List (Branch d V)
  hiddenSeed : Fin initBranches.length → State V sizes A → List (Val sizes A) → H
  stepBranches : List (Branch d V)
  hiddenUpdate : Fin stepBranches.length → State V sizes A → State V sizes A → List (Val sizes A) → H → H
  obsForm : Form d V
  initObsForm : Form d V := .truth true
  constraintForm : Form d V := .truth true
  actionConstraintForm : Form d V := .truth true
  actionObsForm : Form d V := .truth true

namespace Model
variable {d : Nat} {sizes : Fin d → Nat} {V A H : Type} [HasNatAtom A] (m : Model d sizes V A H)
abbrev Source (_m : Model d sizes V A H) := State V sizes A × H

def concrete : System m.Source where
  initial s := ∃ (b : Fin m.initBranches.length) (ws : List (Val sizes A)),
    evalBranchWithWitness m.ops s.1 s.1 emptyEnv (m.initBranches[b.val]'b.isLt).bounds ws (m.initBranches[b.val]'b.isLt).body ∧
    s.2 = m.hiddenSeed b s.1 ws
  next s t := ∃ (b : Fin m.stepBranches.length) (ws : List (Val sizes A)),
    evalBranchWithWitness m.ops s.1 t.1 emptyEnv (m.stepBranches[b.val]'b.isLt).bounds ws (m.stepBranches[b.val]'b.isLt).body ∧
    t.2 = m.hiddenUpdate b s.1 t.1 ws s.2
  safe s := evalForm m.ops s.1 s.1 emptyEnv m.obsForm

def erased : EquivRule.Model d sizes V A where
  ops := m.ops
  initForm := branchesToForm m.initBranches
  nextForm := branchesToForm m.stepBranches
  obsForm := m.obsForm
  initObsForm := m.initObsForm
  constraintForm := m.constraintForm
  actionConstraintForm := m.actionConstraintForm
  actionObsForm := m.actionObsForm

def erase (s : m.Source) : State V sizes A := s.1

theorem erasure_certificate : Certificate m.concrete m.erased.concrete m.erase := by
  constructor
  · intro a
    constructor
    · intro hi
      obtain ⟨b, ws, hb⟩ := (exists_branch_iff_branchesToForm m.ops a a emptyEnv m.initBranches).mpr hi
      exact ⟨(a, m.hiddenSeed b a ws), ⟨b, ws, hb, rfl⟩, rfl⟩
    · rintro ⟨s, ⟨b, ws, hb, _⟩, rfl⟩
      exact (exists_branch_iff_branchesToForm m.ops s.1 s.1 emptyEnv m.initBranches).mp ⟨b, ws, hb⟩
  · intro s a
    constructor
    · intro hn
      obtain ⟨b, ws, hb⟩ := (exists_branch_iff_branchesToForm m.ops s.1 a emptyEnv m.stepBranches).mpr hn
      exact ⟨(a, m.hiddenUpdate b s.1 a ws s.2), ⟨b, ws, hb, rfl⟩, rfl⟩
    · rintro ⟨t, ⟨b, ws, hb, _⟩, rfl⟩
      exact (exists_branch_iff_branchesToForm m.ops s.1 t.1 emptyEnv m.stepBranches).mp ⟨b, ws, hb⟩
  · intro s
    rfl

noncomputable def reduced := m.erased.reduced
def project (s : m.Source) := EquivRule.project (m.erase s)

theorem certificate : Certificate m.concrete m.reduced m.project :=
  compose (p := m.erase) (q := EquivRule.project) m.erasure_certificate m.erased.certificate

theorem orbit_key_equivalent (s t : m.Source) :
    m.project s = m.project t ↔ Orbit s.1 t.1 := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound (show (orbits V sizes A).r s.1 t.1 from h)

theorem optimization_correct :
    (∀ s, Reachable m.concrete s → m.concrete.safe s) ↔
    (∀ a, Reachable m.reduced a → m.reduced.safe a) := safety_iff m.certificate

theorem specification_correct :
    (∀ s, Reachable (withStuttering m.concrete) s → m.concrete.safe s) ↔
    (∀ a, Reachable (withStuttering m.reduced) a → m.reduced.safe a) := by
  simpa only [stuttering_reachable_iff] using m.optimization_correct

theorem counterexample_lifts {a} (ha : Reachable m.reduced a) (bad : ¬ m.reduced.safe a) :
    ∃ s, Reachable m.concrete s ∧ m.project s = a ∧ ¬ m.concrete.safe s := by
  obtain ⟨s, hs, he⟩ := reachable_backward m.certificate ha
  refine ⟨s, hs, he, ?_⟩
  intro good
  apply bad
  rw [← he]
  exact (m.certificate.observe s).mp good

theorem deadlock_preserved (s : m.Source) :
    (¬ ∃ t, m.concrete.next s t) ↔ (¬ ∃ a, m.reduced.next (m.project s) a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s a).mp ha
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨m.project t, (m.certificate.next s (m.project t)).mpr ⟨t, ht, rfl⟩⟩

def constrainedConcrete : ConstrainedSystem m.Source where
  toSystem := m.concrete
  initSafe s := m.erased.constrainedConcrete.initSafe s.1
  constraint s := m.erased.constrainedConcrete.constraint s.1
  actionConstraint s t := m.erased.constrainedConcrete.actionConstraint s.1 t.1
  actionSafe s t := m.erased.constrainedConcrete.actionSafe s.1 t.1

theorem erasure_constrained_certificate :
    ConstrainedCertificate m.constrainedConcrete m.erased.constrainedConcrete m.erase := by
  refine ⟨m.erasure_certificate.initial, m.erasure_certificate.next, m.erasure_certificate.observe,
    fun _ => Iff.rfl, fun _ => Iff.rfl, ?_, ?_⟩
  · intro s a
    constructor
    · rintro ⟨hn, hc, hac⟩
      obtain ⟨b, ws, hb⟩ := (exists_branch_iff_branchesToForm m.ops s.1 a emptyEnv m.stepBranches).mpr hn
      exact ⟨(a, m.hiddenUpdate b s.1 a ws s.2), ⟨b, ws, hb, rfl⟩, hc, hac, rfl⟩
    · rintro ⟨t, ⟨b, ws, hb, _⟩, hc, hac, rfl⟩
      exact ⟨(exists_branch_iff_branchesToForm m.ops s.1 t.1 emptyEnv m.stepBranches).mp ⟨b, ws, hb⟩, hc, hac⟩
  · intro s a
    constructor
    · intro h hn
      obtain ⟨b, ws, hb⟩ := (exists_branch_iff_branchesToForm m.ops s.1 a emptyEnv m.stepBranches).mpr hn
      exact h (a, m.hiddenUpdate b s.1 a ws s.2) ⟨b, ws, hb, rfl⟩ rfl
    · intro h t ⟨b, ws, hb, _⟩ rfl
      exact h ((exists_branch_iff_branchesToForm m.ops s.1 t.1 emptyEnv m.stepBranches).mp ⟨b, ws, hb⟩)

noncomputable def constrainedReduced := m.erased.constrainedReduced

theorem constrained_certificate :
    ConstrainedCertificate m.constrainedConcrete m.constrainedReduced m.project :=
  composeConstrained (p := m.erase) (q := EquivRule.project)
    m.erasure_constrained_certificate m.erased.constrained_certificate

end Model
end
end TlxOptimization.ErasedEquivRule
