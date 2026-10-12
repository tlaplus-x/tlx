/- Homogeneous keyed-state rule IR. All key equality, quantifiers and map reads
are explicit. Semantic leaves receive payloads and key-independent state only. -/
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

abbrev Environment (K : Type) := Nat → K
abbrev Maps (M K V : Type) := M → K → V
abbrev State (C M K V : Type) := C × Maps M K V

def push {K : Type} (keys : Environment K) (k : K) : Environment K
  | 0 => k
  | i+1 => keys i

def renameKeys {K : Type} (p : Permutation K) (keys : Environment K) : Environment K :=
  fun i => p.toFun (keys i)
def renameMaps {M K V : Type} (p : Permutation K) (r : Maps M K V) : Maps M K V :=
  fun m k => r m (p.invFun k)
def rename {C M K V : Type} (p : Permutation K) (s : State C M K V) : State C M K V :=
  (s.1, renameMaps p s.2)

theorem renameKeys_push {K : Type} (p : Permutation K) (keys : Environment K) (k : K) :
    renameKeys p (push keys k) = push (renameKeys p keys) (p.toFun k) := by
  funext i
  cases i <;> rfl

def read {M K V : Type} (r : Maps M K V) (keys : Environment K) (reads : List (M × Nat)) : List V :=
  reads.map (fun item => r item.1 (keys item.2))

theorem read_rename {M K V : Type} (p : Permutation K) (r : Maps M K V)
    (keys : Environment K) (reads : List (M × Nat)) :
    read (renameMaps p r) (renameKeys p keys) reads = read r keys reads := by
  simp [read, renameMaps, renameKeys, p.left]

inductive Test (M : Type) where
  | truth (value : Bool)
  | leaf (id : Nat) (reads : List (M × Nat))
  | equal (left right : Nat)
  | conj (left right : Test M)
  | disj (left right : Test M)
  | neg (body : Test M)
  | all (body : Test M)
  | some (body : Test M)

def Test.eval {M K V : Type} (leaf : Nat → List V → Prop) (r : Maps M K V)
    (keys : Environment K) : Test M → Prop
  | .truth value => value = true
  | .leaf id reads => leaf id (read r keys reads)
  | .equal a b => keys a = keys b
  | .conj a b => a.eval leaf r keys ∧ b.eval leaf r keys
  | .disj a b => a.eval leaf r keys ∨ b.eval leaf r keys
  | .neg a => ¬ a.eval leaf r keys
  | .all a => ∀ k, a.eval leaf r (push keys k)
  | .some a => ∃ k, a.eval leaf r (push keys k)

theorem Test.equivariant {M K V : Type} (p : Permutation K) (leaf : Nat → List V → Prop)
    (r : Maps M K V) (test : Test M) (keys : Environment K) :
    test.eval leaf (renameMaps p r) (renameKeys p keys) ↔ test.eval leaf r keys := by
  induction test generalizing keys with
  | truth value => rfl
  | leaf id reads => simp only [Test.eval, read_rename]
  | equal a b => exact p.injective
  | conj a b ha hb => exact and_congr (ha keys) (hb keys)
  | disj a b ha hb => exact or_congr (ha keys) (hb keys)
  | neg a ha => exact not_congr (ha keys)
  | all a ha =>
    constructor
    · intro h k
      apply (ha (push keys k)).mp
      rw [renameKeys_push]
      exact h (p.toFun k)
    · intro h k
      have hp := (ha (push keys (p.invFun k))).mpr (h (p.invFun k))
      simpa only [renameKeys_push, p.right] using hp
  | some a ha =>
    constructor
    · rintro ⟨k, h⟩
      refine ⟨p.invFun k, (ha (push keys (p.invFun k))).mp ?_⟩
      simpa only [renameKeys_push, p.right] using h
    · rintro ⟨k, h⟩
      refine ⟨p.toFun k, ?_⟩
      have hp := (ha (push keys k)).mpr h
      simpa only [renameKeys_push] using hp

inductive ValueExpr (M : Type) where
  | leaf (id : Nat) (reads : List (M × Nat))
  | branch (condition : Test M) (yes no : ValueExpr M)

def ValueExpr.eval {M K V : Type} (test : Nat → List V → Prop) (value : Nat → List V → V)
    (r : Maps M K V) (keys : Environment K) : ValueExpr M → V := by
  classical
  exact fun e => match e with
    | .leaf id reads => value id (read r keys reads)
    | .branch condition yes no => if condition.eval test r keys then yes.eval test value r keys else no.eval test value r keys

theorem ValueExpr.equivariant {M K V : Type} (p : Permutation K)
    (test : Nat → List V → Prop) (value : Nat → List V → V)
    (r : Maps M K V) (keys : Environment K) (e : ValueExpr M) :
    e.eval test value (renameMaps p r) (renameKeys p keys) = e.eval test value r keys := by
  induction e with
  | leaf id reads => simp only [ValueExpr.eval, read_rename]
  | branch condition yes no hy hn =>
    simp only [ValueExpr.eval, hy, hn]
    rw [propext (Test.equivariant p test r condition keys)]

structure Write (M : Type) where
  map : M
  key : Nat
  value : ValueExpr M

def Write.apply {M K V : Type} (test : Nat → List V → Prop) (value : Nat → List V → V) (original : Maps M K V)
    (keys : Environment K) (current : Maps M K V) (w : Write M) : Maps M K V := by
  classical
  exact fun m k => if m = w.map ∧ k = keys w.key then w.value.eval test value original keys else current m k

theorem Write.equivariant {M K V : Type} (p : Permutation K) (test : Nat → List V → Prop) (value : Nat → List V → V)
    (original current : Maps M K V) (keys : Environment K) (w : Write M) :
    w.apply test value (renameMaps p original) (renameKeys p keys) (renameMaps p current) =
      renameMaps p (w.apply test value original keys current) := by
  classical
  funext m k
  have eq : k = p.toFun (keys w.key) ↔ p.invFun k = keys w.key := by
    constructor
    · intro h; rw [h, p.left]
    · intro h; rw [← h, p.right]
  simp only [Write.apply, ValueExpr.equivariant, renameMaps, renameKeys]
  simp only [eq]

def update {M K V : Type} (test : Nat → List V → Prop) (value : Nat → List V → V) (r : Maps M K V)
    (keys : Environment K) (writes : List (Write M)) : Maps M K V :=
  writes.foldl (fun current w => w.apply test value r keys current) r

theorem update_equivariant {M K V : Type} (p : Permutation K) (test : Nat → List V → Prop) (value : Nat → List V → V)
    (r : Maps M K V) (keys : Environment K) (writes : List (Write M)) :
    update test value (renameMaps p r) (renameKeys p keys) writes = renameMaps p (update test value r keys writes) := by
  have fold (ws : List (Write M)) (current : Maps M K V) :
      ws.foldl (fun r' w => w.apply test value (renameMaps p r) (renameKeys p keys) r') (renameMaps p current) =
      renameMaps p (ws.foldl (fun r' w => w.apply test value r keys r') current) := by
    induction ws generalizing current with
    | nil => rfl
    | cons w ws ih =>
      simp only [List.foldl_cons, Write.equivariant]
      exact ih _
  exact fold writes r

theorem rename_identity {C M K V : Type} (s : State C M K V) :
    rename Permutation.identity s = s := rfl

theorem rename_then {C M K V : Type} (p q : Permutation K) (s : State C M K V) :
    rename (p.then q) s = rename q (rename p s) := rfl

theorem rename_inverse {C M K V : Type} (p : Permutation K) (s : State C M K V) :
    rename p.inverse (rename p s) = s := by
  apply Prod.ext
  · rfl
  funext m k
  exact congrArg (s.2 m) (p.left k)

def Orbit {C M K V : Type} (s t : State C M K V) : Prop := ∃ p, rename p s = t

def orbits (C M K V : Type) : Setoid (State C M K V) where
  r := Orbit
  iseqv := {
    refl := fun s => ⟨Permutation.identity, rename_identity s⟩
    symm := by
      rintro s t ⟨p, rfl⟩
      exact ⟨p.inverse, rename_inverse p s⟩
    trans := by
      rintro s t u ⟨p, rfl⟩ ⟨q, rfl⟩
      exact ⟨p.then q, rfl⟩ }

def project {C M K V : Type} (s : State C M K V) : Quotient (orbits C M K V) :=
  Quotient.mk _ s

theorem project_rename {C M K V : Type} (p : Permutation K) (s : State C M K V) :
    project (rename p s) = project s := by
  have h : project s = project (rename p s) := Quotient.sound (show Orbit s (rename p s) from ⟨p, rfl⟩)
  exact h.symm

structure Model (C M K V B W : Type) where
  initial : State C M K V → Prop
  guard : B → Test M
  test : B → C → C → W → Nat → List V → Prop
  writes : B → List (Write M)
  value : B → C → C → W → Nat → List V → V
  observation : Test M
  observe : C → Nat → List V → Prop

namespace Model
variable {C M K V B W : Type} (m : Model C M K V B W)

def concrete : System (State C M K V) where
  initial := m.initial
  next s t := ∃ b w keys, (m.guard b).eval (m.test b s.1 t.1 w) s.2 keys ∧
    t = (t.1, update (m.test b s.1 t.1 w) (m.value b s.1 t.1 w) s.2 keys (m.writes b))
  safe s := ∀ keys, m.observation.eval (m.observe s.1) s.2 keys

theorem next_rename (p : Permutation K) (s t : State C M K V) (h : m.concrete.next s t) :
    m.concrete.next (rename p s) (rename p t) := by
  obtain ⟨b, w, keys, hg, ht⟩ := h
  refine ⟨b, w, renameKeys p keys, (Test.equivariant p _ _ _ keys).mpr hg, ?_⟩
  have hu := update_equivariant p (m.test b s.1 t.1 w) (m.value b s.1 t.1 w) s.2 keys (m.writes b)
  apply Prod.ext
  · rfl
  change renameMaps p t.2 = _
  change renameMaps p t.2 = update (m.test b s.1 t.1 w) (m.value b s.1 t.1 w) (renameMaps p s.2) (renameKeys p keys) (m.writes b)
  rw [hu]
  exact congrArg (renameMaps p) (congrArg Prod.snd ht)

theorem safe_rename (p : Permutation K) (s : State C M K V) :
    m.concrete.safe (rename p s) ↔ m.concrete.safe s := by
  constructor
  · intro h keys
    exact (Test.equivariant p _ _ _ keys).mp (h (renameKeys p keys))
  · intro h keys
    have hp := (Test.equivariant p (m.observe s.1) s.2 m.observation (renameKeys p.inverse keys)).mpr (h (renameKeys p.inverse keys))
    have hk : renameKeys p (renameKeys p.inverse keys) = keys := by
      funext i
      exact p.right (keys i)
    rw [hk] at hp
    exact hp

def reduced : System (Quotient (orbits C M K V)) where
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

theorem deadlock_preserved (s : State C M K V) :
    (¬ ∃ t, m.concrete.next s t) ↔ (¬ ∃ a, m.reduced.next (project s) a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s a).mp ha
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨project t, (m.certificate.next s (project t)).mpr ⟨t, ht, rfl⟩⟩

theorem orbit_key_equivalent (s t : State C M K V) :
    project s = project t ↔ Orbit s t := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound (show (orbits C M K V).r s t from h)
end Model
end
end TlxOptimization.KeyedRule
