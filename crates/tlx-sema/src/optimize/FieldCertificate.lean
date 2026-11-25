/- Phase-dependent field erasure. The finite read/write tables carry checked
liveness side conditions; no transition-preservation premise is assumed. -/
set_option autoImplicit false
namespace TlxOptimization.FieldRule
open TlxOptimization
noncomputable section

abbrev State (C K P F V : Type) := C × ((K → P) × (K → F → V))

structure Model (C K P F V B W : Type) where
  missing : V
  live : P → F → Bool
  source : B → P
  target : B → P
  readsActor : B → F → Bool
  readsGlobal : B → F → Bool
  writes : B → F → Bool
  observed : F → Bool
  actorLive : ∀ b f, readsActor b f = true → live (source b) f = true
  globalLive : ∀ b p f, readsGlobal b f = true → live p f = true
  frameLive : ∀ b f, live (target b) f = true → writes b f = false → live (source b) f = true
  observedLive : ∀ p f, observed f = true → live p f = true
  actor : B → W → K
  initial : C → B → W → Prop
  seedPhase : C → B → W → K → P
  seedValue : C → B → W → K → F → V
  guard : B → C → C → W → (K → P) → (K → F → V) → Prop
  value : B → C → C → W → (K → P) → (K → F → V) → F → V
  observe : C → (K → P) → (K → F → V) → Prop
  initObserve : C → (K → P) → (K → F → V) → Prop := fun _ _ _ => True
  constraint : C → (K → P) → (K → F → V) → Prop := fun _ _ _ => True
  -- Action checks see both endpoints' retained phases and observed values.
  -- The default is the vacuous predicate used by unconstrained checks.
  actionConstraint : C → C → (K → P) → (K → P) → (K → F → V) → (K → F → V) → Prop :=
    fun _ _ _ _ _ _ => True
  actionObserve : C → C → (K → P) → (K → P) → (K → F → V) → (K → F → V) → Prop :=
    fun _ _ _ _ _ _ => True

namespace Model
variable {C K P F V B W : Type} (m : Model C K P F V B W)

def mask (p : K → P) (v : K → F → V) : K → F → V :=
  fun k f => if m.live (p k) f then v k f else m.missing

def reads (b : B) (a : K) (v : K → F → V) : K → F → V := by
  classical
  exact fun k f => if m.readsGlobal b f || (decide (k = a) && m.readsActor b f) then v k f else m.missing

def observations (v : K → F → V) : K → F → V :=
  fun k f => if m.observed f then v k f else m.missing

theorem reads_mask (b : B) (a : K) (p : K → P) (v : K → F → V)
    (phase : p a = m.source b) : m.reads b a (m.mask p v) = m.reads b a v := by
  classical
  funext k f
  by_cases hg : m.readsGlobal b f = true
  · simp [reads, mask, hg, m.globalLive b (p k) f hg]
  · have hg' : m.readsGlobal b f = false := Bool.eq_false_iff.mpr hg
    by_cases hk : k = a
    · subst k
      by_cases hr : m.readsActor b f = true
      · simp [reads, mask, hg', hr, phase, m.actorLive b f hr]
      · simp [reads, hg', Bool.eq_false_iff.mpr hr]
    · simp [reads, hg', hk]

theorem observations_mask (p : K → P) (v : K → F → V) :
    m.observations (m.mask p v) = m.observations v := by
  funext k f
  by_cases h : m.observed f = true
  · simp [observations, mask, h, m.observedLive (p k) f h]
  · simp [observations, Bool.eq_false_iff.mpr h]

def project (s : State C K P F V) : State C K P F V :=
  (s.1, (s.2.1, m.mask s.2.1 s.2.2))
def seed (c : C) (b : B) (w : W) : State C K P F V :=
  (c, (m.seedPhase c b w, m.seedValue c b w))
def advance (s : State C K P F V) (d : C) (b : B) (w : W) : State C K P F V := by
  classical
  let a := m.actor b w
  let input := m.reads b a s.2.2
  exact (d, ((fun k => if k = a then m.target b else s.2.1 k),
    fun k f => if k = a ∧ m.writes b f = true then m.value b s.1 d w s.2.1 input f else s.2.2 k f))

theorem advance_commutes (s : State C K P F V) (d : C) (b : B) (w : W)
    (phase : s.2.1 (m.actor b w) = m.source b) :
    m.project (m.advance s d b w) = m.project (m.advance (m.project s) d b w) := by
  classical
  change (d, _) = (d, _)
  apply congrArg (fun record => (d, record))
  apply Prod.ext
  · rfl
  funext k f
  change (if m.live (if k = m.actor b w then m.target b else s.2.1 k) f then
    (if k = m.actor b w ∧ m.writes b f = true then m.value b s.1 d w s.2.1 (m.reads b (m.actor b w) s.2.2) f else s.2.2 k f)
    else m.missing) = _
  simp only [project, advance, mask, m.reads_mask b (m.actor b w) s.2.1 s.2.2 phase]
  by_cases hk : k = m.actor b w
  · subst k
    by_cases hl : m.live (m.target b) f = true
    · by_cases hw : m.writes b f = true
      · simp [hl, hw]
      · have hw' : m.writes b f = false := Bool.eq_false_iff.mpr hw
        simp [hl, hw', phase, m.frameLive b f hl hw']
    · simp [Bool.eq_false_iff.mpr hl]
  · by_cases hl : m.live (s.2.1 k) f = true
    · simp [hk, hl]
    · simp [hk, Bool.eq_false_iff.mpr hl]

def enabled (s : State C K P F V) (d : C) (b : B) (w : W) : Prop :=
  s.2.1 (m.actor b w) = m.source b ∧
    m.guard b s.1 d w s.2.1 (m.reads b (m.actor b w) s.2.2)

theorem enabled_project (s : State C K P F V) (d : C) (b : B) (w : W) :
    m.enabled s d b w ↔ m.enabled (m.project s) d b w := by
  constructor <;> rintro ⟨phase, guard⟩
  · exact ⟨phase, by simpa only [project, m.reads_mask b (m.actor b w) s.2.1 s.2.2 phase] using guard⟩
  · exact ⟨phase, by simpa only [project, m.reads_mask b (m.actor b w) s.2.1 s.2.2 phase] using guard⟩

def concrete : System (State C K P F V) where
  initial s := ∃ c b w, m.initial c b w ∧ s = m.seed c b w
  next s t := ∃ b w, m.enabled s t.1 b w ∧ t = m.advance s t.1 b w
  safe s := m.observe s.1 s.2.1 (m.observations s.2.2)

def reduced : System (State C K P F V) where
  initial s := ∃ c b w, m.initial c b w ∧ s = m.project (m.seed c b w)
  next s t := ∃ b w, m.enabled s t.1 b w ∧ t = m.project (m.advance s t.1 b w)
  safe s := m.observe s.1 s.2.1 (m.observations s.2.2)

theorem certificate : Certificate m.concrete m.reduced m.project := by
  constructor
  · intro a
    constructor
    · rintro ⟨c, b, w, hi, rfl⟩
      exact ⟨m.seed c b w, ⟨c, b, w, hi, rfl⟩, rfl⟩
    · rintro ⟨s, ⟨c, b, w, hi, rfl⟩, rfl⟩
      exact ⟨c, b, w, hi, rfl⟩
  · intro s a
    constructor
    · rintro ⟨b, w, hg, ha⟩
      have hc := (m.enabled_project s a.1 b w).mpr hg
      refine ⟨m.advance s a.1 b w, ⟨b, w, hc, rfl⟩, ?_⟩
      exact (m.advance_commutes s a.1 b w hc.1).trans ha.symm
    · rintro ⟨t, ⟨b, w, hg, ht⟩, rfl⟩
      refine ⟨b, w, (m.enabled_project s t.1 b w).mp hg, ?_⟩
      exact (congrArg m.project ht).trans (m.advance_commutes s t.1 b w hg.1)
  · intro s
    change _ ↔ m.observe s.1 s.2.1 (m.observations (m.mask s.2.1 s.2.2))
    rw [m.observations_mask]
    rfl

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

theorem deadlock_preserved (s : State C K P F V) :
    (¬ ∃ t, m.concrete.next s t) ↔ (¬ ∃ a, m.reduced.next (m.project s) a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s a).mp ha
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨m.project t, (m.certificate.next s (m.project t)).mpr ⟨t, ht, rfl⟩⟩

def constrainedConcrete : ConstrainedSystem (State C K P F V) where
  toSystem := m.concrete
  initSafe s := m.initObserve s.1 s.2.1 (m.observations s.2.2)
  constraint s := m.constraint s.1 s.2.1 (m.observations s.2.2)
  actionConstraint s t :=
    m.actionConstraint s.1 t.1 s.2.1 t.2.1 (m.observations s.2.2) (m.observations t.2.2)
  actionSafe s t :=
    m.actionObserve s.1 t.1 s.2.1 t.2.1 (m.observations s.2.2) (m.observations t.2.2)

def constrainedReduced : ConstrainedSystem (State C K P F V) where
  toSystem := m.reduced
  initSafe s := m.initObserve s.1 s.2.1 (m.observations s.2.2)
  constraint s := m.constraint s.1 s.2.1 (m.observations s.2.2)
  actionConstraint s t :=
    m.actionConstraint s.1 t.1 s.2.1 t.2.1 (m.observations s.2.2) (m.observations t.2.2)
  actionSafe s t :=
    m.actionObserve s.1 t.1 s.2.1 t.2.1 (m.observations s.2.2) (m.observations t.2.2)

-- Projection keeps the retained core, the phase map and every observed value,
-- so both action checks are unchanged on the projected pair.
theorem actionConstraint_project (s t : State C K P F V) :
    m.constrainedConcrete.actionConstraint s t ↔
      m.constrainedReduced.actionConstraint (m.project s) (m.project t) := by
  change m.actionConstraint s.1 t.1 s.2.1 t.2.1 (m.observations s.2.2) (m.observations t.2.2) ↔
    m.actionConstraint s.1 t.1 s.2.1 t.2.1
      (m.observations (m.mask s.2.1 s.2.2)) (m.observations (m.mask t.2.1 t.2.2))
  rw [m.observations_mask, m.observations_mask]

theorem actionObserve_project (s t : State C K P F V) :
    m.constrainedConcrete.actionSafe s t ↔
      m.constrainedReduced.actionSafe (m.project s) (m.project t) := by
  change m.actionObserve s.1 t.1 s.2.1 t.2.1 (m.observations s.2.2) (m.observations t.2.2) ↔
    m.actionObserve s.1 t.1 s.2.1 t.2.1
      (m.observations (m.mask s.2.1 s.2.2)) (m.observations (m.mask t.2.1 t.2.2))
  rw [m.observations_mask, m.observations_mask]

theorem initObserve_project (s : State C K P F V) :
    m.constrainedConcrete.initSafe s ↔ m.constrainedReduced.initSafe (m.project s) := by
  change m.initObserve s.1 s.2.1 (m.observations s.2.2) ↔
    m.initObserve s.1 s.2.1 (m.observations (m.mask s.2.1 s.2.2))
  rw [m.observations_mask]

theorem constraint_project (s : State C K P F V) :
    m.constrainedConcrete.constraint s ↔ m.constrainedReduced.constraint (m.project s) := by
  change m.constraint s.1 s.2.1 (m.observations s.2.2) ↔
    m.constraint s.1 s.2.1 (m.observations (m.mask s.2.1 s.2.2))
  rw [m.observations_mask]

theorem constrained_certificate :
    ConstrainedCertificate m.constrainedConcrete m.constrainedReduced m.project :=
  constrainedOfProjectedAction m.certificate
    m.initObserve_project m.constraint_project m.actionConstraint_project m.actionObserve_project
end Model
end
end TlxOptimization.FieldRule
