/- Relative-age rule semantics. Retained payloads and timestamp presence stay
exact; only absolute time and ages above an observed threshold are forgotten. -/
set_option autoImplicit false
namespace TlxOptimization.AgeRule
open TlxOptimization

inductive Change where
  | keep | reset | erase

-- Compose a field-only reset after earlier EXCEPT updates. Missing fields
-- stay missing; an earlier whole-record erase must not be undone.
def Change.refresh : Change → Bool → Change
  | .keep, present => if present then .reset else .keep
  | .reset, _ => .reset
  | .erase, _ => .erase

abbrev Stamps (K : Type) (now : Nat) := K → Option {n : Nat // n ≤ now}
abbrev Ages (K : Type) := K → Option Nat

def summarize {K : Type} (caps : K → Nat) (now : Nat) (h : Stamps K now) : Ages K :=
  fun k => (h k).map (fun n => min (now - n.val) (caps k))

def presence {K V : Type} (h : K → Option V) : K → Bool := fun k => (h k).isSome

theorem presence_summary {K : Type} (caps : K → Nat) (now : Nat) (h : Stamps K now) :
    presence (summarize caps now h) = presence h := by
  funext k; simp [presence, summarize]

def updateStamp (now delta : Nat) : Change → Option {n : Nat // n ≤ now} →
    Option {n : Nat // n ≤ now + delta}
  | .keep, s => s.map (fun n => ⟨n.val, Nat.le_trans n.property (Nat.le_add_right _ _)⟩)
  | .reset, _ => some ⟨now + delta, Nat.le_refl _⟩
  | .erase, _ => none

def updateAge (cap delta : Nat) : Change → Option Nat → Option Nat
  | .keep, a => a.map (fun n => min (n + delta) cap)
  | .reset, _ => some 0
  | .erase, _ => none

theorem update_commutes (now delta cap : Nat) (change : Change)
    (stamp : Option {n : Nat // n ≤ now}) :
    (updateStamp now delta change stamp).map (fun n => min (now + delta - n.val) cap) =
      updateAge cap delta change (stamp.map (fun n => min (now - n.val) cap)) := by
  cases change with
  | erase => rfl
  | reset => simp [updateStamp, updateAge]
  | keep =>
    cases stamp with
    | none => rfl
    | some n =>
      simp only [updateStamp, updateAge, Option.map_some, Option.some.injEq]
      have past := n.property
      omega

inductive Test {K : Type} (caps : K → Nat) where
  | pure (p : Prop)
  | atLeast (key : K) (delay : Nat) (within : delay ≤ caps key)
  | neg (p : Test caps)
  | conj (p q : Test caps)
  | disj (p q : Test caps)
  | bind (p : Test caps) (next : Bool → Test caps)

def Test.concrete {K : Type} {caps : K → Nat} (now : Nat) (h : Stamps K now) : Test caps → Prop
  | .pure p => p
  | .atLeast k d _ => ∃ n, h k = some n ∧ n.val + d ≤ now
  | .neg p => ¬ p.concrete now h
  | .conj p q => p.concrete now h ∧ q.concrete now h
  | .disj p q => p.concrete now h ∨ q.concrete now h
  | .bind p next => ∃ b : Bool, (b = true ↔ p.concrete now h) ∧ (next b).concrete now h

def Test.reduced {K : Type} {caps : K → Nat} (h : Ages K) : Test caps → Prop
  | .pure p => p
  | .atLeast k d _ => ∃ n, h k = some n ∧ d ≤ n
  | .neg p => ¬ p.reduced h
  | .conj p q => p.reduced h ∧ q.reduced h
  | .disj p q => p.reduced h ∨ q.reduced h
  | .bind p next => ∃ b : Bool, (b = true ↔ p.reduced h) ∧ (next b).reduced h

theorem Test.commutes {K : Type} {caps : K → Nat} (p : Test caps) (now : Nat) (h : Stamps K now) :
    p.concrete now h ↔ p.reduced (summarize caps now h) := by
  induction p with
  | pure => rfl
  | atLeast k d within =>
    cases hk : h k with
    | none => simp [Test.concrete, Test.reduced, summarize, hk]
    | some n =>
      simp only [Test.concrete, Test.reduced, summarize, hk, Option.map_some,
        Option.some.injEq]
      have past := n.property
      constructor
      · rintro ⟨x, hx, hd⟩
        subst x
        exact ⟨_, rfl, by omega⟩
      · rintro ⟨x, hx, hd⟩
        subst x
        exact ⟨n, rfl, by omega⟩
  | neg p ih => simp only [Test.concrete, Test.reduced, ih]
  | conj p q ih₁ ih₂ => simp only [Test.concrete, Test.reduced, ih₁, ih₂]
  | disj p q ih₁ ih₂ => simp only [Test.concrete, Test.reduced, ih₁, ih₂]
  | bind p next ih ihNext => simp only [Test.concrete, Test.reduced, ih, ihNext]

-- Explicit finite filtering. The continuation receives the selected source
-- positions, so an arbitrary retained consumer sees the same exact set.
def Test.select {K I : Type} {caps : K → Nat} (keys : List I)
    (predicate : I → Test caps) (consume : List I → Test caps) : Test caps :=
  match keys with
  | [] => consume []
  | k :: ks => .bind (predicate k) (fun b =>
      Test.select ks predicate (fun selected => consume (if b then k :: selected else selected)))

theorem Test.select_concrete {K I : Type} {caps : K → Nat} (keys : List I)
    (predicate : I → Test caps) (consume : List I → Test caps) (now : Nat) (h : Stamps K now) :
    (Test.select keys predicate consume).concrete now h ↔
      (consume (keys.filter (fun k => @decide ((predicate k).concrete now h) (Classical.propDecidable _)))).concrete now h := by
  induction keys generalizing consume with
  | nil => rfl
  | cons k ks ih =>
    simp only [Test.select, Test.concrete, ih]
    classical
    by_cases hp : (predicate k).concrete now h <;> simp [hp]

theorem Test.select_reduced {K I : Type} {caps : K → Nat} (keys : List I)
    (predicate : I → Test caps) (consume : List I → Test caps) (h : Ages K) :
    (Test.select keys predicate consume).reduced h ↔
      (consume (keys.filter (fun k => @decide ((predicate k).reduced h) (Classical.propDecidable _)))).reduced h := by
  induction keys generalizing consume with
  | nil => rfl
  | cons k ks ih =>
    simp only [Test.select, Test.reduced, ih]
    classical
    by_cases hp : (predicate k).reduced h <;> simp [hp]

structure State (C K : Type) where
  core : C
  now : Nat
  stamps : Stamps K now

abbrev Abstract (C K : Type) := C × Ages K

structure Model (C K W : Type) where
  caps : K → Nat
  initial : C → W → Prop
  seed : C → W → K → Bool
  delta : W → Nat
  guard : C → C → W → (K → Bool) → Test caps
  change : C → C → W → (K → Bool) → K → Change
  observe : C → (K → Bool) → Test caps

namespace Model
variable {C K W : Type} (m : Model C K W)

def project (s : State C K) : Abstract C K := (s.core, summarize m.caps s.now s.stamps)
def seedState (c : C) (w : W) : State C K :=
  ⟨c, 0, fun k => if m.seed c w k then some ⟨0, Nat.le_refl _⟩ else none⟩
def seedAbstract (c : C) (w : W) : Abstract C K :=
  (c, fun k => if m.seed c w k then some 0 else none)
def advanceState (s : State C K) (d : C) (w : W) : State C K :=
  ⟨d, s.now + m.delta w, fun k =>
    updateStamp s.now (m.delta w) (m.change s.core d w (presence s.stamps) k) (s.stamps k)⟩
def advanceAbstract (s : Abstract C K) (d : C) (w : W) : Abstract C K :=
  (d, fun k => updateAge (m.caps k) (m.delta w) (m.change s.1 d w (presence s.2) k) (s.2 k))

theorem seed_commutes (c : C) (w : W) : m.project (m.seedState c w) = m.seedAbstract c w := by
  unfold project seedState seedAbstract
  apply congrArg (fun ages => (c, ages))
  funext k
  simp only [summarize]
  split <;> simp

theorem advance_commutes (s : State C K) (d : C) (w : W) :
    m.project (m.advanceState s d w) = m.advanceAbstract (m.project s) d w := by
  unfold project advanceState advanceAbstract
  simp only [presence_summary]
  apply congrArg (fun ages => (d, ages))
  funext k
  simp only [summarize]
  exact update_commutes _ _ _ _ _

def concrete : System (State C K) where
  initial s := ∃ c w, m.initial c w ∧ s = m.seedState c w
  next s t := ∃ w, (m.guard s.core t.core w (presence s.stamps)).concrete s.now s.stamps ∧
    t = m.advanceState s t.core w
  safe s := (m.observe s.core (presence s.stamps)).concrete s.now s.stamps

def reduced : System (Abstract C K) where
  initial s := ∃ c w, m.initial c w ∧ s = m.seedAbstract c w
  next s t := ∃ w, (m.guard s.1 t.1 w (presence s.2)).reduced s.2 ∧ t = m.advanceAbstract s t.1 w
  safe s := (m.observe s.1 (presence s.2)).reduced s.2

theorem certificate : Certificate m.concrete m.reduced m.project := by
  constructor
  · intro a
    constructor
    · rintro ⟨c, w, hi, rfl⟩
      exact ⟨m.seedState c w, ⟨c, w, hi, rfl⟩, m.seed_commutes c w⟩
    · rintro ⟨s, ⟨c, w, hi, rfl⟩, rfl⟩
      exact ⟨c, w, hi, m.seed_commutes c w⟩
  · intro s a
    constructor
    · rintro ⟨w, hg, ha⟩
      have hc : (m.guard s.core a.1 w (presence s.stamps)).concrete s.now s.stamps := by
        apply (Test.commutes _ _ _).mpr
        simpa only [project, presence_summary] using hg
      refine ⟨m.advanceState s a.1 w, ⟨w, hc, rfl⟩, ?_⟩
      exact (m.advance_commutes s a.1 w).trans ha.symm
    · rintro ⟨t, ⟨w, hg, ht⟩, rfl⟩
      refine ⟨w, ?_, ?_⟩
      · simpa only [project, presence_summary] using (Test.commutes _ _ _).mp hg
      · exact (congrArg m.project ht).trans (m.advance_commutes s t.core w)
  · intro s
    change _ ↔ (m.observe s.core (presence (summarize m.caps s.now s.stamps))).reduced _
    rw [presence_summary]
    exact Test.commutes _ _ _

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

theorem deadlock_preserved (s : State C K) :
    (¬ ∃ t, m.concrete.next s t) ↔ (¬ ∃ a, m.reduced.next (m.project s) a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s a).mp ha
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨m.project t, (m.certificate.next s (m.project t)).mpr ⟨t, ht, rfl⟩⟩
end Model
end TlxOptimization.AgeRule
