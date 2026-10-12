import Rules

set_option autoImplicit false

/-
History-summary correctness for pragmatic/database-blob/working/working.tla.
The protocol below is a manual, typed formalization, not a verified TLA+ parser.
See README.md for the source/configuration identity and the remaining trust boundary.
-/
namespace Blob
open TlxOptimization

inductive User where | u1
  deriving DecidableEq
inductive Server where | s1 | s2
  deriving DecidableEq
inductive Metadata where | m1 | m2
  deriving DecidableEq
inductive Image where | i1 | i2
  deriving DecidableEq
inductive UUID where | ui1 | ui2
  deriving DecidableEq

inductive Kind where | read | write
  deriving DecidableEq

structure Operation where
  kind : Kind
  userId : Option User
  metadata : Option Metadata
  image : Option Image
  deriving DecidableEq

abbrev Log := History Operation

-- Zero-based occurrence positions correspond to TLA+'s indices minus one.
inductive At : Log → Nat → Operation → Prop
  | last (h : Log) (e : Operation) : At (.append h e) h.length e
  | earlier {h i e} (x : Operation) : At h i e → At (.append h x) i e

theorem at_bound {h i e} (a : At h i e) : i < h.length := by
  induction a with
  | last => simp [History.length]
  | earlier _ _ ih => simp only [History.length]; omega

theorem at_exists (h : Log) (i : Nat) (hi : i < h.length) : ∃ e, At h i e := by
  induction h with
  | empty => simp [History.length] at hi
  | append h x ih =>
    by_cases old : i < h.length
    · obtain ⟨e, he⟩ := ih old
      exact ⟨e, .earlier x he⟩
    · have eq : i = h.length := by simp only [History.length] at hi; omega
      subst i
      exact ⟨x, .last h x⟩

theorem at_unique {h i e f} (a : At h i e) (b : At h i f) : e = f := by
  induction a with
  | last h x =>
    cases b with
    | last => rfl
    | earlier _ b => have hb := at_bound b; omega
  | earlier x a ih =>
    cases b with
    | last => have ha := at_bound a; omega
    | earlier _ b => exact ih b

theorem seen_iff_at (h : Log) (e : Operation) :
    h.seen e ↔ ∃ i, At h i e := by
  induction h with
  | empty =>
    constructor
    · exact False.elim
    · rintro ⟨i, a⟩; cases a
  | append h x ih =>
    constructor
    · intro hs
      cases hs with
      | inl hs => obtain ⟨i, a⟩ := ih.mp hs; exact ⟨i, .earlier x a⟩
      | inr he => subst e; exact ⟨h.length, .last h x⟩
    · rintro ⟨i, a⟩
      cases a with
      | last => exact Or.inr rfl
      | earlier _ a => exact Or.inl (ih.mpr ⟨_, a⟩)

def seenPrefix (h : Log) (i : Nat) (e : Operation) : Prop :=
  ∃ j, j ≤ i ∧ At h j e

theorem prefix_old (h : Log) (x : Operation) (i : Nat) (hi : i < h.length) :
    seenPrefix (.append h x) i = seenPrefix h i := by
  funext e
  apply propext
  constructor
  · rintro ⟨j, hj, a⟩
    cases a with
    | last => omega
    | earlier _ a => exact ⟨j, hj, a⟩
  · rintro ⟨j, hj, a⟩
    exact ⟨j, hj, .earlier x a⟩

theorem prefix_last (h : Log) (x : Operation) :
    seenPrefix (.append h x) h.length = History.seen (.append h x) := by
  funext e
  apply propext
  constructor
  · rintro ⟨j, _, a⟩; exact (seen_iff_at _ _).mpr ⟨j, a⟩
  · intro hs
    obtain ⟨j, a⟩ := (seen_iff_at _ _).mp hs
    have hb := at_bound a
    exact ⟨j, by simp only [History.length] at hb; omega, a⟩

-- Exact ConsistentReads body: a matching WRITE in the inclusive prefix,
-- or an empty READ, or a WRITE. None is the source's "UNSET" value.
def eventOK (r : Operation) (seen : Operation → Prop) : Prop :=
  (r.kind = .read ∧
    ((∃ w, seen w ∧ w.kind = .write ∧ r.userId = w.userId ∧
      r.metadata = w.metadata ∧ r.image = w.image) ∨
     (r.metadata = none ∧ r.image = none))) ∨ r.kind = .write

def indexed (h : Log) : Prop :=
  ∀ i e, At h i e → eventOK e (seenPrefix h i)

def consistentReads (h : Log) : Prop := h = .empty ∨ indexed h

theorem indexed_append (h : Log) (x : Operation) :
    indexed (.append h x) ↔ indexed h ∧ eventOK x (History.seen (.append h x)) := by
  constructor
  · intro hp
    constructor
    · intro i e a
      have he := hp i e (.earlier x a)
      rw [prefix_old h x i (at_bound a)] at he
      exact he
    · have he := hp h.length x (.last h x)
      rw [prefix_last] at he
      exact he
  · rintro ⟨hp, hx⟩ i e a
    cases a with
    | last => simpa only [prefix_last] using hx
    | earlier _ a =>
      rw [prefix_old h x i (at_bound a)]
      exact hp i e a

theorem indexed_iff_valid (h : Log) : indexed h ↔ History.valid eventOK h := by
  induction h with
  | empty =>
    constructor
    · intro _; trivial
    · intro _ i e a; cases a
  | append h x ih =>
    rw [indexed_append, History.valid, ih]

theorem consistent_iff_valid (h : Log) :
    consistentReads h ↔ History.valid eventOK h := by
  constructor
  · rintro (he | hi)
    · subst h; trivial
    · exact (indexed_iff_valid h).mp hi
  · intro hv; exact Or.inr ((indexed_iff_valid h).mpr hv)

structure Summary where
  seen : Operation → Prop
  consistent : Prop

def summarize (h : Log) : Summary := ⟨h.seen, History.valid eventOK h⟩

def appendSummary (s : Summary) (e : Operation) : Summary :=
  let seen := fun x => s.seen x ∨ x = e
  ⟨seen, s.consistent ∧ eventOK e seen⟩

theorem append_commutes (h : Log) (e : Operation) :
    summarize (.append h e) = appendSummary (summarize h) e := rfl

-- The unchanged fields of the blob protocol are retained exactly.
inductive Phase where
  | waiting | startedWrite | wroteBlob | startedRead | readMetadata
  deriving DecidableEq

structure DatabaseRecord where
  metadata : Option Metadata
  imageId : Option UUID

structure ServerState where
  phase : Phase
  userId : Option User
  metadata : Option Metadata
  imageId : Option UUID
  image : Option Image

structure Core where
  database : User → DatabaseRecord
  blobs : UUID → Option Image
  servers : Server → ServerState

def update {K V : Type} [DecidableEq K] (f : K → V) (k : K) (v : V) : K → V :=
  fun j => if j = k then v else f j

def waiting : ServerState := ⟨.waiting, none, none, none, none⟩
def initialCore : Core := ⟨fun _ => ⟨none, none⟩, fun _ => none, fun _ => waiting⟩

-- Each constructor is one source action with its actual nondeterministic
-- parameters. The optional operation is its sole effect on the log.
inductive CoreStep : Core → Core → Option Operation → Prop
  | startWrite (c : Core) (s : Server) (u : User) (m : Metadata) (i : Image)
      (enabled : (c.servers s).phase = .waiting) :
      CoreStep c
        { c with
          servers := update c.servers s {
            (c.servers s) with
            phase := .startedWrite
            userId := some u
            metadata := some m
            image := some i } }
        (some ⟨.write, some u, some m, some i⟩)
  | writeBlob (c : Core) (s : Server) (id : UUID)
      (enabled : (c.servers s).phase = .startedWrite) (free : c.blobs id = none) :
      CoreStep c
        { c with
          blobs := update c.blobs id (c.servers s).image
          servers := update c.servers s { (c.servers s) with phase := .wroteBlob, imageId := some id } }
        none
  | writeMetadataAndReturn (c : Core) (s : Server) (u : User)
      (enabled : (c.servers s).phase = .wroteBlob) (user : (c.servers s).userId = some u) :
      CoreStep c
        { c with
          database := update c.database u ⟨(c.servers s).metadata, (c.servers s).imageId⟩
          servers := update c.servers s waiting } none
  | failWrite (c : Core) (s : Server)
      (enabled : (c.servers s).phase = .startedWrite ∨ (c.servers s).phase = .wroteBlob) :
      CoreStep c { c with servers := update c.servers s waiting } none
  | startRead (c : Core) (s : Server) (u : User)
      (enabled : (c.servers s).phase = .waiting) :
      CoreStep c
        { c with servers := update c.servers s { (c.servers s) with phase := .startedRead, userId := some u } }
        none
  | readMetadata (c : Core) (s : Server) (u : User)
      (enabled : (c.servers s).phase = .startedRead) (user : (c.servers s).userId = some u)
      (present : (c.database u).metadata ≠ none) :
      CoreStep c
        { c with
          servers := update c.servers s {
            (c.servers s) with
            phase := .readMetadata
            metadata := (c.database u).metadata
            imageId := (c.database u).imageId } } none
  | readMetadataAndReturnEmpty (c : Core) (s : Server) (u : User)
      (enabled : (c.servers s).phase = .startedRead) (user : (c.servers s).userId = some u)
      (absent : (c.database u).metadata = none) :
      CoreStep c { c with servers := update c.servers s waiting }
        (some ⟨.read, (c.servers s).userId, none, none⟩)
  | readBlobAndReturn (c : Core) (s : Server) (id : UUID)
      (enabled : (c.servers s).phase = .readMetadata) (image : (c.servers s).imageId = some id) :
      CoreStep c { c with servers := update c.servers s waiting }
        (some ⟨.read, (c.servers s).userId, (c.servers s).metadata, c.blobs id⟩)

-- The source's partial function lookups are defined in every reachable core.
-- The extra 'some' witnesses in CoreStep do not discard reachable actions.
def serverWF (s : ServerState) : Prop :=
  (s.phase ≠ .waiting → s.userId ≠ none) ∧
  ((s.phase = .wroteBlob ∨ s.phase = .readMetadata) → s.imageId ≠ none)

def coreWF (c : Core) : Prop :=
  (∀ s, serverWF (c.servers s)) ∧
  (∀ u, (c.database u).metadata ≠ none → (c.database u).imageId ≠ none)

theorem all_update {K V : Type} [DecidableEq K] (p : V → Prop)
    (f : K → V) (hf : ∀ k, p (f k)) (k : K) (v : V) (hv : p v) :
    ∀ j, p (update f k v j) := by
  intro j
  by_cases hj : j = k
  · simpa [update, hj] using hv
  · simpa [update, hj] using hf j

theorem waiting_wf : serverWF waiting := by simp [serverWF, waiting]

theorem initial_wf : coreWF initialCore := by
  simp [coreWF, initialCore, serverWF, waiting]

theorem core_step_wf {c d e} (hc : coreWF c) (h : CoreStep c d e) : coreWF d := by
  cases h with
  | startWrite s u m i enabled =>
    exact ⟨all_update serverWF _ hc.1 s _ (by simp [serverWF]), hc.2⟩
  | writeBlob s id enabled free =>
    refine ⟨all_update serverWF _ hc.1 s _ ?_, hc.2⟩
    constructor
    · intro _; exact (hc.1 s).1 (by simp [enabled])
    · intro _; simp
  | writeMetadataAndReturn s u enabled user =>
    refine ⟨all_update serverWF _ hc.1 s waiting waiting_wf,
      all_update (fun r : DatabaseRecord => r.metadata ≠ none → r.imageId ≠ none)
        _ hc.2 u _ ?_⟩
    intro _
    exact (hc.1 s).2 (Or.inl enabled)
  | failWrite s enabled =>
    exact ⟨all_update serverWF _ hc.1 s waiting waiting_wf, hc.2⟩
  | startRead s u enabled =>
    exact ⟨all_update serverWF _ hc.1 s _ (by simp [serverWF]), hc.2⟩
  | readMetadata s u enabled user present =>
    refine ⟨all_update serverWF _ hc.1 s _ ?_, hc.2⟩
    constructor
    · intro _; simp [user]
    · intro _; exact hc.2 u present
  | readMetadataAndReturnEmpty s u enabled user absent =>
    exact ⟨all_update serverWF _ hc.1 s waiting waiting_wf, hc.2⟩
  | readBlobAndReturn s id enabled image =>
    exact ⟨all_update serverWF _ hc.1 s waiting waiting_wf, hc.2⟩

theorem user_lookup_defined {c : Core} (hc : coreWF c) (s : Server)
    (active : (c.servers s).phase ≠ .waiting) :
    ∃ u, (c.servers s).userId = some u := by
  cases hu : (c.servers s).userId with
  | none => exact False.elim ((hc.1 s).1 active hu)
  | some u => exact ⟨u, rfl⟩

theorem image_lookup_defined {c : Core} (hc : coreWF c) (s : Server)
    (reading : (c.servers s).phase = .readMetadata) :
    ∃ id, (c.servers s).imageId = some id := by
  cases hi : (c.servers s).imageId with
  | none => exact False.elim ((hc.1 s).2 (Or.inr reading) hi)
  | some id => exact ⟨id, rfl⟩

def advanceLog (h : Log) : Option Operation → Log
  | none => h
  | some e => .append h e

def advanceSummary (s : Summary) : Option Operation → Summary
  | none => s
  | some e => appendSummary s e

theorem advance_commutes (h : Log) (e : Option Operation) :
    summarize (advanceLog h e) = advanceSummary (summarize h) e := by
  cases e <;> rfl

abbrev Concrete := Core × Log
abbrev Reduced := Core × Summary

def project (s : Concrete) : Reduced := (s.1, summarize s.2)

def concrete : System Concrete where
  initial s := s = (initialCore, .empty)
  next s t := ∃ e, CoreStep s.1 t.1 e ∧ t.2 = advanceLog s.2 e
  safe s := consistentReads s.2

def reduced : System Reduced where
  initial s := s = (initialCore, summarize .empty)
  next s t := ∃ e, CoreStep s.1 t.1 e ∧ t.2 = advanceSummary s.2 e
  safe s := s.2.consistent

theorem reachable_core_wf {s : Concrete} (h : Reachable concrete s) : coreWF s.1 := by
  induction h with
  | initial hi =>
    change _ = (initialCore, History.empty) at hi
    cases hi
    exact initial_wf
  | step _ hn ih =>
    obtain ⟨e, hc, _⟩ := hn
    exact core_step_wf ih hc

-- This is an actual certificate term, not an assumed certificate parameter.
theorem certificate : Certificate concrete reduced project := by
  constructor
  · intro a
    constructor
    · intro ha
      exact ⟨(initialCore, .empty), rfl, ha.symm⟩
    · rintro ⟨s, hs, he⟩
      change s = (initialCore, .empty) at hs
      subst s
      exact he.symm
  · intro s a
    constructor
    · rintro ⟨e, hc, ha⟩
      refine ⟨(a.1, advanceLog s.2 e), ⟨e, hc, rfl⟩, ?_⟩
      apply Prod.ext
      · rfl
      · exact (advance_commutes s.2 e).trans ha.symm
    · rintro ⟨t, ⟨e, hc, ht⟩, he⟩
      subst a
      refine ⟨e, hc, ?_⟩
      change summarize t.2 = advanceSummary (summarize s.2) e
      rw [ht, advance_commutes]
  · intro s
    exact consistent_iff_valid s.2

theorem optimization_correct :
    (∀ s, Reachable concrete s → consistentReads s.2) ↔
    (∀ a, Reachable reduced a → a.2.consistent) := safety_iff certificate

theorem specification_correct :
    (∀ s, Reachable (withStuttering concrete) s → consistentReads s.2) ↔
    (∀ a, Reachable (withStuttering reduced) a → a.2.consistent) := by
  simpa only [stuttering_reachable_iff] using optimization_correct

-- Every reduced reachable state has a concrete reachable representative,
-- including a representative with the same failing invariant verdict.
theorem counterexample_lifts {a} (ha : Reachable reduced a) (bad : ¬ a.2.consistent) :
    ∃ s, Reachable concrete s ∧ project s = a ∧ ¬ consistentReads s.2 := by
  obtain ⟨s, hs, he⟩ := reachable_backward certificate ha
  refine ⟨s, hs, he, ?_⟩
  intro good
  have hg := (consistent_iff_valid s.2).mp good
  apply bad
  rw [← he]
  exact hg

theorem deadlock_preserved (s : Concrete) :
    (¬ ∃ t, concrete.next s t) ↔ (¬ ∃ a, reduced.next (project s) a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    obtain ⟨t, ht, _⟩ := (certificate.next s a).mp ha
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨project t, (certificate.next s (project t)).mpr ⟨t, ht, rfl⟩⟩

#print axioms optimization_correct
#print axioms specification_correct
#print axioms counterexample_lifts
#print axioms deadlock_preserved
#print axioms reachable_core_wf
end Blob
