/- Synchronous age/history reduction. Both transfers share the retained core
and branch witness. No transfer can inspect the forgotten history or time. -/
set_option autoImplicit false
namespace TlxOptimization.AgeHistoryRule
open TlxOptimization AgeRule

structure Model (C K E I W : Type) where
  age : AgeRule.Model C K W
  predicate : I → E → (E → Prop) → Prop
  historySeed : C → W → History E
  historyTransfer : C → C → W → (K → Bool) → HistoryRule.Summary E I → HistoryRule.Transfer E
  guard : C → C → W → (K → Bool) → HistoryRule.Summary E I → Test age.caps
  observe : C → (K → Bool) → HistoryRule.Summary E I → Test age.caps

namespace Model
variable {C K E I W : Type} (m : Model C K E I W)

def project (s : State C K × History E) : Abstract C K × HistoryRule.Summary E I :=
  (m.age.project s.1, History.summary m.predicate s.2)
def seedState (c : C) (w : W) : State C K × History E :=
  (m.age.seedState c w, m.historySeed c w)
def seedAbstract (c : C) (w : W) : Abstract C K × HistoryRule.Summary E I :=
  (m.age.seedAbstract c w, History.summary m.predicate (m.historySeed c w))
def advanceState (s : State C K × History E) (d : C) (w : W) : State C K × History E :=
  (m.age.advanceState s.1 d w,
   (m.historyTransfer s.1.core d w (presence s.1.stamps) (HistoryRule.indexedSummary m.predicate s.2)).concrete s.2)
def advanceAbstract (s : Abstract C K × HistoryRule.Summary E I) (d : C) (w : W) :
    Abstract C K × HistoryRule.Summary E I :=
  (m.age.advanceAbstract s.1 d w,
   (m.historyTransfer s.1.1 d w (presence s.1.2) s.2).reduced m.predicate s.2)

theorem seed_commutes (c : C) (w : W) : m.project (m.seedState c w) = m.seedAbstract c w := by
  exact Prod.ext (m.age.seed_commutes c w) rfl

theorem advance_commutes (s : State C K × History E) (d : C) (w : W) :
    m.project (m.advanceState s d w) = m.advanceAbstract (m.project s) d w := by
  apply Prod.ext
  · exact m.age.advance_commutes s.1 d w
  · change History.summary m.predicate ((m.historyTransfer s.1.core d w (presence s.1.stamps) (HistoryRule.indexedSummary m.predicate s.2)).concrete s.2) = _
    rw [HistoryRule.Transfer.commutes]
    simp only [advanceAbstract, project, AgeRule.Model.project, presence_summary, HistoryRule.indexedSummary_eq]

def concrete : System (State C K × History E) where
  initial s := ∃ c w, m.age.initial c w ∧ s = m.seedState c w
  next s t := ∃ w, (m.guard s.1.core t.1.core w (presence s.1.stamps) (HistoryRule.indexedSummary m.predicate s.2)).concrete s.1.now s.1.stamps ∧
    t = m.advanceState s t.1.core w
  safe s := (m.observe s.1.core (presence s.1.stamps) (HistoryRule.indexedSummary m.predicate s.2)).concrete s.1.now s.1.stamps

def reduced : System (Abstract C K × HistoryRule.Summary E I) where
  initial s := ∃ c w, m.age.initial c w ∧ s = m.seedAbstract c w
  next s t := ∃ w, (m.guard s.1.1 t.1.1 w (presence s.1.2) s.2).reduced s.1.2 ∧ t = m.advanceAbstract s t.1.1 w
  safe s := (m.observe s.1.1 (presence s.1.2) s.2).reduced s.1.2

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
      have hc : (m.guard s.1.core a.1.1 w (presence s.1.stamps) (HistoryRule.indexedSummary m.predicate s.2)).concrete s.1.now s.1.stamps := by
        rw [HistoryRule.indexedSummary_eq]
        apply (Test.commutes _ _ _).mpr
        simpa only [project, AgeRule.Model.project, presence_summary, HistoryRule.indexedSummary_eq] using hg
      refine ⟨m.advanceState s a.1.1 w, ⟨w, hc, rfl⟩, ?_⟩
      exact (m.advance_commutes s a.1.1 w).trans ha.symm
    · rintro ⟨t, ⟨w, hg, ht⟩, rfl⟩
      refine ⟨w, ?_, ?_⟩
      · simpa only [project, AgeRule.Model.project, presence_summary, HistoryRule.indexedSummary_eq] using (Test.commutes _ _ _).mp hg
      · exact (congrArg m.project ht).trans (m.advance_commutes s t.1.core w)
  · intro s
    change _ ↔ (m.observe s.1.core (presence (summarize m.age.caps s.1.now s.1.stamps)) (History.summary m.predicate s.2)).reduced _
    rw [presence_summary]
    change (m.observe _ _ (HistoryRule.indexedSummary _ _)).concrete _ _ ↔ _
    rw [HistoryRule.indexedSummary_eq]
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

theorem deadlock_preserved (s : State C K × History E) :
    (¬ ∃ t, m.concrete.next s t) ↔ (¬ ∃ a, m.reduced.next (m.project s) a) := by
  constructor
  · intro noStep ⟨a, ha⟩
    obtain ⟨t, ht, _⟩ := (m.certificate.next s a).mp ha
    exact noStep ⟨t, ht⟩
  · intro noStep ⟨t, ht⟩
    exact noStep ⟨m.project t, (m.certificate.next s (m.project t)).mpr ⟨t, ht, rfl⟩⟩
end Model
end TlxOptimization.AgeHistoryRule
