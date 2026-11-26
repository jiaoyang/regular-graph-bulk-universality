import GeneralizedBulk.Counting.GlobalOccurrences
import BourgadeHuang.CountingLawSubsequence

/-!
# Canonical fixed-index presentation of infinite anchored laws

Every infinite locally finite counting state receives a measurable Nat list
of actual occurrences. Laws carried by such states are pulled back to the
measurable subtype, so no arbitrary null-set particle list is required.
-/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped Topology ENNReal
namespace GeneralizedBulk.Counting
open Gaussian

abbrev InfiniteAnchoredState := {s : AnchoredCountingState // s.val.1.measure Set.univ = ∞}

def infiniteCountingState (s : InfiniteAnchoredState) : InfiniteCountingMeasure :=
  ⟨s.val.val.1,s.property⟩

theorem measurable_infiniteCountingState : Measurable infiniteCountingState :=
  (measurable_fst.comp (measurable_subtype_coe.comp measurable_subtype_coe)).subtype_mk

/-- A canonical fixed Nat presentation of every actual infinite counting state. -/
def canonicalPresentation (s : InfiniteAnchoredState) : PresentedState ℕ :=
  ⟨(s.val,globalOccurrence (infiniteCountingState s)),
    measure_eq_sum_global_occurrences (infiniteCountingState s)⟩

@[simp] theorem canonicalPresentation_scalar (s : InfiniteAnchoredState) :
    (canonicalPresentation s).scalar = s.val := rfl

@[simp] theorem canonicalPresentation_location (s : InfiniteAnchoredState) (n : ℕ) :
    (canonicalPresentation s).location n = globalOccurrence (infiniteCountingState s) n := rfl

/-- Measurability of the full presentation is proved coordinatewise from
unit-cell counts and their sorted occurrence CDFs. -/
theorem measurable_canonicalPresentation : Measurable canonicalPresentation := by
  apply Measurable.subtype_mk
  apply measurable_subtype_coe.prodMk
  exact measurable_pi_lambda _ (fun n => (measurable_globalOccurrence n).comp measurable_infiniteCountingState)

theorem measurableSet_infiniteAnchoredState :
    MeasurableSet {s : AnchoredCountingState | s.val.1.measure Set.univ = ∞} :=
  ((LocalCountingMeasure.measurable_mass MeasurableSet.univ).comp
    (measurable_fst.comp measurable_subtype_coe)) (measurableSet_singleton ∞)

theorem infiniteAnchoredState_range_compl_null
    (ν : ProbabilityMeasure AnchoredCountingState)
    (hmass : ∀ᵐ s ∂(ν : Measure AnchoredCountingState), s.val.1.measure Set.univ = ∞) :
    (ν : Measure AnchoredCountingState)
      (Set.range (Subtype.val : InfiniteAnchoredState → AnchoredCountingState))ᶜ = 0 := by
  have heq : Set.range (Subtype.val : InfiniteAnchoredState → AnchoredCountingState) =
      {s : AnchoredCountingState | s.val.1.measure Set.univ = ∞} := by ext s; simp
  rw [heq]
  exact ae_iff.mp hmass

/-- The actual limiting scalar law restricted to its probability-one infinite
particle subtype. -/
def infiniteAnchoredLaw (ν : ProbabilityMeasure AnchoredCountingState)
    (hmass : ∀ᵐ s ∂(ν : Measure AnchoredCountingState), s.val.1.measure Set.univ = ∞) :
    ProbabilityMeasure InfiniteAnchoredState :=
  embeddingPullbackLaw (MeasurableEmbedding.subtype_coe measurableSet_infiniteAnchoredState)
    ν (infiniteAnchoredState_range_compl_null ν hmass)

/-- Forgetting the subtype recovers the exact original scalar law. -/
theorem map_infiniteAnchoredLaw (ν : ProbabilityMeasure AnchoredCountingState)
    (hmass : ∀ᵐ s ∂(ν : Measure AnchoredCountingState), s.val.1.measure Set.univ = ∞) :
    Measure.map (Subtype.val : InfiniteAnchoredState → AnchoredCountingState)
      (infiniteAnchoredLaw ν hmass : Measure InfiniteAnchoredState) = ν := by
  have h := map_embeddingPullbackLaw
    (MeasurableEmbedding.subtype_coe measurableSet_infiniteAnchoredState)
    ν (infiniteAnchoredState_range_compl_null ν hmass)
  exact congrArg (fun mu : ProbabilityMeasure AnchoredCountingState => (mu : Measure AnchoredCountingState)) h

/-- The constructed canonical presentation has exactly the prescribed scalar
law, so it can feed the existing Gaussian marked criterion without a separate
measurable-enumeration hypothesis. -/
theorem canonicalPresentation_scalar_law (ν : ProbabilityMeasure AnchoredCountingState)
    (hmass : ∀ᵐ s ∂(ν : Measure AnchoredCountingState), s.val.1.measure Set.univ = ∞) :
    Measure.map (fun s => (canonicalPresentation s).scalar)
      (infiniteAnchoredLaw ν hmass : Measure InfiniteAnchoredState) = ν :=
  map_infiniteAnchoredLaw ν hmass

end GeneralizedBulk.Counting
