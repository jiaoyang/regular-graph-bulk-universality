import Mathlib.Probability.ConditionalProbability
import Mathlib

/-! Actual probability laws on positive-mass measurable strata. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GeneralizedBulk.Analysis
variable {E : Type*} [MeasurableSpace E]

/-- Conditioning on a positive-mass stratum and pulling back its subtype
gives a genuine probability measure on that stratum. -/
def conditionalSubtypeLaw (ν : Measure E) [IsProbabilityMeasure ν]
    (s : Set E) (hs : MeasurableSet s) (hν : ν s ≠ 0) : ProbabilityMeasure s :=
  ⟨Measure.comap Subtype.val (ProbabilityTheory.cond ν s),⟨by
    rw [(MeasurableEmbedding.subtype_coe hs).comap_apply,Set.image_univ,Subtype.range_coe]
    exact ProbabilityTheory.cond_apply_self hν (measure_ne_top ν s)⟩⟩

theorem map_conditionalSubtypeLaw (ν : Measure E) [IsProbabilityMeasure ν]
    (s : Set E) (hs : MeasurableSet s) (hν : ν s ≠ 0) :
    Measure.map (Subtype.val : s → E) (conditionalSubtypeLaw ν s hs hν : Measure s) =
      ProbabilityTheory.cond ν s := by
  change Measure.map (Subtype.val : s → E) (Measure.comap Subtype.val (ProbabilityTheory.cond ν s)) = _
  rw [map_comap_subtype_coe hs]
  apply Measure.restrict_eq_self_of_ae_mem
  apply ae_iff.mpr
  change ProbabilityTheory.cond ν s sᶜ = 0
  rw [ProbabilityTheory.cond_apply hs ν sᶜ,Set.inter_compl_self,measure_empty,mul_zero]

/-- Multiplying a normalized stratum law by its original mass recovers the
literal restriction, so mixing strata does not alter the scalar marginal. -/
theorem mass_smul_map_conditionalSubtypeLaw (ν : Measure E) [IsProbabilityMeasure ν]
    (s : Set E) (hs : MeasurableSet s) (hν : ν s ≠ 0) :
    ν s • Measure.map (Subtype.val : s → E) (conditionalSubtypeLaw ν s hs hν : Measure s) =
      ν.restrict s := by
  rw [map_conditionalSubtypeLaw,ProbabilityTheory.cond,smul_smul,
    ENNReal.mul_inv_cancel hν (measure_ne_top ν s),one_smul]

/-- Integrability on the full scalar law gives actual integrability on each
positive-mass conditioned stratum. -/
theorem integrable_conditionalSubtypeLaw
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (s : Set E) (hs : MeasurableSet s) (hν : ν s ≠ 0)
    (f : E → V) (hf : Integrable f ν) :
    Integrable (fun x : s => f x.val) (conditionalSubtypeLaw ν s hs hν : Measure s) := by
  have hi : Integrable f (ProbabilityTheory.cond ν s) :=
    (hf.mono_measure ν.restrict_le_self).smul_measure (ENNReal.inv_ne_top.mpr hν)
  rw [← map_conditionalSubtypeLaw ν s hs hν] at hi
  exact (integrable_map_measure hi.aestronglyMeasurable measurable_subtype_coe.aemeasurable).mp hi


end GeneralizedBulk.Analysis
