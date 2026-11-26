import Mathlib

/-! Integration against actual measure-preserving observation maps. -/
noncomputable section
open MeasureTheory

namespace GeneralizedBulk.Analysis
variable {S T E : Type*} [MeasurableSpace S] [MeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_comp_measurePreserving {μ : Measure S} {ν : Measure T} {f : S → T}
    (hf : MeasurePreserving f μ ν) (g : T → E) (hg : AEStronglyMeasurable g ν) :
    (∫ x, g (f x) ∂μ) = ∫ y, g y ∂ν := by
  have hm : AEStronglyMeasurable g (Measure.map f μ) := by rw [hf.map_eq]; exact hg
  have h := integral_map hf.measurable.aemeasurable hm
  rw [hf.map_eq] at h
  exact h.symm

theorem lp_two_norm_sq_of_ae {μ : Measure S} (f : Lp ℝ 2 μ) (g : S → ℝ)
    (hg : (f : S → ℝ) =ᵐ[μ] g) : ‖f‖ ^ 2 = ∫ x, (g x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

end GeneralizedBulk.Analysis
