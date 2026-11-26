import Mathlib

/-! Almost-sure absolute convergence from summable expected norms. -/
noncomputable section
open MeasureTheory Filter ENNReal
open scoped ENNReal NNReal BigOperators

namespace GeneralizedBulk.Analysis

theorem ae_summable_norm_of_summable_integral_norm
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (F : ι → Ω → E)
    (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable (fun i => ∫ ω, ‖F i ω‖ ∂μ)) :
    ∀ᵐ ω ∂μ, Summable (fun i => ‖F i ω‖) := by
  have hmeas (i : ι) : AEMeasurable (fun ω => ‖F i ω‖ₑ) μ := (hF i).1.enorm
  have heq (i : ι) : (∫⁻ ω, ‖F i ω‖ₑ ∂μ) = ‖∫ ω, ‖F i ω‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF i).norm, coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun ω => norm_nonneg (F i ω)))]
    rfl
  have hfinite : (∑' i, ∫⁻ ω, ‖F i ω‖ₑ ∂μ) ≠ ∞ := by
    simp_rw [heq]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)
  rw [← lintegral_tsum hmeas] at hfinite
  refine (ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) hfinite).mono ?_
  intro ω hω
  change Summable (fun i => (‖F i ω‖₊ : ℝ))
  rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
  exact hω.ne

/-- Integrable marks with a uniform expected norm have almost-sure weighted
absolute summability whenever the deterministic particle weights are summable. -/
theorem ae_weighted_summable
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (F : ι → Ω → ℂ) (weight : ι → ℝ) (B : ℝ)
    (hF : ∀ i, Integrable (F i) μ)
    (hw : ∀ i, 0 ≤ weight i) (hs : Summable weight)
    (hbound : ∀ i, (∫ ω, ‖F i ω‖ ∂μ) ≤ B) :
    ∀ᵐ ω ∂μ, Summable (fun i => weight i * ‖F i ω‖) := by
  have hi (i : ι) : Integrable (fun ω => (weight i : ℂ) * F i ω) μ :=
    (hF i).const_mul _
  have hsum : Summable (fun i => ∫ ω, ‖(weight i : ℂ) * F i ω‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _)) _
      (hs.mul_right B)
    intro i
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i),
      integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hbound i) (hw i)
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _)] using
    ae_summable_norm_of_summable_integral_norm μ _ hi hsum

end GeneralizedBulk.Analysis
