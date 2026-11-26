import Mathlib

/-! Integration formulas for nonnegative real densities, including integrability. -/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.Analysis
variable {X : Type*} [MeasurableSpace X]

theorem integrable_realDensity_iff (μ : Measure X) (f g : X → ℝ)
    (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x) :
    Integrable g (μ.withDensity (fun x => ENNReal.ofReal (f x))) ↔
      Integrable (fun x => f x * g x) μ := by
  simpa only [ENNReal.toReal_ofReal (hpos _), smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
      (ae_of_all μ (fun _ => ENNReal.ofReal_lt_top)) (g := g))

theorem integral_realDensity (μ : Measure X) (f g : X → ℝ)
    (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x) :
    (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) =
      ∫ x, f x * g x ∂μ := by
  simpa only [ENNReal.toReal_ofReal (hpos _), smul_eq_mul] using
    integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
      (ae_of_all μ (fun _ => ENNReal.ofReal_lt_top)) g

end GeneralizedBulk.Analysis
