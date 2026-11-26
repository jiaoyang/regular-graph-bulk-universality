import GeneralizedBulk.Spectral.PairedAngularLog

/-! Actual integrability and real-part extraction for the computed paired
logarithmic factors. -/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Spectral

theorem pairedLog_norm_bound (u : ℂ) (hu : ‖u‖ < 1) (theta : ℝ) :
    ‖pairedLog u theta‖ ≤ 2 * (‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2 + ‖u‖) := by
  have hA : ‖Complex.log (1 - u * circlePoint 1 theta)‖ ≤ ‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2 + ‖u‖ := by
    have hh := Complex.norm_log_one_add_le (z := -u * circlePoint 1 theta)
      (by simpa only [norm_mul, norm_neg, circlePoint_norm, abs_one, mul_one] using hu)
    simpa only [norm_mul, norm_neg, circlePoint_norm, abs_one, mul_one, neg_mul, sub_eq_add_neg] using hh
  have hB := Complex.norm_log_one_add_le (z := u * circlePoint 1 (-theta))
    (by simpa only [norm_mul, circlePoint_norm, abs_one, mul_one] using hu)
  simp only [norm_mul, circlePoint_norm, abs_one, mul_one] at hB
  exact (norm_add_le _ _).trans (by linarith)

theorem measurable_pairedLog (u : ℂ) : Measurable (pairedLog u) := by
  unfold pairedLog circlePoint
  fun_prop

theorem integrable_pairedLog (d : ℝ) (hd : 3 ≤ d) (u : ℂ) (hu : ‖u‖ < 1) :
    Integrable (pairedLog u) (angularLaw d) := by
  letI := angularLaw_isProbability d hd
  exact (integrable_const _).mono' (measurable_pairedLog u).aestronglyMeasurable
    (Filter.Eventually.of_forall (pairedLog_norm_bound u hu))

theorem integral_pairedLog_re (d : ℝ) (hd : 3 ≤ d) (u : ℂ) (hu : ‖u‖ < 1) :
    (∫ theta, (pairedLog u theta).re ∂angularLaw d) =
      -(d - 2) / 2 * Real.log ‖1 - logSeriesParameter d u‖ := by
  have hre : (∫ theta, (pairedLog u theta).re ∂angularLaw d) =
      (∫ theta, pairedLog u theta ∂angularLaw d).re := integral_re (integrable_pairedLog d hd u hu)
  rw [hre, integral_pairedLog d hd u hu]
  have hc : -((d - 2 : ℝ) : ℂ) / 2 = ((-(d - 2) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hc]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.log_re]

end GeneralizedBulk.KestenMcKay
