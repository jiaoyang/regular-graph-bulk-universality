import GeneralizedBulk.Spectral.KestenMcKayQuantile
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The quantile CDF and regularized potentials are integrals against the
actual Kesten–McKay probability law. -/
noncomputable section
open Set MeasureTheory
namespace GeneralizedBulk.KestenMcKay

theorem integral_law (d : ℝ) (hd : 3 ≤ d) (f : ℝ → ℝ) :
    (∫ x, f x ∂law d) = ∫ x in -radius d..radius d, f x * rawDensity d x := by
  rw [law, integral_withDensity_eq_integral_toReal_smul
    (measurable_rawDensity d).ennreal_ofReal (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [intervalIntegral.integral_of_le (by linarith [radius_pos d hd]), ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [ENNReal.toReal_ofReal (rawDensity_nonneg d hd hx), smul_eq_mul, mul_comm]

/-- The analytic CDF used to construct quantiles is exactly the actual
probability mass of the lower interval. -/
theorem law_Iic (d : ℝ) (hd : 3 ≤ d) {x : ℝ} (hx : x ∈ Icc (-radius d) (radius d)) :
    law d (Iic x) = ENNReal.ofReal (cdf d x) := by
  rw [law, withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic x ∩ Icc (-radius d) (radius d) = Icc (-radius d) x := by
    ext t
    constructor
    · rintro ⟨ht, ha, hb⟩
      exact ⟨ha, ht⟩
    · rintro ⟨ha, ht⟩
      exact ⟨ht, ha, ht.trans hx.2⟩
  rw [hset]
  have hi : IntegrableOn (rawDensity d) (Icc (-radius d) x) volume :=
    (continuousOn_rawDensity d hd).mono (Icc_subset_Icc le_rfl hx.2) |>.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    ((ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ (fun t ht =>
      rawDensity_nonneg d hd ⟨ht.1, ht.2.trans hx.2⟩))), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hx.1]
  rfl

theorem law_Iic_quantile (d : ℝ) (hd : 3 ≤ d) (u : Icc (0 : ℝ) 1) :
    law d (Iic (quantile d hd u)) = ENNReal.ofReal u.val := by
  rw [law_Iic d hd (quantile_mem d hd u), cdf_quantile]

end GeneralizedBulk.KestenMcKay
