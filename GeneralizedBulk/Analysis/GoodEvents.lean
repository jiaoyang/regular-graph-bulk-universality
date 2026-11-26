import GeneralizedBulk.ExternalInputs

/-! Polynomial exceptional-event bounds imply vanishing real probabilities. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.External

 theorem PolynomialGoodEvents.failure_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ → ℕ} (H : PolynomialGoodEvents P N) (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => P.real (H.good n)ᶜ) atTop (𝓝 0) := by
  have hpow := (tendsto_rpow_neg_atTop H.exponent_pos).comp (tendsto_natCast_atTop_atTop.comp hN)
  have hr := hpow.const_mul H.constant
  have hb : ∀ᶠ n in atTop, P.real (H.good n)ᶜ ≤ H.constant * (N n : ℝ) ^ (-H.exponent) := by
    filter_upwards [eventually_ge_atTop H.threshold] with n hn
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (H.failure_bound n hn)
    simpa only [measureReal_def, ENNReal.toReal_ofReal (mul_nonneg H.constant_pos.le
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))] using h
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => measureReal_nonneg)) hb
  simpa only [mul_zero] using hr

end GeneralizedBulk.External
