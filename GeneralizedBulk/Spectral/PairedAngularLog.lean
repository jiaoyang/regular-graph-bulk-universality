import GeneralizedBulk.Spectral.PairedAngularPowers

/-! Integration of the two genuine complex logarithmic factors, using their
actual Taylor series and exact Kesten–McKay paired-power expectations. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
namespace GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Spectral

def pairedLog (u : ℂ) (theta : ℝ) : ℂ :=
  Complex.log (1 - u * circlePoint 1 theta) + Complex.log (1 + u * circlePoint 1 (-theta))

theorem pairedPower_div_hasSum (u : ℂ) (hu : ‖u‖ < 1) (theta : ℝ) :
    HasSum (fun n : ℕ => pairedPower u n theta / (n : ℂ)) (-pairedLog u theta) := by
  have hsmall : ∀ t : ℝ, ‖u * circlePoint 1 t‖ < 1 := by
    intro t; simpa only [norm_mul, circlePoint_norm, abs_one, mul_one] using hu
  have hneg : ‖-u * circlePoint 1 (-theta)‖ < 1 := by
    simpa only [norm_mul, norm_neg, circlePoint_norm, abs_one, mul_one] using hu
  have hh := (Complex.hasSum_taylorSeries_neg_log (hsmall theta)).add
    (Complex.hasSum_taylorSeries_neg_log hneg)
  convert hh using 1
  · funext n
    exact add_div _ _ _
  · dsimp [pairedLog]
    rw [neg_mul, sub_neg_eq_add]
    ring

theorem pairedPower_div_norm_bound (u : ℂ) (n : ℕ) (theta : ℝ) :
    ‖pairedPower u n theta / (n : ℂ)‖ ≤ 2 * ‖u‖ ^ n := by
  by_cases hn : n = 0
  · subst n; simp
  · rw [norm_div, Complex.norm_natCast]
    calc
      _ ≤ (2 * ‖u‖ ^ n) / (n : ℝ) := div_le_div_of_nonneg_right (pairedPower_norm_bound u n theta) (Nat.cast_nonneg n)
      _ ≤ _ := div_le_self (by positivity) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)

/-- The actual log-series may be integrated termwise against the actual
angular probability law, with a proved geometric majorant. -/
theorem hasSum_integral_pairedPower_div (d : ℝ) (hd : 3 ≤ d) (u : ℂ) (hu : ‖u‖ < 1) :
    HasSum (fun n : ℕ => ∫ theta, pairedPower u n theta / (n : ℂ) ∂angularLaw d)
      (-(∫ theta, pairedLog u theta ∂angularLaw d)) := by
  letI := angularLaw_isProbability d hd
  have hs : Summable (fun n : ℕ => 2 * ‖u‖ ^ n) :=
    (summable_geometric_of_norm_lt_one (by simpa only [norm_norm] using hu)).mul_left 2
  have hh := hasSum_integral_of_dominated_convergence
    (μ := angularLaw d) (fun n _theta => 2 * ‖u‖ ^ n)
    (fun n => ((continuous_pairedPower u n).div_const (n : ℂ)).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (pairedPower_div_norm_bound u n))
    (Filter.Eventually.of_forall (fun _ => hs)) (integrable_const _)
    (Filter.Eventually.of_forall (pairedPower_div_hasSum u hu))
  simpa only [integral_neg] using hh

def logSeriesParameter (d : ℝ) (u : ℂ) : ℂ := u ^ 2 * ((-1 / (d - 1) : ℝ) : ℂ)

theorem logSeriesParameter_norm_lt_one (d : ℝ) (hd : 3 ≤ d) (u : ℂ) (hu : ‖u‖ < 1) :
    ‖logSeriesParameter d u‖ < 1 := by
  unfold logSeriesParameter
  rw [norm_mul, norm_pow]
  have hr : ‖((-1 / (d - 1) : ℝ) : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using angularPoisson_parameter d hd
  have hp : ‖u‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg u) hu.le
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _) |>.trans_eq (one_mul _)).trans_lt hr

theorem integral_pairedPower_even_div (d : ℝ) (hd : 3 ≤ d) (u : ℂ) (k : ℕ) :
    (∫ theta, pairedPower u (2 * k) theta / ((2 * k : ℕ) : ℂ) ∂angularLaw d) =
      -((d - 2 : ℝ) : ℂ) / 2 * (logSeriesParameter d u ^ k / (k : ℂ)) := by
  rw [integral_div, integral_pairedPower_even d hd u k]
  by_cases hk : k = 0
  · subst k; simp
  · rw [if_neg hk]
    simp only [logSeriesParameter, mul_pow, ← pow_mul, Nat.cast_mul, Nat.cast_ofNat,
      div_eq_mul_inv, mul_inv_rev]
    ring

theorem integral_pairedPower_odd_div (d : ℝ) (hd : 3 ≤ d) (u : ℂ) (k : ℕ) :
    (∫ theta, pairedPower u (2 * k + 1) theta / ((2 * k + 1 : ℕ) : ℂ) ∂angularLaw d) = 0 := by
  rw [integral_div, integral_pairedPower_odd d hd u k, zero_div]

/-- The even and odd subseries are evaluated from the actual paired-power
expectations, yielding the integrated logarithmic Taylor series. -/
theorem hasSum_integral_pairedPower_div_value (d : ℝ) (hd : 3 ≤ d) (u : ℂ) (hu : ‖u‖ < 1) :
    HasSum (fun n : ℕ => ∫ theta, pairedPower u n theta / (n : ℂ) ∂angularLaw d)
      (((d - 2 : ℝ) : ℂ) / 2 * Complex.log (1 - logSeriesParameter d u)) := by
  have hs := (Complex.hasSum_taylorSeries_neg_log (logSeriesParameter_norm_lt_one d hd u hu)).mul_left
    (-((d - 2 : ℝ) : ℂ) / 2)
  have he : HasSum (fun k : ℕ => ∫ theta, pairedPower u (2 * k) theta / ((2 * k : ℕ) : ℂ) ∂angularLaw d)
      (((d - 2 : ℝ) : ℂ) / 2 * Complex.log (1 - logSeriesParameter d u)) := by
    convert hs using 1
    · funext k; exact integral_pairedPower_even_div d hd u k
    · ring
  have ho : HasSum (fun k : ℕ => ∫ theta, pairedPower u (2 * k + 1) theta / ((2 * k + 1 : ℕ) : ℂ) ∂angularLaw d) 0 := by
    simp only [integral_pairedPower_odd_div d hd u]
    exact hasSum_zero
  simpa only [add_zero] using (HasSum.even_add_odd
    (f := fun n : ℕ => ∫ theta, pairedPower u n theta / (n : ℂ) ∂angularLaw d) he ho)

/-- Exact logarithmic-factor average under the actual Kesten–McKay law.
Both infinite series and exchanges of integral have been proved above. -/
theorem integral_pairedLog (d : ℝ) (hd : 3 ≤ d) (u : ℂ) (hu : ‖u‖ < 1) :
    (∫ theta, pairedLog u theta ∂angularLaw d) =
      -((d - 2 : ℝ) : ℂ) / 2 * Complex.log (1 - logSeriesParameter d u) := by
  have hh := (hasSum_integral_pairedPower_div d hd u hu).unique
    (hasSum_integral_pairedPower_div_value d hd u hu)
  linear_combination -hh

end GeneralizedBulk.KestenMcKay
