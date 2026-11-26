import GeneralizedBulk.Entropy.WickDiagonal

/-! Actual fourth moment discrepancies of normalized finite signals. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.Hermite
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

/-- Every actual homogeneous polynomial test is paired with the finite
signal's actual Gaussian chaos vector. -/
theorem signalChaos_inner_fullChaos (weight : S → ℝ) (signal : S → I → ℝ)
    (degree : ℕ) (g : fullChaosSpace I degree) :
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (signalChaos weight signal degree) g =
      ∑ s, weight s * fullChaosEval I degree (signal s) g := by
  have heq := fullChaosCoordinates_spec I degree g
  change chaosLp (degreeIndexNat I) (fullChaosCoordinates I degree g) = (g : Lp ℝ 2 (standardGaussian I)) at heq
  rw [← heq, signalChaos_inner_chaosLp weight signal degree (degreeIndexNat I) _ (degreeIndexNat_sum I)]
  simp_rw [fullChaosEval_apply]

theorem unit_fourth_moment_bound (D : NormalizedFiniteSignal I S) (u : I → ℝ)
    (hu : ∑ i, u i ^ 2 = 1) :
    |(∑ s, D.weight s * linearForm u (D.signal s) ^ 4) - 3| ≤
      ‖signalChaos D.weight D.signal 4‖ * Real.sqrt 24 := by
  obtain ⟨g, hg, hgnorm⟩ := exists_unit_wickFourth u hu
  have hsecond : (∑ s, D.weight s * linearForm u (D.signal s) ^ 2) = 1 := by
    have hh := weighted_bilinear D.weight D.signal D.covariance u u
    simpa only [linearForm, pow_two, mul_assoc, hu] using hh.trans (by simpa only [pow_two] using hu)
  have htest : (∑ s, D.weight s * fullChaosEval I 4 (D.signal s) g) =
      (∑ s, D.weight s * linearForm u (D.signal s) ^ 4) - 3 := by
    simp_rw [hg]
    have he (s : S) : D.weight s * (linearForm u (D.signal s) ^ 4 - 6 * linearForm u (D.signal s) ^ 2 + 3) =
        D.weight s * linearForm u (D.signal s) ^ 4 - 6 * (D.weight s * linearForm u (D.signal s) ^ 2) +
          3 * D.weight s := by ring
    simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsecond, D.total]
    ring
  rw [← htest, ← signalChaos_inner_fullChaos, ← hgnorm]
  exact abs_real_inner_le_norm _ _

/-- The fourth Gaussian cumulant in any linear direction has an explicit
norm-scaled bound. The zero row is treated without division. -/
theorem linear_fourth_moment_bound (D : NormalizedFiniteSignal I S) (u : I → ℝ) :
    |(∑ s, D.weight s * linearForm u (D.signal s) ^ 4) - 3 * (∑ i, u i ^ 2) ^ 2| ≤
      ‖signalChaos D.weight D.signal 4‖ * Real.sqrt 24 * (∑ i, u i ^ 2) ^ 2 := by
  let q := ∑ i, u i ^ 2
  have hq : 0 ≤ q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hq0 : q = 0
  · have hu (i : I) : u i = 0 := by
      have hi := Finset.single_le_sum (s := Finset.univ) (f := fun i => u i ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      have hs : u i ^ 2 = 0 := by change u i ^ 2 ≤ q at hi; nlinarith [sq_nonneg (u i)]
      exact pow_eq_zero hs
    have huf : u = 0 := funext hu
    simp only [huf, linearForm, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_pow (by decide : 4 ≠ 0),
      mul_zero, sub_zero, abs_zero, le_refl]
    norm_num
  · let r := Real.sqrt q
    have hr : 0 < r := Real.sqrt_pos.mpr (lt_of_le_of_ne hq (Ne.symm hq0))
    have hrsq : r ^ 2 = q := Real.sq_sqrt hq
    let v : I → ℝ := fun i => u i / r
    have hv : (∑ i, v i ^ 2) = 1 := by
      simp only [v, div_pow, ← Finset.sum_div]
      change q / r ^ 2 = 1
      rw [hrsq, div_self hq0]
    have hlin (x : I → ℝ) : linearForm u x = r * linearForm v x := by
      unfold linearForm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [v]
      field_simp [ne_of_gt hr]
    have htest := unit_fourth_moment_bound D v hv
    have hsum : (∑ s, D.weight s * linearForm u (D.signal s) ^ 4) =
        r ^ 4 * ∑ s, D.weight s * linearForm v (D.signal s) ^ 4 := by
      simp_rw [hlin, mul_pow]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    have hr4 : r ^ 4 = q ^ 2 := by nlinarith [sq_nonneg (r ^ 2 - q)]
    rw [hsum, hr4]
    change |q ^ 2 * (∑ s, D.weight s * linearForm v (D.signal s) ^ 4) - 3 * q ^ 2| ≤ _
    have he : q ^ 2 * (∑ s, D.weight s * linearForm v (D.signal s) ^ 4) - 3 * q ^ 2 =
        q ^ 2 * ((∑ s, D.weight s * linearForm v (D.signal s) ^ 4) - 3) := by ring
    rw [he, abs_mul, abs_of_nonneg (sq_nonneg q)]
    have hh := mul_le_mul_of_nonneg_left htest (sq_nonneg q)
    exact hh.trans_eq (by ring)

end GeneralizedBulk.Entropy.Mehler
