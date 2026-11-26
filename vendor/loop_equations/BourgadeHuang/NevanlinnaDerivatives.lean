import BourgadeHuang.NevanlinnaLoop

/-! Derivatives of weighted inverse powers and the analytic meaning of the diagonal interaction. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

/-- Differentiation of the weighted power kernel, to every order. -/
theorem hasDerivAt_anchoredPowerKernel (q : ℕ) (a : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (fun w => anchoredPowerKernel q w a)
      ((q + 1 : ℂ) * anchoredPowerKernel (q + 1) z a) z := by
  have hh := ((hasDerivAt_reciprocal a hz).pow (q + 1)).const_mul (nevanlinnaWeight a : ℂ)
  convert hh using 1
  simp only [anchoredPowerKernel, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [show q + 1 + 1 = q + 2 by omega, pow_add]
  ring

/-- Differentiation under the power-kernel integral is justified by a locally
uniform integrable bound; this is valid for every order. -/
theorem hasDerivAt_anchoredPowerIntegral (q : ℕ) (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (anchoredPowerIntegral q s)
      ((q + 1 : ℂ) * anchoredPowerIntegral (q + 1) s z) z := by
  let R := |z.im| / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hmeas (w : ℂ) : Measurable (anchoredPowerKernel q w) :=
    (Complex.measurable_ofReal.comp continuous_nevanlinnaWeight.measurable).mul
      ((Complex.measurable_ofReal.sub measurable_const).inv.pow_const (q + 1))
  have hdm : AEStronglyMeasurable
      (fun a => (q + 1 : ℂ) * anchoredPowerKernel (q + 1) z a) s.val.1.measure :=
    (continuous_const.mul (continuous_anchoredPowerKernel (q + 1) hz)).aestronglyMeasurable
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w a => anchoredPowerKernel q w a)
    (F' := fun w a => (q + 1 : ℂ) * anchoredPowerKernel (q + 1) w a)
    (bound := fun a => (q + 1 : ℝ) * (1 / R) ^ (q + 2) * nevanlinnaWeight a) hR
    (Filter.Eventually.of_forall (fun w => (hmeas w).aestronglyMeasurable))
    (integrable_anchoredPowerKernel q s hz) hdm ?_
    (s.integrable_weight.const_mul _) ?_).2
  · simpa only [anchoredPowerIntegral, integral_const_mul] using hh
  · apply Filter.Eventually.of_forall
    intro a w hw
    have hi := half_imaginary_ball_bound z w hz hw
    have hbase : 1 / |w.im| ≤ 1 / R := one_div_le_one_div_of_le hR hi.1
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / |w.im|) hbase (q + 2)
    have hq : ‖(q + 1 : ℂ)‖ = (q + 1 : ℝ) := by
      norm_cast
    rw [norm_mul, hq]
    calc
      _ ≤ (q + 1 : ℝ) * ((1 / |w.im|) ^ (q + 2) * nevanlinnaWeight a) :=
        mul_le_mul_of_nonneg_left (by simpa only [Nat.add_assoc] using (norm_anchoredPowerKernel_le (q + 1) hi.2 a)) (by positivity)
      _ ≤ (q + 1 : ℝ) * ((1 / R) ^ (q + 2) * nevanlinnaWeight a) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (nevanlinnaWeight_nonneg a))
          (by positivity)
      _ = _ := by ring
  · exact Filter.Eventually.of_forall fun a w hw =>
      hasDerivAt_anchoredPowerKernel q a (half_imaginary_ball_bound z w hz hw).2

/-- The diagonal interaction is exactly half the second derivative. -/
theorem hasDerivAt_anchoredDerivative (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (anchoredDerivative s) (2 * anchoredSecondHalf s z) z := by
  have h0 := hasDerivAt_anchoredPowerIntegral 0 s hz
  have h1 := hasDerivAt_anchoredPowerIntegral 1 s hz
  have hh := ((hasDerivAt_const z (s.val.2.im : ℂ)).add
    (((hasDerivAt_id z).const_mul 2).mul h0)).add
    (((hasDerivAt_const z (1 : ℂ)).add ((hasDerivAt_id z).pow 2)).mul h1)
  convert hh using 1
  simp only [anchoredSecondHalf, Nat.cast_zero, Nat.cast_one, zero_add,
    one_mul, mul_one, id_eq, Nat.cast_ofNat]
  norm_num
  ring

@[simp] theorem deriv_anchoredNevanlinna (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) : deriv (anchoredNevanlinna s) z = anchoredDerivative s z :=
  (hasDerivAt_anchoredNevanlinna s hz).deriv

@[simp] theorem deriv_anchoredDerivative (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) : deriv (anchoredDerivative s) z = 2 * anchoredSecondHalf s z :=
  (hasDerivAt_anchoredDerivative s hz).deriv

/-- Away from its removable diagonal, the interaction is the differentiated
divided difference of the genuine analytic reconstructed resolvent. -/
theorem anchoredInteraction_eq_deriv_dividedDifference (s : AnchoredCountingState)
    {w v : ℂ} (hv : v.im ≠ 0) (hwv : w ≠ v) :
    anchoredInteraction s w v = deriv (fun z =>
      (anchoredNevanlinna s w - anchoredNevanlinna s z) / (w - z)) v := by
  have hd := ((hasDerivAt_const v (anchoredNevanlinna s w)).sub
    (hasDerivAt_anchoredNevanlinna s hv)).div
      ((hasDerivAt_const v w).sub (hasDerivAt_id v)) (sub_ne_zero.mpr hwv)
  simp only [id_eq] at hd
  rw [hd.deriv]
  simp only [anchoredInteraction, if_neg hwv, id_eq]
  ring

end BourgadeHuang
