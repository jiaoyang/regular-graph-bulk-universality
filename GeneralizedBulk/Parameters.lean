import GeneralizedBulk.Algebra

/-!
# Calibrated coefficients for the generalized switching criterion

The parameter domain and all calibration identities are concrete real
inequalities and equalities. This module introduces no probabilistic assumptions.
-/
noncomputable section

namespace GeneralizedBulk

/-- The two-parameter bulk domain of the Gaussian-marked criterion. -/
structure Parameters where
  p : ℝ
  r : ℝ
  r_pos : 0 < r
  r_lt_one : r < 1
  bulk : p ^ 2 < 4 * r * (1 - r)

namespace Parameters

variable (P : Parameters)

/-- The spectral covariance is nondegenerate. -/
theorem p_sq_lt_one : P.p ^ 2 < 1 := by
  nlinarith [sq_nonneg (2 * P.r - 1), P.bulk]

theorem abs_p_lt_one : |P.p| < 1 :=
  (sq_lt_one_iff_abs_lt_one P.p).mp P.p_sq_lt_one

theorem denominator_pos : 0 < 1 - P.p ^ 2 := sub_pos.mpr P.p_sq_lt_one

theorem discriminant_pos : 0 < 4 * P.r * (1 - P.r) - P.p ^ 2 :=
  sub_pos.mpr P.bulk

/-- The deterministic real centering coefficient. -/
def center : ℝ := -P.p * (1 - 2 * P.r) / (2 * (1 - P.p ^ 2))

/-- The positive microscopic scale. -/
def scale : ℝ := Real.sqrt (4 * P.r * (1 - P.r) - P.p ^ 2) /
  (2 * (1 - P.p ^ 2))

theorem scale_pos : 0 < P.scale := by
  exact div_pos (Real.sqrt_pos.2 P.discriminant_pos)
    (mul_pos (by norm_num) P.denominator_pos)

/-- The first calibration eliminates the linear term. -/
theorem center_calibration :
    2 * (1 - P.p ^ 2) * P.center + P.p * (1 - 2 * P.r) = 0 := by
  have hq : 1 - P.p ^ 2 ≠ 0 := ne_of_gt P.denominator_pos
  unfold center
  field_simp [hq]
  ring

/-- The second calibration matches the constant and quadratic coefficients. -/
theorem scale_calibration :
    (1 - P.p ^ 2) * (P.center ^ 2 + P.scale ^ 2) = P.r * (1 - P.r) := by
  have hq : 1 - P.p ^ 2 ≠ 0 := ne_of_gt P.denominator_pos
  have hs := Real.sq_sqrt (le_of_lt P.discriminant_pos)
  unfold center scale
  field_simp
  nlinarith [hs]

/-- The coefficient dividing the stationary identity is strictly positive. -/
def contractionCoefficient : ℝ := 8 * P.scale ^ 2 * (1 - P.p ^ 2)

theorem contractionCoefficient_pos : 0 < P.contractionCoefficient :=
  GeneralizedSwitching.contraction_coefficient_pos P.p P.scale P.scale_pos P.abs_p_lt_one

/-- Calibration remains valid after passing to the complex analytic variable. -/
theorem complex_scalar_polynomial (v : ℂ) :
    ((P.center : ℂ) + (P.scale : ℂ) * v) ^ 2 -
        ((P.p : ℂ) * ((P.center : ℂ) + (P.scale : ℂ) * v) + (P.r : ℂ)) ^ 2 +
        ((P.p : ℂ) * ((P.center : ℂ) + (P.scale : ℂ) * v) + (P.r : ℂ)) =
      (P.scale : ℂ) ^ 2 * (1 - (P.p : ℂ) ^ 2) * (v ^ 2 + 1) := by
  apply GeneralizedSwitching.calibrated_scalar_polynomial
  · exact_mod_cast P.center_calibration
  · exact_mod_cast P.scale_calibration

end Parameters
end GeneralizedBulk

namespace GeneralizedBulk
namespace Parameters

/-- The regular-graph bulk interval lies inside the denominator's positivity domain. -/
theorem regular_denominator_pos (d E : ℝ) (hbulk : E ^ 2 < 4 * (d - 1)) :
    0 < d ^ 2 - E ^ 2 := by
  nlinarith [sq_nonneg (d - 2)]

/-- Regular graphs instantiate the generalized parameter domain. The real degree
formulation also covers the integer degree after the usual cast. -/
def regular (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) : Parameters := by
  have hd0 : 0 < d := by linarith
  have hdne : d ≠ 0 := ne_of_gt hd0
  refine ⟨E / d, 1 / d, one_div_pos.mpr hd0, ?_, ?_⟩
  · exact (div_lt_one hd0).2 (by linarith)
  · have hrew : 4 * (1 / d) * (1 - 1 / d) = (4 * (d - 1)) / d ^ 2 := by
      field_simp [hdne]
      ring_nf
      simp
    rw [div_pow, hrew]
    exact (div_lt_div_iff_of_pos_right (sq_pos_of_pos hd0)).2 hbulk

@[simp] theorem regular_p (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    (regular d E hd hbulk).p = E / d := rfl

@[simp] theorem regular_r (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    (regular d E hd hbulk).r = 1 / d := rfl

/-- The center specializes to the manuscript's unnormalized adjacency convention. -/
theorem regular_center (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    (regular d E hd hbulk).center = -((d - 2) * E) / (2 * (d ^ 2 - E ^ 2)) := by
  have hd0 : 0 < d := by linarith
  have hdne : d ≠ 0 := ne_of_gt hd0
  have hqne : d ^ 2 - E ^ 2 ≠ 0 := ne_of_gt (regular_denominator_pos d E hbulk)
  dsimp [center]
  field_simp [hdne, hqne]
  ring

/-- The scale specializes to pi times the Kesten--McKay bulk density. -/
theorem regular_scale (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    (regular d E hd hbulk).scale =
      d * Real.sqrt (4 * (d - 1) - E ^ 2) / (2 * (d ^ 2 - E ^ 2)) := by
  have hd0 : 0 < d := by linarith
  have hdne : d ≠ 0 := ne_of_gt hd0
  have hqne : d ^ 2 - E ^ 2 ≠ 0 := ne_of_gt (regular_denominator_pos d E hbulk)
  have hdiscr : 4 * (1 / d) * (1 - 1 / d) - (E / d) ^ 2 =
      (4 * (d - 1) - E ^ 2) / d ^ 2 := by
    field_simp [hdne]
    ring
  dsimp [scale]
  rw [hdiscr, Real.sqrt_div (sub_nonneg.mpr (le_of_lt hbulk)), Real.sqrt_sq_eq_abs, abs_of_pos hd0]
  field_simp [hdne, hqne]
  ring

end Parameters
end GeneralizedBulk
