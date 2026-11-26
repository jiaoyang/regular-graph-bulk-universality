import GeneralizedBulk.Spectral.TreePotential
import GeneralizedBulk.Analysis.LogLipschitz

/-! Quantitative radial stability of the actual tree logarithmic primitive. -/
noncomputable section
namespace GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Analysis

def treePrimitive (d : ℝ) (g : ℂ) : ℝ :=
  -Real.log ‖g‖ - (d - 2) / 2 * Real.log ‖1 - g ^ 2‖

theorem treePrimitive_radial_bound (d : ℝ) (hd : 3 ≤ d) (g : ℂ) (hg : g ≠ 0)
    (hgn : ‖g‖ ^ 2 ≤ 1 / 2) (r : ℝ) (hr : 1 / 2 ≤ r) (hr' : r ≤ 1) :
    |treePrimitive d ((r : ℂ) * g) - treePrimitive d g| ≤ d * (1 - r) := by
  have hr0 : 0 ≤ r := by linarith
  have hre : 0 ≤ 1 - r := by linarith
  have hr2 : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hrad : ‖((r : ℂ) * g) ^ 2‖ ≤ 1 / 2 := by
    rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, mul_pow]
    have hm := mul_le_mul_of_nonneg_left hgn (sq_nonneg r)
    nlinarith [sq_nonneg r]
  have hA : 1 / 2 ≤ ‖1 - ((r : ℂ) * g) ^ 2‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (((r : ℂ) * g) ^ 2)
    rw [norm_one] at hh
    linarith
  have hB : 1 / 2 ≤ ‖1 - g ^ 2‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (g ^ 2)
    rw [norm_one, norm_pow] at hh
    linarith
  have hdiff : ‖(1 - ((r : ℂ) * g) ^ 2) - (1 - g ^ 2)‖ ≤ 1 - r := by
    have hid : (1 - ((r : ℂ) * g) ^ 2) - (1 - g ^ 2) = ((1 - r ^ 2 : ℝ) : ℂ) * g ^ 2 := by
      push_cast; ring
    rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr2, norm_pow]
    have hm := mul_le_mul_of_nonneg_left hgn hr2
    nlinarith
  have hlog2 : |Real.log ‖1 - ((r : ℂ) * g) ^ 2‖ - Real.log ‖1 - g ^ 2‖| ≤ 2 * (1 - r) := by
    have hh := abs_log_norm_sub_le (1 - ((r : ℂ) * g) ^ 2) (1 - g ^ 2) (1 / 2) (by norm_num) hA hB
    exact hh.trans (by
      convert mul_le_mul_of_nonneg_left hdiff (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring)
  have hlog1 : |Real.log ‖(r : ℂ) * g‖ - Real.log ‖g‖| ≤ 2 * (1 - r) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      Real.log_mul (by linarith : r ≠ 0) (norm_ne_zero_iff.mpr hg)]
    have hh := abs_log_sub_le_abs_sub_div (by norm_num : (0 : ℝ) < 1 / 2) hr (by norm_num : (1 / 2 : ℝ) ≤ 1)
    simp only [Real.log_one, sub_zero] at hh
    have ha : |r - 1| = 1 - r := by rw [abs_sub_comm, abs_of_nonneg hre]
    rw [add_sub_cancel_right]
    exact hh.trans_eq (by rw [ha]; ring)
  have hc : 0 ≤ (d - 2) / 2 := by linarith
  unfold treePrimitive
  have hid : -Real.log ‖(r : ℂ) * g‖ - (d - 2) / 2 * Real.log ‖1 - ((r : ℂ) * g) ^ 2‖ -
      (-Real.log ‖g‖ - (d - 2) / 2 * Real.log ‖1 - g ^ 2‖) =
      -(Real.log ‖(r : ℂ) * g‖ - Real.log ‖g‖) -
        (d - 2) / 2 * (Real.log ‖1 - ((r : ℂ) * g) ^ 2‖ - Real.log ‖1 - g ^ 2‖) := by ring
  rw [hid]
  calc
    _ ≤ |Real.log ‖(r : ℂ) * g‖ - Real.log ‖g‖| +
        (d - 2) / 2 * |Real.log ‖1 - ((r : ℂ) * g) ^ 2‖ - Real.log ‖1 - g ^ 2‖| := by
      simpa only [abs_neg, abs_mul, abs_of_nonneg hc] using
        abs_sub (-(Real.log ‖(r : ℂ) * g‖ - Real.log ‖g‖))
          ((d - 2) / 2 * (Real.log ‖1 - ((r : ℂ) * g) ^ 2‖ - Real.log ‖1 - g ^ 2‖))
    _ ≤ 2 * (1 - r) + (d - 2) / 2 * (2 * (1 - r)) :=
      add_le_add hlog1 (mul_le_mul_of_nonneg_left hlog2 hc)
    _ = _ := by ring

theorem cavityBoundary_ne_zero (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    cavityBoundary d E ≠ 0 := by
  intro hz
  have hh := cavityBoundary_quadratic d E hd hbulk
  simp only [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero, zero_add] at hh
  exact one_ne_zero hh

theorem cavityBoundary_norm_sq_le_half (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    ‖cavityBoundary d E‖ ^ 2 ≤ 1 / 2 := by
  rw [← Complex.normSq_eq_norm_sq, cavityBoundary_normSq d E hd hbulk, inv_eq_one_div]
  apply (div_le_div_iff₀ (by linarith : 0 < d - 1) (by norm_num : (0 : ℝ) < 2)).mpr
  linarith

theorem treePrimitive_cavityBoundary (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    treePrimitive d (cavityBoundary d E) =
      (d - 1) / 2 * Real.log (d - 1) - (d - 2) / 4 * Real.log (d ^ 2 - E ^ 2) := by
  have hh := treePotential_boundary_value d E hd hbulk
  simp only [Complex.normSq_eq_norm_sq, Real.log_pow] at hh
  convert hh using 1 <;> unfold treePrimitive <;> ring

end GeneralizedBulk.KestenMcKay
