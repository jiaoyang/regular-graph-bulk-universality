import GeneralizedBulk.Spectral.TreePrimitiveRadial
import GeneralizedBulk.Spectral.RadialContraction

/-! Exact spectral coordinates of the contracted bulk cavity root. -/
noncomputable section
open scoped ComplexConjugate
namespace GeneralizedBulk.KestenMcKay

theorem cavityBoundary_inv (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    (cavityBoundary d E)⁻¹ = ((d - 1 : ℝ) : ℂ) * conj (cavityBoundary d E) := by
  apply Complex.ext
  · simp only [Complex.inv_re, cavityBoundary_normSq d E hd hbulk, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, zero_mul, sub_zero]
    simpa only [mul_comm] using (div_inv_eq_mul ((cavityBoundary d E).re) (d - 1))
  · simp only [Complex.inv_im, cavityBoundary_normSq d E hd hbulk, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, zero_mul, add_zero]
    rw [div_inv_eq_mul]
    ring

theorem treeSpectralPoint_radial_re (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1))
    (r : ℝ) (hr : r ≠ 0) :
    (treeSpectralPoint d ((r : ℂ) * cavityBoundary d E)).re = E / 2 * (r + r⁻¹) := by
  rw [treeSpectralPoint, mul_inv_rev, cavityBoundary_inv d E hd hbulk]
  have hi : ((r : ℂ)⁻¹) = ((r⁻¹ : ℝ) : ℂ) := by simp
  rw [hi]
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    zero_mul, mul_zero, sub_zero, add_zero, cavityBoundary]
  have hq : d - 1 ≠ 0 := by linarith
  field_simp
  <;> ring

theorem treeSpectralPoint_radial_im (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1))
    (r : ℝ) (hr : r ≠ 0) :
    (treeSpectralPoint d ((r : ℂ) * cavityBoundary d E)).im =
      (d - 1) * (cavityBoundary d E).im * (r⁻¹ - r) := by
  rw [treeSpectralPoint, mul_inv_rev, cavityBoundary_inv d E hd hbulk]
  have hi : ((r : ℂ)⁻¹) = ((r⁻¹ : ℝ) : ℂ) := by simp
  rw [hi]
  simp only [Complex.sub_im, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  ring

theorem cavityBoundary_im_pos (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    0 < (cavityBoundary d E).im := by
  exact div_pos (Real.sqrt_pos.mpr (by dsimp [discriminant]; linarith))
    (mul_pos (by norm_num) (by linarith))

theorem treeLogParameter_boundary_norm (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    ‖treeLogParameter d (cavityBoundary d E)‖ = 1 := by
  have hq : 0 < d - 1 := by linarith
  have hn : ‖treeLogParameter d (cavityBoundary d E)‖ ^ 2 = 1 := by
    unfold treeLogParameter
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hq.le,
      ← Complex.normSq_eq_norm_sq, cavityBoundary_normSq d E hd hbulk, mul_inv_cancel₀ hq.ne']
  nlinarith [norm_nonneg (treeLogParameter d (cavityBoundary d E))]

theorem treeLogParameter_radial_norm (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1))
    (r : ℝ) (hr : 0 ≤ r) : ‖treeLogParameter d ((r : ℂ) * cavityBoundary d E)‖ = r := by
  have he : treeLogParameter d ((r : ℂ) * cavityBoundary d E) =
      (r : ℂ) * treeLogParameter d (cavityBoundary d E) := by unfold treeLogParameter; ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
    treeLogParameter_boundary_norm d E hd hbulk, mul_one]

theorem radial_energyShift_bound (E r : ℝ) (hr : 1 / 2 ≤ r) :
    |E / 2 * (r + r⁻¹) - E| ≤ |E| * (1 - r) ^ 2 := by
  have hrp : 0 < r := by linarith
  have hid : E / 2 * (r + r⁻¹) - E = E * (1 - r) ^ 2 / (2 * r) := by field_simp; ring
  rw [hid, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (1 - r)), abs_of_pos (mul_pos (by norm_num) hrp)]
  exact div_le_self (by positivity) (by linarith)

end GeneralizedBulk.KestenMcKay
