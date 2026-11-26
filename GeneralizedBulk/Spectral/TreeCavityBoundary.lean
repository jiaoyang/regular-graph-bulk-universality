import GeneralizedBulk.Spectral.TreeCavity
import GeneralizedBulk.Spectral.KestenMcKayUniformPotential

/-! Direct quantitative boundary convergence of the actual small tree cavity
root, without any unproved complex branch convention. -/
noncomputable section
open scoped ComplexConjugate
namespace GeneralizedBulk.KestenMcKay

theorem cavityBoundary_root_sum (d E : ℝ) (hd : 3 ≤ d) :
    ((d - 1 : ℝ) : ℂ) * (cavityBoundary d E + conj (cavityBoundary d E)) = -(E : ℂ) := by
  have hq : d - 1 ≠ 0 := by linarith
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.conj_re, Complex.conj_im, Complex.neg_re, zero_mul, sub_zero, cavityBoundary]
    field_simp
    <;> ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
      Complex.conj_re, Complex.conj_im, Complex.neg_im, Complex.ofReal_im]
    ring

theorem cavityBoundary_root_product (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    ((d - 1 : ℝ) : ℂ) * cavityBoundary d E * conj (cavityBoundary d E) = 1 := by
  rw [mul_assoc, Complex.mul_conj, cavityBoundary_normSq d E hd hbulk,
    Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (by linarith : d - 1 ≠ 0))]

 theorem IsCavityRoot.boundary_factorization {d E : ℝ} (hd : 3 ≤ d)
    (hbulk : E ^ 2 < 4 * (d - 1)) {z g : ℂ} (hg : IsCavityRoot d z g) :
    ((d - 1 : ℝ) : ℂ) * (g - cavityBoundary d E) * (g - conj (cavityBoundary d E)) =
      -(z - (E : ℂ)) * g := by
  calc
    _ = ((d - 1 : ℝ) : ℂ) * g ^ 2 -
        (((d - 1 : ℝ) : ℂ) * (cavityBoundary d E + conj (cavityBoundary d E))) * g +
        ((d - 1 : ℝ) : ℂ) * cavityBoundary d E * conj (cavityBoundary d E) := by ring
    _ = ((d - 1 : ℝ) : ℂ) * g ^ 2 + (E : ℂ) * g + 1 := by
      rw [cavityBoundary_root_sum d E hd, cavityBoundary_root_product d E hd hbulk]
      ring
    _ = _ := by unfold IsCavityRoot at hg; linear_combination hg

/-- The other boundary root lies in the lower half-plane, giving a genuine
positive separation from the actual upper-half-plane root. -/
theorem treeCavity_boundary_bound (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1))
    (z : ℂ) (hz : 0 < z.im) :
    ‖treeCavity d hd z - cavityBoundary d E‖ ≤ ‖z - (E : ℂ)‖ / bulkHeightScale d E := by
  let g := treeCavity d hd z
  let g0 := cavityBoundary d E
  have hq : 0 < d - 1 := by linarith
  have hb : 0 < bulkHeightScale d E := bulkHeightScale_pos d E hd hbulk
  have him : 0 < g.im := treeCavity_im_pos d hd z hz
  have h0im : 0 < g0.im := cavityBoundary_im_pos d E hd hbulk
  have hsep : g0.im ≤ ‖g - conj g0‖ := by
    have hh : g0.im ≤ |(g - conj g0).im| := by
      simp only [Complex.sub_im, Complex.conj_im, sub_neg_eq_add]
      rw [abs_of_nonneg (by linarith : 0 ≤ g.im + g0.im)]
      linarith
    exact hh.trans (Complex.abs_im_le_norm _)
  have hf := (treeCavity_isRoot d hd z hz).boundary_factorization hd hbulk (E := E)
  have hn := congrArg norm hf
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq, norm_neg] at hn
  have hl : bulkHeightScale d E * ‖g - g0‖ ≤ ‖z - (E : ℂ)‖ := by
    have ht := mul_le_mul_of_nonneg_left hsep (mul_nonneg hq.le (norm_nonneg (g - g0)))
    have heq : bulkHeightScale d E * ‖g - g0‖ = (d - 1) * ‖g - g0‖ * g0.im := by unfold bulkHeightScale g0; ring
    rw [heq]
    exact ht.trans (hn.le.trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (treeCavity_norm_le_one d hd z hz) (norm_nonneg (z - (E : ℂ)))))
  exact (le_div_iff₀ hb).mpr (by simpa only [mul_comm] using hl)

end GeneralizedBulk.KestenMcKay
