import GeneralizedBulk.Spectral.TreeCavityRoots
import GeneralizedBulk.Spectral.CavityRadial

/-! The actual regular-tree cavity Green function is the unique small
quadratic root in the upper half-plane; its root properties are proved. -/
noncomputable section
namespace GeneralizedBulk.KestenMcKay

def treeCavity (d : ℝ) (hd : 3 ≤ d) (z : ℂ) : ℂ :=
  if hz : 0 < z.im then Classical.choose (exists_small_cavityRoot d hd z hz) else 0

theorem treeCavity_isRoot (d : ℝ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    IsCavityRoot d z (treeCavity d hd z) := by
  simp only [treeCavity, dif_pos hz]
  exact (Classical.choose_spec (exists_small_cavityRoot d hd z hz)).1

theorem treeCavity_small (d : ℝ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    (d - 1) * Complex.normSq (treeCavity d hd z) < 1 := by
  simp only [treeCavity, dif_pos hz]
  exact (Classical.choose_spec (exists_small_cavityRoot d hd z hz)).2

theorem treeCavity_unique (d : ℝ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im)
    (g : ℂ) (hg : IsCavityRoot d z g) (hsmall : (d - 1) * Complex.normSq g < 1) :
    treeCavity d hd z = g :=
  small_cavityRoot_unique d hd z _ _ (treeCavity_isRoot d hd z hz) hg (treeCavity_small d hd z hz) hsmall

theorem treeCavity_im_pos (d : ℝ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    0 < (treeCavity d hd z).im :=
  (treeCavity_isRoot d hd z hz).im_pos_of_small hz (treeCavity_small d hd z hz)

theorem treeCavity_ne_zero (d : ℝ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) : treeCavity d hd z ≠ 0 :=
  (treeCavity_isRoot d hd z hz).ne_zero

theorem treeCavity_norm_sq_le_half (d : ℝ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    ‖treeCavity d hd z‖ ^ 2 ≤ 1 / 2 := by
  have hs := treeCavity_small d hd z hz
  have hn := Complex.normSq_nonneg (treeCavity d hd z)
  have hm := mul_le_mul_of_nonneg_right (by linarith : 2 ≤ d - 1) hn
  rw [Complex.sq_norm]
  linarith

theorem treeCavity_norm_le_one (d : ℝ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    ‖treeCavity d hd z‖ ≤ 1 := by
  have hh := treeCavity_norm_sq_le_half d hd z hz
  nlinarith [norm_nonneg (treeCavity d hd z)]

theorem treeLogParameter_norm_sq (d : ℝ) (hd : 3 ≤ d) (g : ℂ) :
    ‖treeLogParameter d g‖ ^ 2 = (d - 1) * Complex.normSq g := by
  unfold treeLogParameter
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by linarith), Complex.sq_norm]

theorem treeCavity_logParameter_norm_lt_one (d : ℝ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    ‖treeLogParameter d (treeCavity d hd z)‖ < 1 := by
  have hs := treeCavity_small d hd z hz
  rw [← treeLogParameter_norm_sq d hd] at hs
  nlinarith [norm_nonneg (treeLogParameter d (treeCavity d hd z))]

theorem isCavityRoot_treeSpectralPoint (d : ℝ) (g : ℂ) (hg : g ≠ 0) :
    IsCavityRoot d (treeSpectralPoint d g) g := by
  unfold IsCavityRoot treeSpectralPoint
  rw [sub_mul, neg_mul, inv_mul_cancel₀ hg]
  ring

end GeneralizedBulk.KestenMcKay
