import GeneralizedBulk.Spectral.TreeLogFactor

/-! Algebraic and upper-half-plane control of actual regular-tree cavity roots. -/
noncomputable section
namespace GeneralizedBulk.KestenMcKay

def IsCavityRoot (d : ℝ) (z g : ℂ) : Prop :=
  ((d - 1 : ℝ) : ℂ) * g ^ 2 + z * g + 1 = 0

theorem IsCavityRoot.ne_zero {d : ℝ} {z g : ℂ} (hg : IsCavityRoot d z g) : g ≠ 0 := by
  intro hz
  unfold IsCavityRoot at hg
  simp only [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero, zero_add] at hg
  exact one_ne_zero hg

theorem IsCavityRoot.spectralPoint {d : ℝ} {z g : ℂ} (hg : IsCavityRoot d z g) :
    z = treeSpectralPoint d g := by
  apply mul_right_cancel₀ hg.ne_zero
  unfold treeSpectralPoint
  rw [sub_mul, neg_mul, inv_mul_cancel₀ hg.ne_zero]
  unfold IsCavityRoot at hg
  linear_combination hg

/-- The genuine imaginary root equation fixes the upper-half-plane sign and
rules out roots on the critical circle. -/
theorem IsCavityRoot.imaginary_identity {d : ℝ} {z g : ℂ} (hg : IsCavityRoot d z g) :
    z.im * Complex.normSq g = g.im * (1 - (d - 1) * Complex.normSq g) := by
  have hh := congrArg Complex.im hg.spectralPoint
  simp only [treeSpectralPoint, Complex.sub_im, Complex.neg_im, Complex.inv_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, neg_neg] at hh
  rw [hh]
  have hn := (Complex.normSq_pos.mpr hg.ne_zero).ne'
  field_simp [hn]
  <;> ring

theorem IsCavityRoot.not_critical_circle {d : ℝ} {z g : ℂ} (hg : IsCavityRoot d z g)
    (hz : 0 < z.im) : (d - 1) * Complex.normSq g ≠ 1 := by
  intro he
  have hh := hg.imaginary_identity
  rw [he, sub_self, mul_zero] at hh
  exact (mul_pos hz (Complex.normSq_pos.mpr hg.ne_zero)).ne' hh

theorem IsCavityRoot.im_pos_of_small {d : ℝ} {z g : ℂ} (hg : IsCavityRoot d z g)
    (hz : 0 < z.im) (hsmall : (d - 1) * Complex.normSq g < 1) : 0 < g.im := by
  have hh := hg.imaginary_identity
  have hp : 0 < g.im * (1 - (d - 1) * Complex.normSq g) :=
    (mul_pos hz (Complex.normSq_pos.mpr hg.ne_zero)).trans_eq hh
  exact (mul_pos_iff_of_pos_right (by linarith : 0 < 1 - (d - 1) * Complex.normSq g)).mp hp

/-- Two distinct quadratic roots have the exact reciprocal product. -/
theorem IsCavityRoot.product_of_ne {d : ℝ} {z g h : ℂ} (hg : IsCavityRoot d z g)
    (hh : IsCavityRoot d z h) (hne : g ≠ h) : ((d - 1 : ℝ) : ℂ) * g * h = 1 := by
  have hf : (g - h) * (((d - 1 : ℝ) : ℂ) * (g + h) + z) = 0 := by
    unfold IsCavityRoot at hg hh
    linear_combination hg - hh
  have hs := (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hne)
  unfold IsCavityRoot at hg
  linear_combination g * hs - hg

end GeneralizedBulk.KestenMcKay
