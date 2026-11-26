import GeneralizedBulk.Spectral.PoissonKernel

/-! The actual angular Kesten–McKay density is an explicit Poisson-kernel
combination. This gives its Fourier moments without a spectral assumption. -/
noncomputable section
namespace GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Spectral

theorem angularPoisson_parameter (d : ℝ) (hd : 3 ≤ d) : |(-1 / (d - 1) : ℝ)| < 1 := by
  rw [abs_div, abs_neg, abs_one, abs_of_pos (by linarith : 0 < d - 1)]
  apply (div_lt_one (by linarith : 0 < d - 1)).mpr
  linarith

theorem angularPoisson_value (d : ℝ) (hd : 3 ≤ d) (theta : ℝ) :
    poissonKernel (-1 / (d - 1)) (2 * theta) =
      d * (d - 2) / (d ^ 2 - 4 * (d - 1) * Real.sin theta ^ 2) := by
  have hq : d - 1 ≠ 0 := by linarith
  have hden := (angularDenominator_pos d hd theta).ne'
  have hs : Real.sin theta ^ 2 = 1 - Real.cos theta ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq theta]
  have heq : 1 - 2 * (-1 / (d - 1)) * Real.cos (2 * theta) + (-1 / (d - 1)) ^ 2 =
      (d ^ 2 - 4 * (d - 1) * Real.sin theta ^ 2) / (d - 1) ^ 2 := by
    rw [Real.cos_two_mul]
    field_simp [hq]
    ring_nf
    simp only [hs]
    ring
  unfold poissonKernel
  rw [heq]
  field_simp [hq, hden]
  <;> ring

theorem angularDensity_eq_poisson (d : ℝ) (hd : 3 ≤ d) (theta : ℝ) :
    angularDensity d theta = d / (2 * Real.pi) -
      (d - 2) / (2 * Real.pi) * poissonKernel (-1 / (d - 1)) (2 * theta) := by
  rw [angularPoisson_value d hd theta]
  unfold angularDensity
  have hden := (angularDenominator_pos d hd theta).ne'
  field_simp [hden, Real.pi_ne_zero]
  have hs : Real.sin theta ^ 2 = 1 - Real.cos theta ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq theta]
  simp only [hs]
  ring

end GeneralizedBulk.KestenMcKay
