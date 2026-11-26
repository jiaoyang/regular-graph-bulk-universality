import GeneralizedBulk.Spectral.AngularFourier

/-! Explicit complex Fourier coefficients of the real Poisson kernel. -/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace GeneralizedBulk.Spectral

theorem circlePoint_pow_angularMode (r theta : ℝ) (n : ℕ) :
    circlePoint r (2 * theta) ^ n = (r : ℂ) ^ n * angularMode (n : ℤ) theta := by
  unfold circlePoint angularMode
  rw [mul_pow, ← Complex.exp_nat_mul]
  congr 1
  congr 1
  push_cast
  ring

theorem angularMode_conj (k : ℤ) (theta : ℝ) : conj (angularMode k theta) = angularMode (-k) theta := by
  unfold angularMode
  have he : 2 * ((-k : ℤ) : ℝ) * theta = -(2 * (k : ℝ) * theta) := by push_cast; ring
  rw [he]
  apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]

/-- The displayed coefficients are the literal convergent complex Fourier
series of the actual Poisson kernel. -/
theorem poissonKernel_hasSum_modes (r theta : ℝ) (hr : |r| < 1) :
    HasSum (fun n : ℕ => (r : ℂ) ^ n * (angularMode (n : ℤ) theta + angularMode (-(n : ℤ)) theta) -
      if n = 0 then 1 else 0) (poissonKernel r (2 * theta) : ℂ) := by
  have hh := Complex.ofRealCLM.hasSum (poissonKernel_hasSum r (2 * theta) hr)
  convert hh using 1
  funext n
  change _ = ((2 * (circlePoint r (2 * theta) ^ n).re - if n = 0 then 1 else 0 : ℝ) : ℂ)
  rw [Complex.ofReal_sub, ← Complex.add_conj, circlePoint_pow_angularMode]
  simp only [map_mul, map_pow, Complex.conj_ofReal, angularMode_conj]
  by_cases hn : n = 0 <;> simp only [hn, ↓reduceIte, Complex.ofReal_one, Complex.ofReal_zero] <;> ring

end GeneralizedBulk.Spectral
