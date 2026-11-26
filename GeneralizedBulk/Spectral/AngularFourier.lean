import GeneralizedBulk.Spectral.PoissonKernel
import Mathlib.Analysis.SpecialFunctions.Integrals

/-! Literal Fourier modes and orthogonality on the half-angle interval used
for the Kesten–McKay law. -/
noncomputable section
namespace GeneralizedBulk.Spectral

def angularMode (k : ℤ) (theta : ℝ) : ℂ :=
  Complex.exp (((2 * (k : ℝ) * theta : ℝ) : ℂ) * Complex.I)

theorem angularMode_norm (k : ℤ) (theta : ℝ) : ‖angularMode k theta‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem angularMode_add (k l : ℤ) (theta : ℝ) :
    angularMode (k + l) theta = angularMode k theta * angularMode l theta := by
  unfold angularMode
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem angularMode_zero (theta : ℝ) : angularMode 0 theta = 1 := by simp [angularMode]

theorem continuous_angularMode (k : ℤ) : Continuous (angularMode k) := by unfold angularMode; fun_prop

/-- Exact Fourier orthogonality for the actual angular interval. -/
theorem integral_angularMode (k : ℤ) :
    (∫ theta in -(Real.pi / 2)..Real.pi / 2, angularMode k theta) =
      if k = 0 then (Real.pi : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simp only [angularMode_zero, ↓reduceIte, intervalIntegral.integral_const]
    simp only [Complex.real_smul, mul_one]
    congr 1
    ring
  · rw [if_neg hk]
    let c : ℂ := (2 * (k : ℂ)) * Complex.I
    have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast hk)) Complex.I_ne_zero
    have hf : (fun theta => angularMode k theta) = fun theta : ℝ => Complex.exp (c * theta) := by
      funext theta
      unfold angularMode c
      congr 1
      push_cast
      ring
    rw [hf, integral_exp_mul_complex hc]
    have hupper : c * (Real.pi / 2 : ℝ) = (((k : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I := by
      dsimp [c]; push_cast; ring
    have hlower : c * (-(Real.pi / 2) : ℝ) = ((-((k : ℝ) * Real.pi) : ℝ) : ℂ) * Complex.I := by
      dsimp [c]; push_cast; ring
    rw [hupper, hlower]
    have he : Complex.exp (((-((k : ℝ) * Real.pi) : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((((k : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Real.cos_neg, Real.sin_neg, Real.sin_int_mul_pi, neg_zero]
    rw [he, sub_self, zero_div]

end GeneralizedBulk.Spectral
