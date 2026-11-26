import GeneralizedBulk.Spectral.KestenMcKayAngular
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! A proved Fourier expansion of the real Poisson kernel, used to compute
the actual Kesten–McKay logarithmic potential. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Spectral

def circlePoint (r theta : ℝ) : ℂ := (r : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)

def poissonKernel (r theta : ℝ) : ℝ :=
  (1 - r ^ 2) / (1 - 2 * r * Real.cos theta + r ^ 2)

theorem circlePoint_norm (r theta : ℝ) : ‖circlePoint r theta‖ = |r| := by
  simp only [circlePoint, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, mul_one]

theorem poissonDenominator_pos (r theta : ℝ) (hr : |r| < 1) :
    0 < 1 - 2 * r * Real.cos theta + r ^ 2 := by
  have hb : |r * Real.cos theta| < 1 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg r) (Real.abs_cos_le_one theta)).trans_lt hr
  have hs : 0 < (1 - |r|) ^ 2 := sq_pos_of_ne_zero (by linarith)
  have hc : r * Real.cos theta ≤ |r| := by
    calc
      _ ≤ |r * Real.cos theta| := le_abs_self _
      _ ≤ |r| := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg r) (Real.abs_cos_le_one theta)
  nlinarith [sq_abs r]

theorem poissonKernel_eq_real_geometric (r theta : ℝ) (hr : |r| < 1) :
    poissonKernel r theta = 2 * ((1 - circlePoint r theta)⁻¹).re - 1 := by
  have hd := (poissonDenominator_pos r theta hr).ne'
  have hn : Complex.normSq (1 - circlePoint r theta) = 1 - 2 * r * Real.cos theta + r ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, circlePoint, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      mul_zero, zero_mul, sub_zero, zero_add]
    nlinarith [Real.sin_sq_add_cos_sq theta]
  rw [Complex.inv_re, hn]
  simp only [Complex.sub_re, Complex.one_re, circlePoint, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, zero_mul, sub_zero]
  unfold poissonKernel
  field_simp [hd]
  <;> ring

/-- The Fourier expansion is derived from the genuine geometric series. -/
theorem poissonKernel_hasSum (r theta : ℝ) (hr : |r| < 1) :
    HasSum (fun n : ℕ => 2 * (circlePoint r theta ^ n).re - if n = 0 then 1 else 0)
      (poissonKernel r theta) := by
  have hh := (Complex.reCLM.hasSum (hasSum_geometric_of_norm_lt_one
    (by simpa only [circlePoint_norm] using hr : ‖circlePoint r theta‖ < 1))).mul_left 2
  have hd : HasSum (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) 1 := hasSum_ite_eq 0 1
  rw [poissonKernel_eq_real_geometric r theta hr]
  exact hh.sub hd

end GeneralizedBulk.Spectral
