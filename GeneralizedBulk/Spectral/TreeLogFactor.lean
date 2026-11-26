import GeneralizedBulk.Spectral.TreeGreenBoundary
import GeneralizedBulk.Spectral.PoissonKernel
import GeneralizedBulk.Spectral.KestenMcKayDensity

/-! Algebraic factorization behind the actual Kesten–McKay logarithmic
potential, parameterized by the small cavity root. -/
noncomputable section
namespace GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Spectral

def treeSpectralPoint (d : ℝ) (g : ℂ) : ℂ := -g⁻¹ - ((d - 1 : ℝ) : ℂ) * g

def treeLogParameter (d : ℝ) (g : ℂ) : ℂ := Complex.I * (Real.sqrt (d - 1) : ℂ) * g

theorem circlePoint_one_mul_neg (theta : ℝ) : circlePoint 1 theta * circlePoint 1 (-theta) = 1 := by
  simp only [circlePoint, Complex.ofReal_one, one_mul, ← Complex.exp_add]
  convert Complex.exp_zero using 1
  congr 1
  push_cast
  ring

theorem circlePoint_one_neg_sub (theta : ℝ) :
    circlePoint 1 (-theta) - circlePoint 1 theta = -2 * Complex.I * (Real.sin theta : ℂ) := by
  have he : Complex.exp (((-theta : ℝ) : ℂ) * Complex.I) - Complex.exp ((theta : ℂ) * Complex.I) =
      (((-2 * Real.sin theta : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp only [Complex.sub_re, Complex.sub_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  simp only [circlePoint, Complex.ofReal_one, one_mul]
  rw [he]
  push_cast
  ring

theorem treeLogParameter_sq (d : ℝ) (hd : 3 ≤ d) (g : ℂ) :
    treeLogParameter d g ^ 2 = -((d - 1 : ℝ) : ℂ) * g ^ 2 := by
  have hs : ((Real.sqrt (d - 1) : ℝ) : ℂ) ^ 2 = ((d - 1 : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ d - 1)
  simp only [treeLogParameter, mul_pow, Complex.I_sq, hs]
  ring

theorem treeLogFactor_product (d : ℝ) (hd : 3 ≤ d) (g : ℂ) (theta : ℝ) :
    (1 - treeLogParameter d g * circlePoint 1 theta) *
      (1 + treeLogParameter d g * circlePoint 1 (-theta)) =
      1 + ((d - 1 : ℝ) : ℂ) * g ^ 2 + (radius d : ℂ) * g * (Real.sin theta : ℂ) := by
  calc
    _ = 1 + treeLogParameter d g * (circlePoint 1 (-theta) - circlePoint 1 theta) -
        treeLogParameter d g ^ 2 * (circlePoint 1 theta * circlePoint 1 (-theta)) := by ring
    _ = _ := by
      rw [circlePoint_one_neg_sub, treeLogParameter_sq d hd, circlePoint_one_mul_neg]
      dsimp [treeLogParameter, radius]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring

/-- Literal spectral factorization; only the nonzero cavity parameter is used. -/
theorem treeSpectralPoint_factor (d : ℝ) (hd : 3 ≤ d) (g : ℂ) (hg : g ≠ 0) (theta : ℝ) :
    treeSpectralPoint d g - ((radius d * Real.sin theta : ℝ) : ℂ) =
      -g⁻¹ * ((1 - treeLogParameter d g * circlePoint 1 theta) *
        (1 + treeLogParameter d g * circlePoint 1 (-theta))) := by
  rw [treeLogFactor_product d hd]
  unfold treeSpectralPoint
  push_cast
  field_simp
  <;> ring

end GeneralizedBulk.KestenMcKay
