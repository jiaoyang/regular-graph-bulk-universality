import GeneralizedBulk.Spectral.KestenMcKayPoisson
import GeneralizedBulk.Spectral.PoissonMoments

/-! Exact Fourier moments of the actual angular Kesten–McKay density. -/
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
namespace GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Spectral

theorem integral_angularDensity_mode (d : ℝ) (hd : 3 ≤ d) (k : ℕ) :
    (∫ theta in -(Real.pi / 2)..Real.pi / 2,
      (angularDensity d theta : ℂ) * angularMode k theta) =
      if k = 0 then 1 else -((d - 2 : ℝ) : ℂ) / 2 * ((-1 / (d - 1) : ℝ) : ℂ) ^ k := by
  have hf : (fun theta => (angularDensity d theta : ℂ) * angularMode k theta) =
      fun theta => ((d : ℂ) / (2 * (Real.pi : ℂ))) * angularMode k theta -
        (((d - 2 : ℝ) : ℂ) / (2 * (Real.pi : ℂ))) *
          ((poissonKernel (-1 / (d - 1)) (2 * theta) : ℂ) * angularMode k theta) := by
    funext theta
    rw [angularDensity_eq_poisson d hd theta]
    push_cast
    ring
  have hpcont : Continuous (fun theta => (poissonKernel (-1 / (d - 1)) (2 * theta) : ℂ) * angularMode k theta) := by
    have hc : Continuous (fun theta => poissonKernel (-1 / (d - 1)) (2 * theta)) := by
      unfold poissonKernel
      fun_prop (disch := intro theta; exact (poissonDenominator_pos _ _ (angularPoisson_parameter d hd)).ne')
    exact (Complex.continuous_ofReal.comp hc).mul (continuous_angularMode _)
  rw [hf, intervalIntegral.integral_sub
    ((continuous_const.mul (continuous_angularMode _)).intervalIntegrable _ _)
    ((continuous_const.mul hpcont).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_angularMode, integral_poissonKernel_mode _ (angularPoisson_parameter d hd)]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases hk : k = 0
  · subst k
    simp only [Int.ofNat_zero, ↓reduceIte, pow_zero, mul_one]
    field_simp [hpi]
    push_cast
    ring
  · have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk
    rw [if_neg hk, if_neg hk', mul_zero, zero_sub]
    have hcoef : (((d - 2 : ℝ) : ℂ) / (2 * (Real.pi : ℂ))) * (Real.pi : ℂ) = ((d - 2 : ℝ) : ℂ) / 2 := by
      field_simp [hpi]
      <;> ring
    rw [← mul_assoc, hcoef]
    ring

end GeneralizedBulk.KestenMcKay
