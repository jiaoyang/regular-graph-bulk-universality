import GeneralizedBulk.Spectral.KestenMcKayAngularLaw
import GeneralizedBulk.Spectral.KestenMcKayQuadrature

/-! The actual physical Kesten–McKay integral is the sine pushforward of
its normalized angular law. -/
noncomputable section
open Set MeasureTheory
namespace GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Spectral

theorem integral_angularLaw_real (d : ℝ) (hd : 3 ≤ d) (f : ℝ → ℝ) :
    (∫ theta, f theta ∂angularLaw d) =
      ∫ theta in -(Real.pi / 2)..Real.pi / 2, angularDensity d theta * f theta := by
  rw [angularLaw, integral_withDensity_eq_integral_toReal_smul
    (continuous_angularDensity d hd).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (angularDensity_nonneg d hd _), smul_eq_mul]
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), ← integral_Icc_eq_integral_Ioc]

theorem integral_rawDensity_change_variables (d : ℝ) (hd : 3 ≤ d) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (-radius d) (radius d))) :
    (∫ x in -radius d..radius d, f x * rawDensity d x) =
      ∫ theta, f (radius d * Real.sin theta) ∂angularLaw d := by
  have hab : -(Real.pi / 2) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hsub : (fun theta => radius d * Real.sin theta) ''
      uIcc (-(Real.pi / 2)) (Real.pi / 2) ⊆ Icc (-radius d) (radius d) := by
    rintro x ⟨theta, ht, rfl⟩
    constructor
    · have hh := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin theta) (radius_pos d hd).le
      simpa only [mul_neg, mul_one] using hh
    · have hh := mul_le_mul_of_nonneg_left (Real.sin_le_one theta) (radius_pos d hd).le
      simpa only [mul_one] using hh
  have hc := intervalIntegral.integral_comp_mul_deriv'
    (a := -(Real.pi / 2)) (b := Real.pi / 2)
    (f := fun theta => radius d * Real.sin theta) (f' := fun theta => radius d * Real.cos theta)
    (g := fun x => f x * rawDensity d x)
    (fun theta _ => (Real.hasDerivAt_sin theta).const_mul (radius d))
    (by fun_prop) ((hf.mul (continuousOn_rawDensity d hd)).mono hsub)
  simp only [Real.sin_neg, Real.sin_pi_div_two, mul_neg, mul_one] at hc
  rw [← hc, integral_angularLaw_real d hd]
  apply intervalIntegral.integral_congr
  intro theta ht
  have hh := rawDensity_sin d hd (by simpa only [uIcc_of_le hab] using ht)
  change (f (radius d * Real.sin theta) * rawDensity d (radius d * Real.sin theta)) *
      (radius d * Real.cos theta) = angularDensity d theta * f (radius d * Real.sin theta)
  rw [mul_assoc, hh, mul_comm]

theorem regularizedLog_eq_logNorm (z : ℂ) (t : ℝ) :
    regularizedLog z.re z.im t = Real.log ‖z - (t : ℂ)‖ := by
  have hn : ‖z - (t : ℂ)‖ ^ 2 = (t - z.re) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, sub_zero]
    ring
  rw [regularizedLog, ← hn, Real.log_pow]
  ring

end GeneralizedBulk.KestenMcKay
