import GeneralizedBulk.Spectral.KestenMcKayAngular
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The literal Kesten–McKay density and its normalization by a proved
trigonometric change of variables. -/
noncomputable section
open scoped Topology
open Set MeasureTheory
namespace GeneralizedBulk.KestenMcKay

def radius (d : ℝ) : ℝ := 2 * Real.sqrt (d - 1)

def rawDensity (d x : ℝ) : ℝ :=
  d * Real.sqrt (4 * (d - 1) - x ^ 2) / (2 * Real.pi * (d ^ 2 - x ^ 2))

theorem radius_pos (d : ℝ) (hd : 3 ≤ d) : 0 < radius d := by
  dsimp [radius]
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (by linarith))

theorem radius_sq (d : ℝ) (hd : 3 ≤ d) : radius d ^ 2 = 4 * (d - 1) := by
  dsimp [radius]
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  ring

theorem rawDenominator_pos (d : ℝ) (hd : 3 ≤ d) {x : ℝ}
    (hx : x ∈ Icc (-radius d) (radius d)) : 0 < d ^ 2 - x ^ 2 := by
  have hs : x ^ 2 ≤ radius d ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) (radius_pos d hd).le).mpr (abs_le.mpr hx)
  rw [radius_sq d hd] at hs
  nlinarith [sq_nonneg (d - 3)]

theorem continuousOn_rawDensity (d : ℝ) (hd : 3 ≤ d) :
    ContinuousOn (rawDensity d) (Icc (-radius d) (radius d)) := by
  unfold rawDensity
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (rawDenominator_pos d hd hx).ne'

theorem rawDensity_nonneg (d : ℝ) (hd : 3 ≤ d) {x : ℝ}
    (hx : x ∈ Icc (-radius d) (radius d)) : 0 ≤ rawDensity d x := by
  exact div_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) (rawDenominator_pos d hd hx)).le

theorem rawDensity_sin (d : ℝ) (hd : 3 ≤ d) {theta : ℝ}
    (ht : theta ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    rawDensity d (radius d * Real.sin theta) * (radius d * Real.cos theta) = angularDensity d theta := by
  have hcos : 0 ≤ Real.cos theta := Real.cos_nonneg_of_mem_Icc ht
  have hr := radius_pos d hd
  have hs : 4 * (d - 1) - (radius d * Real.sin theta) ^ 2 =
      (radius d * Real.cos theta) ^ 2 := by
    rw [mul_pow, mul_pow, radius_sq d hd]
    nlinarith [Real.sin_sq_add_cos_sq theta]
  unfold rawDensity angularDensity
  rw [hs, Real.sqrt_sq (mul_nonneg hr.le hcos)]
  simp only [mul_pow, radius_sq d hd]
  field_simp [Real.pi_ne_zero, (angularDenominator_pos d hd theta).ne']
  ring_nf
  simp only [radius_sq d hd]
  ring

/-- The displayed density integrates to one on the actual spectral support. -/
theorem integral_rawDensity (d : ℝ) (hd : 3 ≤ d) :
    (∫ x in -radius d..radius d, rawDensity d x) = 1 := by
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
    (g := rawDensity d)
    (fun theta _ => (Real.hasDerivAt_sin theta).const_mul (radius d))
    (by fun_prop) ((continuousOn_rawDensity d hd).mono hsub)
  simp only [Real.sin_neg, Real.sin_pi_div_two, mul_neg, mul_one] at hc
  rw [← hc]
  calc
    _ = ∫ theta in -(Real.pi / 2)..Real.pi / 2, angularDensity d theta := by
      apply intervalIntegral.integral_congr
      intro theta ht
      exact rawDensity_sin d hd (by simpa only [uIcc_of_le hab] using ht)
    _ = 1 := integral_angularDensity d hd

end GeneralizedBulk.KestenMcKay
