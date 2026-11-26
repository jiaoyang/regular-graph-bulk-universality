import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The Kesten–McKay density in angular coordinates, with an explicit
antiderivative. This is deterministic calculus independent of HY. -/
noncomputable section
open scoped Topology
open Filter Set MeasureTheory
namespace GeneralizedBulk.KestenMcKay

def angularDensity (d theta : ℝ) : ℝ :=
  2 * d * (d - 1) * Real.cos theta ^ 2 /
    (Real.pi * (d ^ 2 - 4 * (d - 1) * Real.sin theta ^ 2))

def angularPrimitive (d theta : ℝ) : ℝ :=
  d * theta / (2 * Real.pi) - (d - 2) / (2 * Real.pi) *
    Real.arctan ((d - 2) / d * Real.tan theta)

theorem angularDenominator_pos (d : ℝ) (hd : 3 ≤ d) (theta : ℝ) :
    0 < d ^ 2 - 4 * (d - 1) * Real.sin theta ^ 2 := by
  have hs : Real.sin theta ^ 2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq theta, sq_nonneg (Real.cos theta)]
  have hm := mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ 4 * (d - 1))
  nlinarith [sq_nonneg (d - 3)]

theorem continuous_angularDensity (d : ℝ) (hd : 3 ≤ d) : Continuous (angularDensity d) := by
  unfold angularDensity
  fun_prop (disch := intro theta; exact mul_ne_zero Real.pi_ne_zero (angularDenominator_pos d hd theta).ne')

theorem angularPrimitive_hasDerivAt (d : ℝ) (hd : 3 ≤ d) (theta : ℝ)
    (hcos : Real.cos theta ≠ 0) : HasDerivAt (angularPrimitive d) (angularDensity d theta) theta := by
  have hd0 : d ≠ 0 := by linarith
  have hden := (angularDenominator_pos d hd theta).ne'
  have hAt := ((Real.hasDerivAt_tan hcos).const_mul ((d - 2) / d)).arctan
  have hh := ((hasDerivAt_id theta).const_mul (d / (2 * Real.pi))).sub
    (hAt.const_mul ((d - 2) / (2 * Real.pi)))
  convert hh using 1
  · funext t
    dsimp [angularPrimitive]
    ring
  · dsimp [angularDensity]
    rw [Real.tan_eq_sin_div_cos]
    have hs : Real.sin theta ^ 2 = 1 - Real.cos theta ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq theta]
    have htan : 1 + ((d - 2) / d * (Real.sin theta / Real.cos theta)) ^ 2 =
        (d ^ 2 - 4 * (d - 1) * Real.sin theta ^ 2) / (d ^ 2 * Real.cos theta ^ 2) := by
      field_simp [hcos, hd0]
      ring_nf
      simp only [hs]
      ring
    rw [htan]
    simp only [hs] at hden ⊢
    field_simp [hcos, hd0, Real.pi_ne_zero, hden]
    <;> ring

theorem angularPrimitive_tendsto_upper (d : ℝ) (hd : 3 ≤ d) :
    Tendsto (angularPrimitive d) (𝓝[<] (Real.pi / 2)) (𝓝 (1 / 2 : ℝ)) := by
  have hk : 0 < (d - 2) / d := div_pos (by linarith) (by linarith)
  have ht : Tendsto (fun theta => (d - 2) / d * Real.tan theta)
      (𝓝[<] (Real.pi / 2)) atTop :=
    (tendsto_const_mul_atTop_of_pos hk).mpr Real.tendsto_tan_pi_div_two
  have ha := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp ht
  have hi : Tendsto (fun theta : ℝ => theta) (𝓝[<] (Real.pi / 2)) (𝓝 (Real.pi / 2)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hh := ((hi.const_mul d).div_const (2 * Real.pi)).sub
    (ha.const_mul ((d - 2) / (2 * Real.pi)))
  have hv : d * (Real.pi / 2) / (2 * Real.pi) - (d - 2) / (2 * Real.pi) * (Real.pi / 2) = (1 / 2 : ℝ) := by
    field_simp
    <;> ring
  rw [hv] at hh
  exact hh

theorem angularPrimitive_tendsto_lower (d : ℝ) (hd : 3 ≤ d) :
    Tendsto (angularPrimitive d) (𝓝[>] (-(Real.pi / 2))) (𝓝 (-1 / 2 : ℝ)) := by
  have hk : 0 < (d - 2) / d := div_pos (by linarith) (by linarith)
  have ht : Tendsto (fun theta => (d - 2) / d * Real.tan theta)
      (𝓝[>] (-(Real.pi / 2))) atBot :=
    (tendsto_const_mul_atBot_of_pos hk).mpr Real.tendsto_tan_neg_pi_div_two
  have ha := (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp ht
  have hi : Tendsto (fun theta : ℝ => theta) (𝓝[>] (-(Real.pi / 2))) (𝓝 (-(Real.pi / 2))) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hh := ((hi.const_mul d).div_const (2 * Real.pi)).sub
    (ha.const_mul ((d - 2) / (2 * Real.pi)))
  have hv : d * (-(Real.pi / 2)) / (2 * Real.pi) - (d - 2) / (2 * Real.pi) * (-(Real.pi / 2)) = (-1 / 2 : ℝ) := by
    field_simp
    <;> ring
  rw [hv] at hh
  exact hh

/-- The actual angular Kesten–McKay density has total mass one. -/
theorem integral_angularDensity (d : ℝ) (hd : 3 ≤ d) :
    (∫ theta in -(Real.pi / 2)..Real.pi / 2, angularDensity d theta) = 1 := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by linarith [Real.pi_pos] : -(Real.pi / 2) < Real.pi / 2)
    (fun theta ht => angularPrimitive_hasDerivAt d hd theta (Real.cos_pos_of_mem_Ioo ht).ne')
    ((continuous_angularDensity d hd).intervalIntegrable _ _)
    (angularPrimitive_tendsto_lower d hd) (angularPrimitive_tendsto_upper d hd)
  norm_num at hh ⊢
  exact hh

end GeneralizedBulk.KestenMcKay
