import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! A quantitative positive radial parameter with prescribed imaginary height. -/
noncomputable section
namespace GeneralizedBulk.KestenMcKay

def radialContraction (h : ℝ) : ℝ := 2 / (Real.sqrt (h ^ 2 + 4) + h)

theorem radialContraction_spec (h : ℝ) (hh : 0 ≤ h) :
    0 < radialContraction h ∧ radialContraction h ≤ 1 ∧
      radialContraction h ^ 2 + h * radialContraction h = 1 := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ h ^ 2 + 4)
  have hn := Real.sqrt_nonneg (h ^ 2 + 4)
  have ht : 2 ≤ Real.sqrt (h ^ 2 + 4) := by nlinarith [sq_nonneg h]
  have hd : 0 < Real.sqrt (h ^ 2 + 4) + h := by linarith
  refine ⟨div_pos (by norm_num) hd, ?_, ?_⟩
  · unfold radialContraction
    apply (div_le_one hd).mpr
    linarith
  · unfold radialContraction
    field_simp
    nlinarith

theorem radialContraction_ge_half (h : ℝ) (hh : 0 ≤ h) (hh' : h ≤ 1) :
    1 / 2 ≤ radialContraction h := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ h ^ 2 + 4)
  have hn := Real.sqrt_nonneg (h ^ 2 + 4)
  have ht : Real.sqrt (h ^ 2 + 4) + h ≤ 4 := by nlinarith
  have hd : 0 < Real.sqrt (h ^ 2 + 4) + h := by positivity
  unfold radialContraction
  apply (le_div_iff₀ hd).mpr
  linarith

theorem radialContraction_reciprocal (h : ℝ) (hh : 0 ≤ h) :
    (radialContraction h)⁻¹ - radialContraction h = h := by
  obtain ⟨hp, hu, he⟩ := radialContraction_spec h hh
  field_simp
  nlinarith [he]

theorem one_sub_radialContraction_le (h : ℝ) (hh : 0 ≤ h) :
    1 - radialContraction h ≤ h := by
  obtain ⟨hp, hu, he⟩ := radialContraction_spec h hh
  have hf : 0 < 1 + radialContraction h := by linarith
  have hid : (1 - radialContraction h) * (1 + radialContraction h) = h * radialContraction h := by nlinarith
  have hb : h * radialContraction h ≤ h * (1 + radialContraction h) := by nlinarith
  exact (mul_le_mul_right hf).mp (hid.le.trans hb)

theorem radialContraction_lt_one (h : ℝ) (hh : 0 < h) : radialContraction h < 1 := by
  obtain ⟨hp, hu, he⟩ := radialContraction_spec h hh.le
  by_contra hn
  have hr : radialContraction h = 1 := le_antisymm hu (le_of_not_gt hn)
  rw [hr] at he
  nlinarith

end GeneralizedBulk.KestenMcKay
