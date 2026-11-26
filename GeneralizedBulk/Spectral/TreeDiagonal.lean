import GeneralizedBulk.Spectral.TreeCavity

/-! Uniform bounds and Lipschitz control for the actual diagonal tree Green
function as a rational function of the small cavity root. -/
noncomputable section
namespace GeneralizedBulk.KestenMcKay

def cavityDiagonal (g : ℂ) : ℂ := g / (1 - g ^ 2)

theorem one_sub_sq_norm_lower (g : ℂ) (hg : ‖g‖ ^ 2 ≤ 1 / 2) :
    1 / 2 ≤ ‖1 - g ^ 2‖ := by
  have hh := norm_sub_norm_le (1 : ℂ) (g ^ 2)
  rw [norm_one, norm_pow] at hh
  linarith

theorem one_sub_sq_ne_zero (g : ℂ) (hg : ‖g‖ ^ 2 ≤ 1 / 2) : 1 - g ^ 2 ≠ 0 := by
  have hh := one_sub_sq_norm_lower g hg
  intro hz
  rw [hz, norm_zero] at hh
  norm_num at hh

theorem norm_le_one_of_sq_le_half (g : ℂ) (hg : ‖g‖ ^ 2 ≤ 1 / 2) : ‖g‖ ≤ 1 := by
  nlinarith [norm_nonneg g]

theorem cavityDiagonal_norm_le_two (g : ℂ) (hg : ‖g‖ ^ 2 ≤ 1 / 2) : ‖cavityDiagonal g‖ ≤ 2 := by
  rw [cavityDiagonal, norm_div]
  have hn := one_sub_sq_norm_lower g hg
  calc
    _ ≤ 1 / ‖1 - g ^ 2‖ := div_le_div_of_nonneg_right (norm_le_one_of_sq_le_half g hg) (norm_nonneg _)
    _ ≤ 1 / (1 / 2) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn
    _ = _ := by norm_num

theorem cavityDiagonal_sub (g h : ℂ) (hg : 1 - g ^ 2 ≠ 0) (hh : 1 - h ^ 2 ≠ 0) :
    cavityDiagonal g - cavityDiagonal h = (g - h) * (1 + g * h) / ((1 - g ^ 2) * (1 - h ^ 2)) := by
  unfold cavityDiagonal
  field_simp
  <;> ring

/-- Actual diagonal Green values have a uniform Lipschitz constant on the
small-root region containing all upper-half-plane cavity values. -/
theorem cavityDiagonal_lipschitz (g h : ℂ) (hg : ‖g‖ ^ 2 ≤ 1 / 2) (hh : ‖h‖ ^ 2 ≤ 1 / 2) :
    ‖cavityDiagonal g - cavityDiagonal h‖ ≤ 8 * ‖g - h‖ := by
  have hA := one_sub_sq_norm_lower g hg
  have hB := one_sub_sq_norm_lower h hh
  have hden : 1 / 4 ≤ ‖1 - g ^ 2‖ * ‖1 - h ^ 2‖ := by
    have ht := mul_le_mul hA hB (by norm_num : (0 : ℝ) ≤ 1 / 2) (norm_nonneg _)
    norm_num at ht ⊢
    exact ht
  have hprod : ‖g‖ * ‖h‖ ≤ 1 := by
    have ht := mul_le_mul (norm_le_one_of_sq_le_half g hg) (norm_le_one_of_sq_le_half h hh)
      (norm_nonneg h) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [mul_one] using ht
  have hsum : ‖1 + g * h‖ ≤ 2 := by
    have ht := norm_add_le (1 : ℂ) (g * h)
    rw [norm_one, norm_mul] at ht
    linarith
  rw [cavityDiagonal_sub g h (one_sub_sq_ne_zero g hg) (one_sub_sq_ne_zero h hh), norm_div,
    norm_mul, norm_mul]
  calc
    _ ≤ (‖g - h‖ * 2) / (‖1 - g ^ 2‖ * ‖1 - h ^ 2‖) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ (‖g - h‖ * 2) / (1 / 4) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = _ := by ring

theorem cavityDiagonal_boundary (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    cavityDiagonal (cavityBoundary d E) = diagonalBoundary d E := by
  rw [cavityDiagonal]
  apply (div_eq_iff (one_sub_sq_ne_zero _ (cavityBoundary_norm_sq_le_half d E hd hbulk))).mpr
  exact (diagonalBoundary_cavity_relation d E hd hbulk).symm

end GeneralizedBulk.KestenMcKay
