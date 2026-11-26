import GeneralizedBulk.Spectral.TreeStarHeight

/-! Compact-bulk uniform tree Green convergence and normalization constants. -/
noncomputable section
open Set
namespace GeneralizedBulk.KestenMcKay

theorem bulkHeightScale_uniform_floor (d : ℝ) (hd : 3 ≤ d) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K, E ^ 2 < 4 * (d - 1)) :
    ∃ b : ℝ, 0 < b ∧ ∀ E ∈ K, b ≤ bulkHeightScale d E := by
  by_cases hne : K.Nonempty
  · obtain ⟨E0, hE0, hmin⟩ := hK.exists_isMinOn hne (continuous_bulkHeightScale d hd).continuousOn
    exact ⟨bulkHeightScale d E0, bulkHeightScale_pos d E0 hd (hbulk E0 hE0), fun E hE => hmin hE⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro E hE
    exact (hne ⟨E, hE⟩).elim

theorem treeGreenStar_height_uniform (d : ℕ) (hd : 3 ≤ (d : ℝ)) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K, E ^ 2 < 4 * ((d : ℝ) - 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ E ∈ K, ∀ eta : ℝ, 0 < eta → ∀ j l : Fin (d + 1),
      ‖treeGreenStar d hd ((E : ℂ) + (eta : ℂ) * Complex.I) j l - boundaryStar d E j l‖ ≤ C * eta := by
  obtain ⟨b, hb, hfloor⟩ := bulkHeightScale_uniform_floor d hd K hK hbulk
  refine ⟨12 / b, by positivity, ?_⟩
  intro E hE eta heta j l
  have hz : 0 < ((E : ℂ) + (eta : ℂ) * Complex.I).im := by simpa using heta
  have hh := treeGreenStar_boundary_bound d hd E (hbulk E hE) _ hz j l
  have hn : ‖(E : ℂ) + (eta : ℂ) * Complex.I - (E : ℂ)‖ = eta := by
    rw [show (E : ℂ) + (eta : ℂ) * Complex.I - (E : ℂ) = (eta : ℂ) * Complex.I by ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_pos heta]
  rw [hn] at hh
  exact hh.trans (by
    convert div_le_div_of_nonneg_left (by positivity : 0 ≤ 12 * eta) hb (hfloor E hE) using 1 <;> ring)

theorem diagonalBoundary_im_heightScale (d E : ℝ) (hd : 3 ≤ d) :
    (diagonalBoundary d E).im = d * bulkHeightScale d E / (d ^ 2 - E ^ 2) := by
  rw [bulkHeightScale_eq d E hd]
  dsimp [diagonalBoundary]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem diagonalBoundary_im_lower (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    bulkHeightScale d E / d ≤ (diagonalBoundary d E).im := by
  have hdpos : 0 < d := by linarith
  have hb := bulkHeightScale_pos d E hd hbulk
  have hden := bulk_denominator_pos d E hd hbulk
  rw [diagonalBoundary_im_heightScale d E hd]
  have hh := div_le_div_of_nonneg_left (mul_nonneg hdpos.le hb.le) hden (by nlinarith [sq_nonneg E] : d ^ 2 - E ^ 2 ≤ d ^ 2)
  convert hh using 1
  field_simp
  <;> ring

theorem diagonalBoundary_im_le_two (d E : ℝ) (hd : 3 ≤ d) (hbulk : E ^ 2 < 4 * (d - 1)) :
    (diagonalBoundary d E).im ≤ 2 := by
  have hn := cavityDiagonal_norm_le_two (cavityBoundary d E) (cavityBoundary_norm_sq_le_half d E hd hbulk)
  rw [cavityDiagonal_boundary d E hd hbulk] at hn
  exact (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hn)

theorem diagonalBoundary_im_uniform (d : ℝ) (hd : 3 ≤ d) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K, E ^ 2 < 4 * (d - 1)) :
    ∃ c : ℝ, 0 < c ∧ ∀ E ∈ K, c ≤ (diagonalBoundary d E).im ∧ (diagonalBoundary d E).im ≤ 2 := by
  obtain ⟨b, hb, hfloor⟩ := bulkHeightScale_uniform_floor d hd K hK hbulk
  have hdpos : 0 < d := by linarith
  refine ⟨b / d, div_pos hb hdpos, ?_⟩
  intro E hE
  exact ⟨(div_le_div_of_nonneg_right (hfloor E hE) hdpos.le).trans (diagonalBoundary_im_lower d E hd (hbulk E hE)),
    diagonalBoundary_im_le_two d E hd (hbulk E hE)⟩

end GeneralizedBulk.KestenMcKay
