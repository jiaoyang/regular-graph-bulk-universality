import GeneralizedBulk.Entropy.GaussianMixtureEntropy

/-! Uniform pointwise logarithmic continuity for actual Gaussian mixtures. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite Mehler
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

theorem abs_log_weighted_sum_sub_le (weight f g : S → ℝ) (hw : ∀ s, 0 ≤ weight s)
    (hnorm : ∑ s, weight s = 1) (hf : ∀ s, 0 < f s) (hg : ∀ s, 0 < g s)
    (R : ℝ) (hbound : ∀ s, |Real.log (f s) - Real.log (g s)| ≤ R) :
    |Real.log (∑ s, weight s * f s) - Real.log (∑ s, weight s * g s)| ≤ R := by
  let G := ∑ s, weight s * g s
  have hG : 0 < G := positive_weighted_sum weight g hw hnorm hg
  have hF : 0 < ∑ s, weight s * f s := positive_weighted_sum weight f hw hnorm hf
  let w := fun s => weight s * g s / G
  have hwp (s) : 0 ≤ w s := div_nonneg (mul_nonneg (hw s) (hg s).le) hG.le
  have hwn : ∑ s, w s = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    exact div_self hG.ne'
  have hb (s) : |Real.log (f s / g s)| ≤ R := by
    rw [Real.log_div (hf s).ne' (hg s).ne']
    exact hbound s
  have hh := abs_log_weighted_sum_le w (fun s => f s / g s) hwp hwn (fun s => div_pos (hf s) (hg s)) R hb
  have he : (∑ s, w s * (f s / g s)) = (∑ s, weight s * f s) / G := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s hs
    dsimp [w]
    field_simp [hG.ne', (hg s).ne']
    <;> ring
  rw [he, Real.log_div hF.ne' hG.ne'] at hh
  exact hh

theorem coordinateL1_neg (x : I → ℝ) : coordinateL1 (-x) = coordinateL1 x := by
  simp only [coordinateL1, Pi.neg_apply, abs_neg]

theorem sum_square_difference_bound (x y : I → ℝ) :
    |(∑ i, x i ^ 2) - ∑ i, y i ^ 2| ≤ coordinateL1 (x - y) * (coordinateL1 x + coordinateL1 y) := by
  have he : (∑ i, x i ^ 2) - ∑ i, y i ^ 2 = ∑ i, (x i - y i) * (x i + y i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  have h := abs_cross_le_coordinateL1 (x + y) (x - y)
  simp only [Pi.add_apply, Pi.sub_apply] at h
  have hp := mul_le_mul_of_nonneg_left (coordinateL1_add_le x y) (coordinateL1_nonneg (x-y))
  calc
    _ ≤ coordinateL1 (x + y) * coordinateL1 (x - y) := h
    _ ≤ _ := by nlinarith

theorem abs_log_affineGaussianPDF_sub_same_matrix (mean : I → ℝ) (M : Matrix I I ℝ)
    (hM : M.det ≠ 0) (x y : I → ℝ) :
    |Real.log (affineGaussianPDF mean M x) - Real.log (affineGaussianPDF mean M y)| ≤
      (matrixEntryL1 M⁻¹ ^ 2 / 2) * coordinateL1 (x - y) *
        (coordinateL1 x + coordinateL1 y + 2 * coordinateL1 mean) := by
  rw [log_affineGaussianPDF mean M hM x, log_affineGaussianPDF mean M hM y]
  have he : (-Real.log |M.det| - (Fintype.card I : ℝ) / 2 * Real.log (2 * Real.pi) -
      (∑ i, (M⁻¹.mulVec (x - mean) i) ^ 2) / 2) -
      (-Real.log |M.det| - (Fintype.card I : ℝ) / 2 * Real.log (2 * Real.pi) -
      (∑ i, (M⁻¹.mulVec (y - mean) i) ^ 2) / 2) =
      -((∑ i, (M⁻¹.mulVec (x - mean) i) ^ 2) - ∑ i, (M⁻¹.mulVec (y - mean) i) ^ 2) / 2 := by ring
  rw [he, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := sum_square_difference_bound (M⁻¹.mulVec (x - mean)) (M⁻¹.mulVec (y - mean))
  rw [← Matrix.mulVec_sub, sub_sub_sub_cancel_right] at hh
  have hdiff := coordinateL1_mulVec_le M⁻¹ (x-y)
  have hx := (coordinateL1_mulVec_le M⁻¹ (x-mean)).trans
    (mul_le_mul_of_nonneg_left (coordinateL1_sub_le x mean) (matrixEntryL1_nonneg _))
  have hy := (coordinateL1_mulVec_le M⁻¹ (y-mean)).trans
    (mul_le_mul_of_nonneg_left (coordinateL1_sub_le y mean) (matrixEntryL1_nonneg _))
  have hprod := mul_le_mul hdiff (add_le_add hx hy)
    (add_nonneg (coordinateL1_nonneg _) (coordinateL1_nonneg _))
    (mul_nonneg (matrixEntryL1_nonneg _) (coordinateL1_nonneg _))
  nlinarith [hh.trans hprod]

theorem abs_log_gaussianMixturePDF_sub (weight : S → ℝ) (mean : S → I → ℝ)
    (M : S → Matrix I I ℝ) (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1)
    (hM : ∀ s, (M s).det ≠ 0) (B L : ℝ) (hB : ∀ s, coordinateL1 (mean s) ≤ B)
    (hL : ∀ s, matrixEntryL1 (M s)⁻¹ ≤ L) (x y : I → ℝ) :
    |Real.log (gaussianMixturePDF weight mean M x) - Real.log (gaussianMixturePDF weight mean M y)| ≤
      (L ^ 2 / 2) * coordinateL1 (x-y) * (coordinateL1 x + coordinateL1 y + 2 * B) := by
  apply abs_log_weighted_sum_sub_le weight _ _ hw hnorm
    (fun s => affineGaussianPDF_pos _ _ (hM s) x) (fun s => affineGaussianPDF_pos _ _ (hM s) y)
  intro s
  refine (abs_log_affineGaussianPDF_sub_same_matrix (mean s) (M s) (hM s) x y).trans ?_
  have hL0 : 0 ≤ L := (matrixEntryL1_nonneg (M s)⁻¹).trans (hL s)
  have hB0 : 0 ≤ B := (coordinateL1_nonneg (mean s)).trans (hB s)
  have hs := pow_le_pow_left₀ (matrixEntryL1_nonneg (M s)⁻¹) (hL s) 2
  have hleft := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hs (by norm_num : (0:ℝ)≤2))
    (coordinateL1_nonneg (x-y))
  have hright : coordinateL1 x + coordinateL1 y + 2 * coordinateL1 (mean s) ≤
      coordinateL1 x + coordinateL1 y + 2 * B := by linarith [hB s]
  exact mul_le_mul hleft hright
    (by nlinarith [coordinateL1_nonneg x, coordinateL1_nonneg y, coordinateL1_nonneg (mean s)])
    (mul_nonneg (div_nonneg (sq_nonneg L) (by norm_num)) (coordinateL1_nonneg (x-y)))

end GeneralizedBulk.Entropy
