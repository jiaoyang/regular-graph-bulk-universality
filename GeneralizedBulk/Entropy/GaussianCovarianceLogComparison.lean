import GeneralizedBulk.Entropy.GaussianLogContinuity

/-! Pointwise covariance stability of positive Gaussian-mixture densities. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite Mehler
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

theorem abs_log_affineGaussianPDF_sub_matrices (mean : I → ℝ) (M A : Matrix I I ℝ)
    (hM : M.det ≠ 0) (hA : A.det ≠ 0) (x : I → ℝ) :
    |Real.log (affineGaussianPDF mean M x) - Real.log (affineGaussianPDF mean A x)| ≤
      |Real.log (|M.det|) - Real.log (|A.det|)| +
        (matrixEntryL1 (M⁻¹ - A⁻¹) / 2) * (matrixEntryL1 M⁻¹ + matrixEntryL1 A⁻¹) * coordinateL1 (x - mean) ^ 2 := by
  rw [log_affineGaussianPDF mean M hM x, log_affineGaussianPDF mean A hA x]
  have he : (-Real.log (|M.det|) - (Fintype.card I : ℝ) / 2 * Real.log (2 * Real.pi) -
      (∑ i, (M⁻¹.mulVec (x - mean) i) ^ 2) / 2) -
      (-Real.log (|A.det|) - (Fintype.card I : ℝ) / 2 * Real.log (2 * Real.pi) -
      (∑ i, (A⁻¹.mulVec (x - mean) i) ^ 2) / 2) =
      -(Real.log (|M.det|) - Real.log (|A.det|)) -
        ((∑ i, (M⁻¹.mulVec (x - mean) i) ^ 2) - ∑ i, (A⁻¹.mulVec (x - mean) i) ^ 2) / 2 := by ring
  rw [he]
  have hh := sum_square_difference_bound (M⁻¹.mulVec (x - mean)) (A⁻¹.mulVec (x - mean))
  rw [← Matrix.sub_mulVec] at hh
  have hd := coordinateL1_mulVec_le (M⁻¹ - A⁻¹) (x-mean)
  have hs := add_le_add (coordinateL1_mulVec_le M⁻¹ (x-mean)) (coordinateL1_mulVec_le A⁻¹ (x-mean))
  have hm := mul_le_mul hd hs (add_nonneg (coordinateL1_nonneg _) (coordinateL1_nonneg _))
    (mul_nonneg (matrixEntryL1_nonneg _) (coordinateL1_nonneg _))
  calc
    _ ≤ |-(Real.log (|M.det|) - Real.log (|A.det|))| +
        |((∑ i, (M⁻¹.mulVec (x - mean) i) ^ 2) - ∑ i, (A⁻¹.mulVec (x - mean) i) ^ 2) / 2| := abs_sub _ _
    _ = |Real.log (|M.det|) - Real.log (|A.det|)| +
        |(∑ i, (M⁻¹.mulVec (x - mean) i) ^ 2) - ∑ i, (A⁻¹.mulVec (x - mean) i) ^ 2| / 2 := by
      rw [abs_neg, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    _ ≤ _ := by nlinarith [hh.trans hm]

theorem gaussianMixture_covariance_log_comparison
    (weight : S → ℝ) (mean : S → I → ℝ) (M A : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1)
    (hM : ∀ s, (M s).det ≠ 0) (hA : ∀ s, (A s).det ≠ 0)
    (B L Dlog Dinv : ℝ) (hL0 : 0 ≤ L) (hDinv : 0 ≤ Dinv)
    (hB : ∀ s, coordinateL1 (mean s) ≤ B)
    (hLM : ∀ s, matrixEntryL1 (M s)⁻¹ ≤ L) (hLA : ∀ s, matrixEntryL1 (A s)⁻¹ ≤ L)
    (hlog : ∀ s, |Real.log (|(M s).det|) - Real.log (|(A s).det|)| ≤ Dlog)
    (hinv : ∀ s, matrixEntryL1 ((M s)⁻¹ - (A s)⁻¹) ≤ Dinv) (x : I → ℝ) :
    |Real.log (gaussianMixturePDF weight mean M x) - Real.log (gaussianMixturePDF weight mean A x)| ≤
      Dlog + Dinv * L * (coordinateL1 x + B) ^ 2 := by
  apply abs_log_weighted_sum_sub_le weight _ _ hw hnorm
    (fun s => affineGaussianPDF_pos _ _ (hM s) x) (fun s => affineGaussianPDF_pos _ _ (hA s) x)
  intro s
  have hsq := pow_le_pow_left₀ (coordinateL1_nonneg (x-mean s))
    ((coordinateL1_sub_le x (mean s)).trans (add_le_add_left (hB s) _)) 2
  have hcoeff : (matrixEntryL1 ((M s)⁻¹ - (A s)⁻¹) / 2) *
      (matrixEntryL1 (M s)⁻¹ + matrixEntryL1 (A s)⁻¹) ≤ Dinv * L := by
    have hm := mul_le_mul (hinv s) (add_le_add (hLM s) (hLA s))
      (add_nonneg (matrixEntryL1_nonneg _) (matrixEntryL1_nonneg _)) hDinv
    nlinarith
  have hmul := mul_le_mul hcoeff hsq (sq_nonneg _) (mul_nonneg hDinv hL0)
  exact (abs_log_affineGaussianPDF_sub_matrices (mean s) (M s) (A s) (hM s) (hA s) x).trans
    (add_le_add (hlog s) hmul)

end GeneralizedBulk.Entropy
