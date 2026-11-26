import GeneralizedBulk.Entropy.GaussianCovarianceLogComparison

/-! A component-count-independent entropy coupling envelope. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite Mehler
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

def mixtureStabilityCoefficient (B T L Dlog Dinv Dfactor : ℝ) : ℝ :=
  Dlog + Dinv * L * (8 * B ^ 2 + 2 * T ^ 2) + L ^ 2 * Dfactor * (B + T)

theorem gaussianMixture_coupled_log_bound
    (weight : S → ℝ) (mean : S → I → ℝ) (M A : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1)
    (hM : ∀ s, (M s).det ≠ 0) (hA : ∀ s, (A s).det ≠ 0)
    (B T L Dlog Dinv Dfactor : ℝ)
    (hB0 : 0 ≤ B) (hT0 : 0 ≤ T) (hL0 : 0 ≤ L) (hDlog0 : 0 ≤ Dlog)
    (hDinv0 : 0 ≤ Dinv) (hDf0 : 0 ≤ Dfactor)
    (hB : ∀ s, coordinateL1 (mean s) ≤ B)
    (hTM : ∀ s, matrixEntryL1 (M s) ≤ T) (hTA : ∀ s, matrixEntryL1 (A s) ≤ T)
    (hLM : ∀ s, matrixEntryL1 (M s)⁻¹ ≤ L) (hLA : ∀ s, matrixEntryL1 (A s)⁻¹ ≤ L)
    (hlog : ∀ s, |Real.log (|(M s).det|) - Real.log (|(A s).det|)| ≤ Dlog)
    (hinv : ∀ s, matrixEntryL1 ((M s)⁻¹ - (A s)⁻¹) ≤ Dinv)
    (hfactor : ∀ s, matrixEntryL1 (M s - A s) ≤ Dfactor) (s : S) (z : I → ℝ) :
    |Real.log (gaussianMixturePDF weight mean M (mean s + (M s).mulVec z)) -
      Real.log (gaussianMixturePDF weight mean A (mean s + (A s).mulVec z))| ≤
      mixtureStabilityCoefficient B T L Dlog Dinv Dfactor * (1 + coordinateL1 z ^ 2) := by
  let x := mean s + (M s).mulVec z
  let y := mean s + (A s).mulVec z
  let Z := coordinateL1 z
  have hZ : 0 ≤ Z := coordinateL1_nonneg z
  have hx : coordinateL1 x ≤ B + T * Z := by
    refine (coordinateL1_add_le _ _).trans (add_le_add (hB s) ?_)
    exact (coordinateL1_mulVec_le (M s) z).trans (mul_le_mul_of_nonneg_right (hTM s) hZ)
  have hy : coordinateL1 y ≤ B + T * Z := by
    refine (coordinateL1_add_le _ _).trans (add_le_add (hB s) ?_)
    exact (coordinateL1_mulVec_le (A s) z).trans (mul_le_mul_of_nonneg_right (hTA s) hZ)
  have hxy : coordinateL1 (x-y) ≤ Dfactor * Z := by
    have he : x-y = (M s - A s).mulVec z := by
      rw [Matrix.sub_mulVec]
      dsimp [x,y]
      abel
    rw [he]
    exact (coordinateL1_mulVec_le _ z).trans (mul_le_mul_of_nonneg_right (hfactor s) hZ)
  have hc := gaussianMixture_covariance_log_comparison weight mean M A hw hnorm hM hA
    B L Dlog Dinv hL0 hDinv0 hB hLM hLA hlog hinv x
  have hs := abs_log_gaussianMixturePDF_sub weight mean A hw hnorm hA B L hB hLA x y
  have hc' : |Real.log (gaussianMixturePDF weight mean M x) - Real.log (gaussianMixturePDF weight mean A x)| ≤
      Dlog + Dinv * L * (2 * B + T * Z) ^ 2 := by
    refine hc.trans (add_le_add_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (add_nonneg (coordinateL1_nonneg x) hB0) (by linarith [hx]) 2)
      (mul_nonneg hDinv0 hL0)) _)
  have hs' : |Real.log (gaussianMixturePDF weight mean A x) - Real.log (gaussianMixturePDF weight mean A y)| ≤
      L ^ 2 * Dfactor * (Z * (2 * B + T * Z)) := by
    have h1 := mul_le_mul_of_nonneg_left hxy (div_nonneg (sq_nonneg L) (by norm_num : (0:ℝ)≤2))
    have h2 : coordinateL1 x + coordinateL1 y + 2 * B ≤ 2 * (2 * B + T * Z) := by linarith [hx,hy]
    have hm := mul_le_mul h1 h2
      (by nlinarith [coordinateL1_nonneg x, coordinateL1_nonneg y])
      (mul_nonneg (div_nonneg (sq_nonneg L) (by norm_num)) (mul_nonneg hDf0 hZ))
    exact hs.trans (by nlinarith [hm])
  have hsq : (2 * B + T * Z) ^ 2 ≤ (8 * B ^ 2 + 2 * T ^ 2) * (1 + Z ^ 2) := by
    nlinarith [sq_nonneg (2 * B - T * Z), mul_nonneg (sq_nonneg B) (sq_nonneg Z), sq_nonneg T]
  have hzquad : Z * (2 * B + T * Z) ≤ (B + T) * (1 + Z ^ 2) := by
    nlinarith [mul_nonneg hB0 (sq_nonneg (Z-1))]
  have hcp := mul_le_mul_of_nonneg_left hsq (mul_nonneg hDinv0 hL0)
  have hsp := mul_le_mul_of_nonneg_left hzquad (mul_nonneg (sq_nonneg L) hDf0)
  have htri := abs_sub_le (Real.log (gaussianMixturePDF weight mean M x))
    (Real.log (gaussianMixturePDF weight mean A x)) (Real.log (gaussianMixturePDF weight mean A y))
  change |Real.log (gaussianMixturePDF weight mean M x) - Real.log (gaussianMixturePDF weight mean A y)| ≤ _
  unfold mixtureStabilityCoefficient
  nlinarith [htri.trans (add_le_add hc' hs'), mul_nonneg hDlog0 (sq_nonneg Z)]

end GeneralizedBulk.Entropy
