import GeneralizedBulk.Entropy.GaussianMixtureEntropyCoupling

/-! Quantitative entropy stability for actual finite Gaussian mixtures.
The estimate allows a polynomial signal-bound loss and is independent of
component count and component weights. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite Mehler
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

theorem gaussianMixture_entropy_stability
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
    (hfactor : ∀ s, matrixEntryL1 (M s - A s) ≤ Dfactor) :
    |differentialEntropy (gaussianMixturePDF weight mean M) - differentialEntropy (gaussianMixturePDF weight mean A)| ≤
      mixtureStabilityCoefficient B T L Dlog Dinv Dfactor * (1 + (Fintype.card I : ℝ) ^ 2) := by
  apply gaussianMixture_entropy_difference_of_coupling weight mean M A hw hnorm hM hA
    (mixtureStabilityCoefficient B T L Dlog Dinv Dfactor)
  · unfold mixtureStabilityCoefficient
    positivity
  · exact gaussianMixture_coupled_log_bound weight mean M A hw hnorm hM hA B T L Dlog Dinv Dfactor
      hB0 hT0 hL0 hDlog0 hDinv0 hDf0 hB hTM hTA hLM hLA hlog hinv hfactor

end GeneralizedBulk.Entropy
