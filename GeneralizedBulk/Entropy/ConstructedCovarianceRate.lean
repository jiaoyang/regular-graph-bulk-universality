import GeneralizedBulk.Entropy.CovarianceStabilityRate

/-! A linear covariance-error entropy theorem with all Gaussian factors constructed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Covariance GeneralizedBulk.Entropy.Mehler
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

def covarianceEntropyRateConstant (M : Matrix I I ℝ) : ℝ :=
  let c := normalizationLoss M 1
  stabilityRateConstant (matrixEntryL1 M+covarianceFactorError M c)
    (matrixEntryL1 M⁻¹+covarianceInverseFactorError M c)
    (Fintype.card I*c) (covarianceInverseFactorError M c) (covarianceFactorError M c) *
      (1+(Fintype.card I : ℝ)^2)

theorem covarianceEntropyRateConstant_nonneg (M : Matrix I I ℝ) : 0 ≤ covarianceEntropyRateConstant M := by
  have h1 := matrixEntryL1_nonneg M
  have h2 := matrixEntryL1_nonneg M⁻¹
  unfold covarianceEntropyRateConstant stabilityRateConstant covarianceFactorError covarianceInverseFactorError normalizationLoss
  positivity

theorem exists_gaussianMixture_entropy_linear_rate
    (weight : S → ℝ) (mean : S → I → ℝ) (Q : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) (hQ : ∀ s, (Q s).PosDef)
    (M : Matrix I I ℝ) (hM : M.det ≠ 0) (B e : ℝ) (hB : 0 ≤ B) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hsignal : ∀ s, coordinateL1 (mean s) ≤ B)
    (hclose : ∀ s i j, |(Q s-M*M.transpose) i j| ≤ e)
    (hsmall : normalizationLoss M e ≤ 1/2) :
    ∃ A : S → Matrix I I ℝ,
      (∀ s, A s*(A s).transpose=Q s ∧ (A s).det ≠ 0) ∧
      |differentialEntropy (gaussianMixturePDF weight mean A) -
        differentialEntropy (gaussianMixturePDF weight mean (fun _ => M))| ≤
      covarianceEntropyRateConstant M*(1+B^2)*e := by
  obtain ⟨A,hA,hEnt⟩ := exists_gaussianMixture_entropy_stable_factors weight mean Q hw hnorm hQ M hM B e hB he hsignal hclose hsmall
  refine ⟨A,hA,hEnt.trans ?_⟩
  let c := normalizationLoss M 1
  have hc : 0 ≤ c := by dsimp [c,normalizationLoss]; positivity
  have heps : normalizationLoss M e=c*e := by dsimp [c,normalizationLoss]; ring
  have hf : covarianceFactorError M (normalizationLoss M e)=covarianceFactorError M c*e := by
    rw [heps]
    unfold covarianceFactorError
    ring
  have hi : covarianceInverseFactorError M (normalizationLoss M e)=covarianceInverseFactorError M c*e := by
    rw [heps]
    unfold covarianceInverseFactorError
    ring
  have hd : (Fintype.card I : ℝ)*normalizationLoss M e=(Fintype.card I*c)*e := by rw [heps]; ring
  rw [hf,hi,hd]
  have hcoef := mixtureStabilityCoefficient_linear_bound B (matrixEntryL1 M) (covarianceFactorError M c)
    (matrixEntryL1 M⁻¹) (covarianceInverseFactorError M c) (Fintype.card I*c)
    (covarianceInverseFactorError M c) (covarianceFactorError M c) e hB (matrixEntryL1_nonneg _)
    (by unfold covarianceFactorError; positivity) (matrixEntryL1_nonneg _)
    (by unfold covarianceInverseFactorError; positivity) (by positivity)
    (by unfold covarianceInverseFactorError; positivity) (by unfold covarianceFactorError; positivity) he he1
  have hm := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ 1+(Fintype.card I : ℝ)^2 by positivity)
  convert hm using 1
  unfold covarianceEntropyRateConstant
  dsimp only [c]
  ring

end GeneralizedBulk.Entropy
