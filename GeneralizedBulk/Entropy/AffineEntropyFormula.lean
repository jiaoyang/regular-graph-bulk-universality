import GeneralizedBulk.Entropy.GaussianMixtureEntropy

/-! The actual Lebesgue-density entropy formula for an affine Gaussian. -/
noncomputable section
open MeasureTheory

namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Analysis

theorem differentialEntropy_affineGaussianPDF {I : Type*} [Fintype I] [DecidableEq I]
    (mean : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    differentialEntropy (affineGaussianPDF mean M) = Real.log (M*M.transpose).det/2+
      (Fintype.card I : ℝ)/2*(1+Real.log (2*Real.pi)) := by
  have h := affineGaussian_differentialEntropy mean M hM
  rw [affineGaussian_eq_volume_withDensity mean M hM,
    integral_realDensity volume _ _ (measurable_affineGaussianPDF mean M)
      (fun x => (affineGaussianPDF_pos mean M hM x).le)] at h
  exact h

theorem differentialEntropy_affineGaussianPDF_mean_independent {I : Type*} [Fintype I] [DecidableEq I]
    (mean mean' : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    differentialEntropy (affineGaussianPDF mean M) = differentialEntropy (affineGaussianPDF mean' M) := by
  rw [differentialEntropy_affineGaussianPDF mean M hM,differentialEntropy_affineGaussianPDF mean' M hM]

end GeneralizedBulk.Entropy
