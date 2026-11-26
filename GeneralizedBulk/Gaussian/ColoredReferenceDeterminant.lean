import GeneralizedBulk.Gaussian.ColoredExtendedWhitening
import GeneralizedBulk.Gaussian.StarReferenceDeterminant

/-! Exact Jacobian of the actual colored extended whitening map. -/
noncomputable section
open scoped BigOperators Matrix
namespace GeneralizedBulk.Gaussian
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.External.RegularSpectralData

theorem extendedStarFactor_logabsdet (d : ℕ) (hd : 2 ≤ d) (E : ℝ) (hE : |E| < d) :
    Real.log (|(extendedStarFactor d hd E).det|) =
      Real.log ((starWaveCovariance d E + starNormalProjection d E).det) / 2 := by
  have hh := congrArg (fun A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ => Real.log A.det)
    (extendedStarFactor_covariance d hd E hE)
  change Real.log ((extendedStarFactor d hd E * (extendedStarFactor d hd E).transpose).det) =
    Real.log ((starWaveCovariance d E + starNormalProjection d E).det) at hh
  rw [Matrix.det_mul, Matrix.det_transpose, ← sq, Real.log_pow] at hh
  rw [Real.log_abs]
  norm_num at hh
  linarith

theorem coloredExtendedFactor_logabsdet (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < d) :
    Real.log (|(coloredExtendedFactor d k hd energy).det|) =
      ∑ a, Real.log ((starWaveCovariance d (energy a) + starNormalProjection d (energy a)).det) / 2 := by
  rw [coloredExtendedFactor_blockDiagonal, Matrix.det_submatrix_equiv_self,
    Matrix.det_blockDiagonal, Finset.abs_prod,
    Real.log_prod _ _ (fun a _ => abs_ne_zero.mpr (extendedStarFactor_det_ne_zero d hd _ (hE a)))]
  apply Finset.sum_congr rfl
  intro a ha
  exact extendedStarFactor_logabsdet d hd _ (hE a)

end GeneralizedBulk.Gaussian
