import GeneralizedBulk.Entropy.IndependentNormalEntropy
import GeneralizedBulk.Gaussian.ColoredReferenceDeterminant

/-! The ideal nonsingular star mixture has exactly the tangent-mixture
entropy, the independent normal Gaussian entropy, and the true whitening
Jacobian. All distributions are literal finite Gaussian mixtures. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Matrix
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.External.RegularSpectralData
variable {S : Type*} [Fintype S]

theorem coloredExtendedMixture_entropy (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < d) (weight : S → ℝ) (mean : S → ScalarCoordinate d k → ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) :
    differentialEntropy (gaussianMixturePDF weight
      (fun s => (coloredExtendedCoefficients d k hd energy).mulVec (Sum.elim (mean s) (fun _ : Fin k => 0)))
      (fun _ => coloredExtendedFactor d k hd energy)) =
      differentialEntropy (gaussianMixturePDF weight mean
        (fun _ => (1 : Matrix (ScalarCoordinate d k) (ScalarCoordinate d k) ℝ))) +
        (k : ℝ) / 2 * (1 + Real.log (2 * Real.pi)) +
        ∑ a, Real.log ((starWaveCovariance d (energy a) + starNormalProjection d (energy a)).det) / 2 := by
  let e := coloredExtendedInputEquiv d k (by omega)
  let A := coloredExtendedCoefficients d k hd energy
  let M := coloredExtendedFactor d k hd energy
  let m : S → (Fin k × Fin (d+1)) → ℝ := fun s j => Sum.elim (mean s) (fun _ : Fin k => 0) (e j)
  have hm (s : S) : M.mulVec (m s) = A.mulVec (Sum.elim (mean s) (fun _ : Fin k => 0)) := by
    change (A.submatrix id e).mulVec (m s) = _
    rw [Matrix.submatrix_mulVec_equiv]
    change A.mulVec (fun a => m s (e.symm a)) = _
    simp only [m, Equiv.apply_symm_apply]
  have hlinear := gaussianMixture_entropy_linear_identity weight m hw hnorm M
    (coloredExtendedFactor_det_ne_zero d k hd energy hE)
  simp_rw [hm] at hlinear
  have hinput : differentialEntropy (gaussianMixturePDF weight m (fun _ => (1 : Matrix (Fin k × Fin (d+1)) (Fin k × Fin (d+1)) ℝ))) =
      differentialEntropy (gaussianMixturePDF weight (fun s => Sum.elim (mean s) (fun _ : Fin k => 0))
        (fun _ => (1 : Matrix (ExtendedColoredCoordinate d k) (ExtendedColoredCoordinate d k) ℝ))) := by
    exact gaussianMixture_entropy_coordinate_identity e.symm weight
      (fun s => Sum.elim (mean s) (fun _ : Fin k => 0))
  rw [hinput, gaussianMixture_entropy_sum_normal weight mean hw hnorm] at hlinear
  simpa only [M, Fintype.card_fin, coloredExtendedFactor_logabsdet d k hd energy hE] using hlinear

end GeneralizedBulk.Entropy
