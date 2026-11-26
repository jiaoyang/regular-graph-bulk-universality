import GeneralizedBulk.Entropy.GaussianMixtureJacobian
import GeneralizedBulk.Gaussian.EdgeWhitening

/-! Exact differential entropy of the literal root-neighbor ideal mixture,
expressed in the actual retained Gaussian observation coordinates. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped BigOperators Matrix
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Channel
variable {S : Type*} [Fintype S]

theorem edgePhysicalMixture_entropy (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < d) (i : Fin d) (weight : S → ℝ)
    (mean : S → coloredObserved d k hd i → ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) :
    differentialEntropy (gaussianMixturePDF weight
      (fun s => (edgeObservationCoefficients d k hd energy i).mulVec (mean s))
      (fun _ => edgePhysicalFactor d k hd energy i)) =
      differentialEntropy (gaussianMixturePDF weight mean
        (fun _ => (1 : Matrix (coloredObserved d k hd i) (coloredObserved d k hd i) ℝ))) +
        ∑ a, Real.log ((edgeWaveCovariance d (energy a)).det) / 2 := by
  let e := edgeInputEquiv d k hd i
  let A := edgeObservationCoefficients d k hd energy i
  let M := edgePhysicalFactor d k hd energy i
  let m : S → (Fin k × Fin 2) → ℝ := fun s j => mean s (e j)
  have hm (s : S) : M.mulVec (m s) = A.mulVec (mean s) := by
    change (A.submatrix id e).mulVec (m s) = _
    rw [Matrix.submatrix_mulVec_equiv]
    change A.mulVec (fun a => m s (e.symm a)) = _
    simp only [m, Equiv.apply_symm_apply]
  have hlinear := gaussianMixture_entropy_linear_identity weight m hw hnorm M
    (edgePhysicalFactor_det_ne_zero d k hd energy hE i)
  simp_rw [hm] at hlinear
  have hinput : differentialEntropy (gaussianMixturePDF weight m
      (fun _ => (1 : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℝ))) =
      differentialEntropy (gaussianMixturePDF weight mean
        (fun _ => (1 : Matrix (coloredObserved d k hd i) (coloredObserved d k hd i) ℝ))) :=
    gaussianMixture_entropy_coordinate_identity e.symm weight mean
  rw [hinput] at hlinear
  simpa only [M, edgePhysicalFactor_logabsdet d k hd energy hE i] using hlinear

theorem edgePhysicalMixture_entropy_coordinates (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < d) (i : Fin d) (weight : S → ℝ) (signal : S → ColoredStar d k)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) :
    differentialEntropy (gaussianMixturePDF weight
      (fun s j => @inner ℝ (ColoredStar d k) _ (physicalEdgeRow d k hd energy i j) (signal s))
      (fun _ => edgePhysicalFactor d k hd energy i)) =
      differentialEntropy (gaussianMixturePDF weight
        (fun s => fun a : coloredObserved d k hd i =>
          ((coloredObservationMatrix d k hd i).transpose.mulVec (scalarCoordinates d k (signal s))) a)
        (fun _ => (1 : Matrix (coloredObserved d k hd i) (coloredObserved d k hd i) ℝ))) +
        ∑ a, Real.log ((edgeWaveCovariance d (energy a)).det) / 2 := by
  have hh := edgePhysicalMixture_entropy d k hd energy hE i weight
    (fun s a => ((coloredObservationMatrix d k hd i).transpose.mulVec (scalarCoordinates d k (signal s))) a) hw hnorm
  simp_rw [edgeObservationCoefficients_action] at hh
  exact hh

end GeneralizedBulk.Entropy
