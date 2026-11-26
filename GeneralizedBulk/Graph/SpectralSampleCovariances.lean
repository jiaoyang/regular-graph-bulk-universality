import GeneralizedBulk.Graph.SpectralSampleDensities
import GeneralizedBulk.Graph.ColoredResolventNoise
import GeneralizedBulk.Graph.HYEdgeEntropy
import GeneralizedBulk.Entropy.SelectedGaussianTrace
import GeneralizedBulk.Graph.ResolventChannelParameters

/-! The constructed physical sample factors have exactly the covariance
and signal values used by the HY full-mixture entropy comparisons. -/
noncomputable section
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Gaussian GeneralizedBulk.Covariance GeneralizedBulk.Entropy
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)
variable {k : ℕ} {J : Type*} [Fintype J]
variable (A : Matrix (Fin k × Fin (N n)) J ℝ) (lo : ℝ) (hlo : 0 < lo)
  (hbound : ∀ x : Fin k × Fin (N n) → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x))

theorem spectralStarNoiseFactor_resolvent_covariance (energy sigma : Fin k → ℝ) (eta : ℝ)
    (hGram : A*A.transpose=D.coloredResolventCovariance n ω energy eta sigma)
    (s : Fin (N n) × Equiv.Perm (Fin d)) :
    D.spectralStarNoiseFactor n ω A lo hlo hbound s*(D.spectralStarNoiseFactor n ω A lo hlo hbound s).transpose=
      colorBlock (fun a => (D.resolventCovariance n ω (energy a) eta (sigma a)).submatrix
        (D.starVertex n ω s) (D.starVertex n ω s)) := by
  rw [D.spectralStarNoiseFactor_covariance n ω A lo hlo hbound,hGram]
  rfl

theorem spectralEdgeNoiseFactor_resolvent_covariance (energy : Fin k → ℝ) (eta : ℝ)
    (hGram : A*A.transpose=D.coloredResolventCovariance n ω energy eta (fun a => (GeneralizedBulk.KestenMcKay.diagonalBoundary d (energy a)).im))
    (s : Fin (N n) × Fin d) :
    D.spectralEdgeNoiseFactor n ω A lo hlo hbound s*(D.spectralEdgeNoiseFactor n ω A lo hlo hbound s).transpose=
      D.coloredLocalEdgeCovariance n ω s energy eta := by
  rw [D.spectralEdgeNoiseFactor_covariance n ω A lo hlo hbound,hGram]
  rfl

theorem spectralStarNoiseFactor_lower (s : Fin (N n) × Equiv.Perm (Fin d)) (x : Fin k × Fin (d+1) → ℝ) :
    lo*(∑ i,x i^2) ≤ dotProduct x ((D.spectralStarNoiseFactor n ω A lo hlo hbound s*
      (D.spectralStarNoiseFactor n ω A lo hlo hbound s).transpose).mulVec x) := selectedGaussianFactor_lower _ _ _ _ _ _ x

theorem spectralEdgeNoiseFactor_lower (s : Fin (N n) × Fin d) (x : Fin k × Fin 2 → ℝ) :
    lo*(∑ i,x i^2) ≤ dotProduct x ((D.spectralEdgeNoiseFactor n ω A lo hlo hbound s*
      (D.spectralEdgeNoiseFactor n ω A lo hlo hbound s).transpose).mulVec x) := selectedGaussianFactor_lower _ _ _ _ _ _ x

theorem spectralStarNoiseFactor_trace_le (U : ℝ) (hU : ∀ i,(coordinateVariance A i : ℝ) ≤ U)
    (s : Fin (N n) × Equiv.Perm (Fin d)) :
    Matrix.trace (D.spectralStarNoiseFactor n ω A lo hlo hbound s*
      (D.spectralStarNoiseFactor n ω A lo hlo hbound s).transpose) ≤ ((k*(d+1) : ℕ) : ℝ)*U := by
  simpa only [Fintype.card_prod,Fintype.card_fin] using selectedGaussianFactor_trace_le A
    (coloredCoordinateSelection (D.starVertex n ω s))
    (coloredCoordinateSelection_injective _ (D.spectral_starVertex_injective n ω s)) lo hlo hbound U hU

theorem spectralEdgeNoiseFactor_trace_le (U : ℝ) (hU : ∀ i,(coordinateVariance A i : ℝ) ≤ U)
    (s : Fin (N n) × Fin d) :
    Matrix.trace (D.spectralEdgeNoiseFactor n ω A lo hlo hbound s*
      (D.spectralEdgeNoiseFactor n ω A lo hlo hbound s).transpose) ≤ ((k*2 : ℕ) : ℝ)*U := by
  simpa only [Fintype.card_prod,Fintype.card_fin] using selectedGaussianFactor_trace_le A
    (coloredCoordinateSelection (D.proposalEndpoint n ω s))
    (coloredCoordinateSelection_injective _ (D.spectral_edgeVertex_injective n ω s)) lo hlo hbound U hU

theorem rawEigenSignal_star_mean (selection : Fin k → Fin (N n)) (r : ℝ)
    (s : Fin (N n) × Equiv.Perm (Fin d)) :
    (fun i => r*D.rawEigenSignal n ω selection i) ∘ coloredCoordinateSelection (D.starVertex n ω s)=
      r • D.starSample n ω (fun a => D.eigenvector n ω (selection a)) s := rfl

theorem rawEigenSignal_edge_mean (selection : Fin k → Fin (N n)) (r : ℝ) (s : Fin (N n) × Fin d) :
    (fun i => r*D.rawEigenSignal n ω selection i) ∘ coloredCoordinateSelection (D.proposalEndpoint n ω s)=
      r • D.orientedEdgeMark n ω (fun a => D.eigenvector n ω (selection a)) s := rfl

end GeneralizedBulk.External.RegularSpectralData
