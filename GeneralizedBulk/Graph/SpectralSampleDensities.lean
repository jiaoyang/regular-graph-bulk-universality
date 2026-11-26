import GeneralizedBulk.Graph.SpectralPortTransport
import GeneralizedBulk.Gaussian.StarPermutation
import GeneralizedBulk.Graph.GaussianChannelEntropy
import GeneralizedBulk.Graph.StarCompression
import GeneralizedBulk.Graph.HYEdgeCovariance
import GeneralizedBulk.Entropy.SelectedGaussianCoordinates

/-! Actual physical product-coordinate Gaussian factors for spectral star
and edge samples, and their exact graph-channel entropy transport. -/
noncomputable section
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Gaussian GeneralizedBulk.Covariance GeneralizedBulk.Entropy GeneralizedBulk.Graph.Configuration
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem spectral_starVertex_injective (s : Fin (N n) × Equiv.Perm (Fin d)) :
    Function.Injective (D.starVertex n ω s) := by
  have he : D.starVertex n ω s=D.entropyStarVertex n ω s.1 ∘ starLeafPermutation s.2 := by
    funext j
    refine Fin.cases ?_ (fun a => ?_) j <;> simp [starVertex,entropyStarVertex]
  rw [he]
  exact (D.entropyStarVertex_injective n ω s.1).comp (starLeafPermutation s.2).injective

theorem spectral_edgeVertex_injective (s : Fin (N n) × Fin d) :
    Function.Injective (D.proposalEndpoint n ω s) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (D.neighbor_ne_root n ω s.1 s.2 (by simpa [proposalEndpoint] using h.symm))
  · exact False.elim (D.neighbor_ne_root n ω s.1 s.2 (by simpa [proposalEndpoint] using h))
  · rfl

variable {k : ℕ} {J : Type*} [Fintype J]
variable (A : Matrix (Fin k × Fin (N n)) J ℝ) (lo : ℝ) (hlo : 0 < lo)
  (hbound : ∀ x : Fin k × Fin (N n) → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x))

def spectralStarNoiseFactor (s : Fin (N n) × Equiv.Perm (Fin d)) :
    Matrix (Fin k × Fin (d+1)) (Fin k × Fin (d+1)) ℝ :=
  selectedGaussianFactor A (coloredCoordinateSelection (D.starVertex n ω s))
    (coloredCoordinateSelection_injective _ (D.spectral_starVertex_injective n ω s)) lo hlo hbound

def spectralEdgeNoiseFactor (s : Fin (N n) × Fin d) : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℝ :=
  selectedGaussianFactor A (coloredCoordinateSelection (D.proposalEndpoint n ω s))
    (coloredCoordinateSelection_injective _ (D.spectral_edgeVertex_injective n ω s)) lo hlo hbound

theorem spectralStarNoiseFactor_det_ne_zero (s : Fin (N n) × Equiv.Perm (Fin d)) :
    (D.spectralStarNoiseFactor n ω A lo hlo hbound s).det ≠ 0 := selectedGaussianFactor_det_ne_zero _ _ _ _ _ _

theorem spectralEdgeNoiseFactor_det_ne_zero (s : Fin (N n) × Fin d) :
    (D.spectralEdgeNoiseFactor n ω A lo hlo hbound s).det ≠ 0 := selectedGaussianFactor_det_ne_zero _ _ _ _ _ _

theorem spectralStarNoiseFactor_covariance (s : Fin (N n) × Equiv.Perm (Fin d)) :
    D.spectralStarNoiseFactor n ω A lo hlo hbound s*(D.spectralStarNoiseFactor n ω A lo hlo hbound s).transpose=
      (A*A.transpose).submatrix (coloredCoordinateSelection (D.starVertex n ω s))
        (coloredCoordinateSelection (D.starVertex n ω s)) := selectedGaussianFactor_covariance _ _ _ _ _ _

theorem spectralEdgeNoiseFactor_covariance (s : Fin (N n) × Fin d) :
    D.spectralEdgeNoiseFactor n ω A lo hlo hbound s*(D.spectralEdgeNoiseFactor n ω A lo hlo hbound s).transpose=
      (A*A.transpose).submatrix (coloredCoordinateSelection (D.proposalEndpoint n ω s))
        (coloredCoordinateSelection (D.proposalEndpoint n ω s)) := selectedGaussianFactor_covariance _ _ _ _ _ _

def spectralStarGaussianDensity (mean : Fin k × Fin (N n) → ℝ) : (Fin k × Fin (d+1) → ℝ) → ℝ :=
  gaussianMixturePDF (uniformSampleWeight (Fin (N n) × Equiv.Perm (Fin d)))
    (fun s => mean ∘ coloredCoordinateSelection (D.starVertex n ω s)) (D.spectralStarNoiseFactor n ω A lo hlo hbound)

def spectralEdgeGaussianDensity (mean : Fin k × Fin (N n) → ℝ) : (Fin k × Fin 2 → ℝ) → ℝ :=
  gaussianMixturePDF (uniformSampleWeight (Fin (N n) × Fin d))
    (fun s => mean ∘ coloredCoordinateSelection (D.proposalEndpoint n ω s)) (D.spectralEdgeNoiseFactor n ω A lo hlo hbound)

theorem starGaussianDensity_entropy_spectral (mean : Fin k × Fin (N n) → ℝ) :
    differentialEntropy (starGaussianDensity A lo hlo hbound (D.spectralRegularGraph n ω) mean)=
      differentialEntropy (D.spectralStarGaussianDensity n ω A lo hlo hbound mean) := by
  letI : Nonempty (Fin (N n)) := ⟨⟨0,D.size_pos n⟩⟩
  exact selectedGaussian_entropy_physical_coordinates A mean
    (starVertexSelection (D.spectralRegularGraph n ω)) (D.starVertex n ω) (D.canonicalStarSampleEquiv n ω)
    (D.canonical_star_selector_eq n ω) (starNoiseFactor A lo hlo hbound (D.spectralRegularGraph n ω))
    (D.spectralStarNoiseFactor n ω A lo hlo hbound)
    (starNoiseFactor_det_ne_zero A lo hlo hbound (D.spectralRegularGraph n ω))
    (D.spectralStarNoiseFactor_det_ne_zero n ω A lo hlo hbound)
    (fun s => selectedGaussianFactor_covariance _ _ _ _ _ _)
    (D.spectralStarNoiseFactor_covariance n ω A lo hlo hbound)

theorem edgeGaussianDensity_entropy_spectral (hd : 0 < d) (mean : Fin k × Fin (N n) → ℝ) :
    differentialEntropy (edgeGaussianDensity A lo hlo hbound (D.spectralRegularGraph n ω) mean)=
      differentialEntropy (D.spectralEdgeGaussianDensity n ω A lo hlo hbound mean) := by
  letI : Nonempty (Fin (N n)) := ⟨⟨0,D.size_pos n⟩⟩
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  apply selectedGaussian_entropy_physical_coordinates A mean
    (edgeVertexSelection (D.spectralRegularGraph n ω)) (D.proposalEndpoint n ω) (D.canonicalEdgeSampleEquiv n ω)
    _ (edgeNoiseFactor A lo hlo hbound (D.spectralRegularGraph n ω))
    (D.spectralEdgeNoiseFactor n ω A lo hlo hbound)
    (edgeNoiseFactor_det_ne_zero A lo hlo hbound (D.spectralRegularGraph n ω))
    (D.spectralEdgeNoiseFactor_det_ne_zero n ω A lo hlo hbound)
    (fun s => selectedGaussianFactor_covariance _ _ _ _ _ _)
    (D.spectralEdgeNoiseFactor_covariance n ω A lo hlo hbound)
  intro s
  funext j
  rw [D.canonical_edge_selector_eq n ω]
  fin_cases j <;> simp [proposalEndpoint]

end GeneralizedBulk.External.RegularSpectralData
