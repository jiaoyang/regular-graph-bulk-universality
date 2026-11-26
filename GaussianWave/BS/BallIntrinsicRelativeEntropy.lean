import GaussianWave.BS.BallIntrinsicChart
import GaussianWave.BS.BallRelativeSSA
import GaussianWave.BS.IndependentReferenceEntropy

/-! Raw innovation relative entropy equals genuine isometric intrinsic
relative entropy under the constructed common invertible chart. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

def coloredVertexInnovationToIntrinsic (κ : Type*) (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :=
  channelwiseLinearEquiv κ (vertexInnovationToIntrinsic m k energy he)

def coloredEdgeInnovationToIntrinsic (κ : Type*) (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :=
  channelwiseLinearEquiv κ (edgeInnovationToIntrinsic m k energy he)

def jointVertexIntrinsicFlatReference (κ : Type*) [Fintype κ] (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :=
  (vertexGaussianIntrinsicPositiveDensity m k energy he).independentChannels κ

def jointEdgeIntrinsicFlatReference (κ : Type*) [Fintype κ] (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :=
  (edgeGaussianIntrinsicPositiveDensity m k energy he).independentChannels κ

theorem vertexInnovationToIntrinsic_reference_law (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    Measure.map (vertexInnovationToIntrinsic m k energy he)
      (forestGaussianInnovationLaw m k (Real.sqrt (siblingVariance (m + 2) energy))
        (vertexRootInnovationFactor m energy)) =
      (vertexGaussianIntrinsicPositiveDensity m k energy he).law := by
  rw [vertexGaussianIntrinsicPositiveDensity_law, ← forest_vertex_reference_physical_law,
    Measure.map_map (measurable_finiteMatrixAction _)
      (vertexBallBuildLinear m k energy).continuous_of_finiteDimensional.measurable]
  rfl

theorem edgeInnovationToIntrinsic_reference_law (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    Measure.map (edgeInnovationToIntrinsic m k energy he)
      (forestGaussianInnovationLaw m k (Real.sqrt (siblingVariance (m + 2) energy))
        (physicalEdgeMatrix (energy / (m + 2)))) =
      (edgeGaussianIntrinsicPositiveDensity m k energy he).law := by
  rw [edgeGaussianIntrinsicPositiveDensity_law, ← forest_edge_reference_physical_law,
    Measure.map_map (measurable_finiteMatrixAction _)
      (edgeBallBuildLinear m k energy).continuous_of_finiteDimensional.measurable]
  rfl

theorem coloredVertexInnovationToIntrinsic_reference_law (κ : Type*) [Fintype κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    Measure.map (coloredVertexInnovationToIntrinsic κ m k energy he)
      (jointVertexInnovationReference κ m k energy he).law =
      (jointVertexIntrinsicFlatReference κ m k energy he).law := by
  rw [jointVertexInnovationReference_law, jointVertexIntrinsicFlatReference,
    PositiveEntropyDensity.independentChannels_law]
  change Measure.map (fun x : (κ × VertexBallInnovation (m + 2) k) → ℝ =>
    fun ci : κ × VertexBallInnovation (m + 2) k => vertexInnovationToIntrinsic m k energy he
      (fun j => x (ci.1, j)) ci.2) _ = _
  have hχ : Measurable (vertexInnovationToIntrinsic m k energy he : _ → _) :=
    (vertexInnovationToIntrinsic m k energy he).toLinearMap.continuous_of_finiteDimensional.measurable
  rw [independentChannelLaw_mapVector _ (vertexInnovationToIntrinsic m k energy he : _ → _) hχ]
  simp only [vertexInnovationToIntrinsic_reference_law]

theorem coloredEdgeInnovationToIntrinsic_reference_law (κ : Type*) [Fintype κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) :
    Measure.map (coloredEdgeInnovationToIntrinsic κ m k energy he)
      (jointEdgeInnovationReference κ m k energy he).law =
      (jointEdgeIntrinsicFlatReference κ m k energy he).law := by
  rw [jointEdgeInnovationReference_law, jointEdgeIntrinsicFlatReference,
    PositiveEntropyDensity.independentChannels_law]
  change Measure.map (fun x : (κ × EdgeBallInnovation (m + 2) k) → ℝ =>
    fun ci : κ × EdgeBallInnovation (m + 2) k => edgeInnovationToIntrinsic m k energy he
      (fun j => x (ci.1, j)) ci.2) _ = _
  have hχ : Measurable (edgeInnovationToIntrinsic m k energy he : _ → _) :=
    (edgeInnovationToIntrinsic m k energy he).toLinearMap.continuous_of_finiteDimensional.measurable
  rw [independentChannelLaw_mapVector _ (edgeInnovationToIntrinsic m k energy he : _ → _) hχ]
  simp only [edgeInnovationToIntrinsic_reference_law]

theorem vertexBallRelativeEntropy_eq_intrinsic (κ : Type*) [Fintype κ] [DecidableEq κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ))
    (f : PositiveEntropyDensity (volume : Measure ((κ × VertexBallInnovation (m + 2) k) → ℝ))) :
    vertexBallRelativeEntropy κ m k energy he f =
      (f.linearEquiv (coloredVertexInnovationToIntrinsic κ m k energy he)).entropy -
        (jointVertexIntrinsicFlatReference κ m k energy he).entropy := by
  have hG := PositiveEntropyDensity.entropy_eq_of_law_eq _ _
    ((PositiveEntropyDensity.linearEquiv_law _ _).trans
      (coloredVertexInnovationToIntrinsic_reference_law κ m k energy he))
  have h := f.linearEquiv_entropy_difference (jointVertexInnovationReference κ m k energy he)
    (coloredVertexInnovationToIntrinsic κ m k energy he)
  rw [hG] at h
  exact h.symm

theorem edgeBallRelativeEntropy_eq_intrinsic (κ : Type*) [Fintype κ] [DecidableEq κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ))
    (f : PositiveEntropyDensity (volume : Measure ((κ × EdgeBallInnovation (m + 2) k) → ℝ))) :
    edgeBallRelativeEntropy κ m k energy he f =
      (f.linearEquiv (coloredEdgeInnovationToIntrinsic κ m k energy he)).entropy -
        (jointEdgeIntrinsicFlatReference κ m k energy he).entropy := by
  have hG := PositiveEntropyDensity.entropy_eq_of_law_eq _ _
    ((PositiveEntropyDensity.linearEquiv_law _ _).trans
      (coloredEdgeInnovationToIntrinsic_reference_law κ m k energy he))
  have h := f.linearEquiv_entropy_difference (jointEdgeInnovationReference κ m k energy he)
    (coloredEdgeInnovationToIntrinsic κ m k energy he)
  rw [hG] at h
  exact h.symm

theorem jointVertexIntrinsicFlatReference_entropy (r m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    (jointVertexIntrinsicFlatReference (Fin r) m k energy he).entropy =
      (jointVertexGaussianIntrinsicDensity r m k energy he).entropy := by
  simp only [jointVertexIntrinsicFlatReference, PositiveEntropyDensity.independentChannels,
    PositiveEntropyDensity.transport_entropy, jointVertexGaussianIntrinsicDensity]

theorem jointEdgeIntrinsicFlatReference_entropy (r m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    (jointEdgeIntrinsicFlatReference (Fin r) m k energy he).entropy =
      (jointEdgeGaussianIntrinsicDensity r m k energy he).entropy := by
  simp only [jointEdgeIntrinsicFlatReference, PositiveEntropyDensity.independentChannels,
    PositiveEntropyDensity.transport_entropy, jointEdgeGaussianIntrinsicDensity]

end GaussianWave.BS
