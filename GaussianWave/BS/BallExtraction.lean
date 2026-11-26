import GaussianWave.BS.LocalGaussianReference
import GaussianWave.BS.ColoredInnovationCharts

/-! Actual measurable inverse innovation maps and Gaussian laws. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

def vertexBallExtractLinear (m k : ℕ) :
    (VertexBallVertex (m + 2) k → ℝ) →ₗ[ℝ] (VertexBallInnovation (m + 2) k → ℝ) where
  toFun := vertexBallExtract m k
  map_add' x y := by
    ext j
    cases j with
    | inl a =>
      change (x _ + y _) - (x _ + y _) = (x _ - x _) + (y _ - y _)
      ring
    | inr aj => exact congrFun (branchExtract_add m k _ _) aj.2
  map_smul' r x := by
    ext j
    cases j with
    | inl a =>
      change r * x _ - r * x _ = r * (x _ - x _)
      ring
    | inr aj => exact congrFun (branchExtract_smul m k r _) aj.2

def edgeBallExtractLinear (m k : ℕ) :
    (EdgeBallVertex (m + 2) k → ℝ) →ₗ[ℝ] (EdgeBallInnovation (m + 2) k → ℝ) where
  toFun := edgeBallExtract m k
  map_add' x y := by
    ext j
    cases j with
    | inl b => rfl
    | inr bj => exact congrFun (branchExtract_add m k _ _) bj.2
  map_smul' r x := by
    ext j
    cases j with
    | inl b => rfl
    | inr bj => exact congrFun (branchExtract_smul m k r _) bj.2

theorem measurable_vertexBallExtract (m k : ℕ) : Measurable (vertexBallExtract m k) :=
  (vertexBallExtractLinear m k).continuous_of_finiteDimensional.measurable

theorem measurable_edgeBallExtract (m k : ℕ) : Measurable (edgeBallExtract m k) :=
  (edgeBallExtractLinear m k).continuous_of_finiteDimensional.measurable

theorem vertexGaussianBallLaw_extract (m k : ℕ) (energy : ℝ) :
    Measure.map (vertexBallExtract m k) (vertexGaussianBallLaw m k energy) =
      forestGaussianInnovationLaw m k (Real.sqrt (siblingVariance (m + 2) energy))
        (vertexRootInnovationFactor m energy) := by
  rw [← forest_vertex_reference_physical_law,
    Measure.map_map (measurable_vertexBallExtract m k)
      (vertexBallBuildLinear m k energy).continuous_of_finiteDimensional.measurable]
  have h : vertexBallExtract m k ∘ vertexBallBuildLinear m k energy = id :=
    funext (vertexBallExtract_build m k energy)
  rw [h, Measure.map_id]

theorem edgeGaussianBallLaw_extract (m k : ℕ) (energy : ℝ) :
    Measure.map (edgeBallExtract m k) (edgeGaussianBallLaw m k energy) =
      forestGaussianInnovationLaw m k (Real.sqrt (siblingVariance (m + 2) energy))
        (physicalEdgeMatrix (energy / (m + 2))) := by
  rw [← forest_edge_reference_physical_law,
    Measure.map_map (measurable_edgeBallExtract m k)
      (edgeBallBuildLinear m k energy).continuous_of_finiteDimensional.measurable]
  have h : edgeBallExtract m k ∘ edgeBallBuildLinear m k energy = id :=
    funext (edgeBallExtract_build m k energy)
  rw [h, Measure.map_id]

theorem localEdgeInnovationEquiv_reference (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (a : Fin (m + 2)) :
    Measure.map (localEdgeInnovationEquiv m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)) a)
      (sumVectorProductLaw
        (forestGaussianInnovationLaw m k (Real.sqrt (siblingVariance (m + 2) energy))
          (vertexRootInnovationFactor m energy))
        (newBranchGaussianLaw m k (Real.sqrt (siblingVariance (m + 2) energy)))) =
      forestGaussianInnovationLaw m (k + 1) (Real.sqrt (siblingVariance (m + 2) energy))
        (physicalEdgeMatrix (energy / (m + 2))) := by
  rw [← edgeGaussianBallLaw_extract, ← localEdgeReconstruction_reference m k energy he a,
    Measure.map_map (measurable_edgeBallExtract m (k + 1))
      (localEdgeReconstruction m k energy a).continuous_of_finiteDimensional.measurable]
  congr 1

theorem localVertexInnovationEquiv_reference (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (b : Bool) :
    Measure.map (localVertexInnovationEquiv m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)) b)
      (sumVectorProductLaw
        (forestGaussianInnovationLaw m k (Real.sqrt (siblingVariance (m + 2) energy))
          (physicalEdgeMatrix (energy / (m + 2))))
        (newBranchGaussianLaw m k (Real.sqrt (siblingVariance (m + 2) energy)))) =
      forestGaussianInnovationLaw m k (Real.sqrt (siblingVariance (m + 2) energy))
        (vertexRootInnovationFactor m energy) := by
  rw [← vertexGaussianBallLaw_extract, ← localVertexReconstruction_reference m k energy he b,
    Measure.map_map (measurable_vertexBallExtract m k)
      (localVertexReconstruction m k energy b).continuous_of_finiteDimensional.measurable]
  congr 1

end GaussianWave.BS
