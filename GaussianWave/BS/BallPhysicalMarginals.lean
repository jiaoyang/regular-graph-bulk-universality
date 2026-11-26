import GaussianWave.BS.BallExtraction
import GaussianWave.BS.BallRelativeSSA

/-! Literal physical window marginals imply the canonical innovation
marginals used in the relative SSA theorems. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

def channelwiseLinearMap (κ : Type*) {I J : Type*} (L : (I → ℝ) →ₗ[ℝ] (J → ℝ)) :
    ((κ × I) → ℝ) →ₗ[ℝ] ((κ × J) → ℝ) where
  toFun x := fun cj => L (fun i => x (cj.1, i)) cj.2
  map_add' x y := by funext ⟨c, j⟩; exact congrFun (L.map_add _ _) j
  map_smul' r x := by funext ⟨c, j⟩; exact congrFun (L.map_smul r _) j

def jointVertexBallBuild (κ : Type*) (m k : ℕ) (energy : ℝ) :=
  channelwiseLinearMap κ (vertexBallBuildLinear m k energy)

def jointEdgeBallBuild (κ : Type*) (m k : ℕ) (energy : ℝ) :=
  channelwiseLinearMap κ (edgeBallBuildLinear m k energy)

def jointVertexBallExtract (κ : Type*) (m k : ℕ) :=
  channelwiseLinearMap κ (vertexBallExtractLinear m k)

def jointEdgeBallExtract (κ : Type*) (m k : ℕ) :=
  channelwiseLinearMap κ (edgeBallExtractLinear m k)

def jointCoordinateRestriction (κ : Type*) {I J : Type*} (site : I → J) :
    ((κ × J) → ℝ) →ₗ[ℝ] ((κ × I) → ℝ) where
  toFun x := fun ci => x (ci.1, site ci.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem forestInnovationSplit_symm_old (A : Type*) (m k : ℕ) (j : ForestInnovation A m k) :
    (forestInnovationSplit A m k).symm (Sum.inl j) = forestInnovationInclusion A m k j := by
  apply (forestInnovationSplit A m k).injective
  rw [Equiv.apply_symm_apply, forestInnovationSplit_old]

theorem jointVertexBallBuild_extract_ae (κ : Type*) [Fintype κ] (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (μ : Measure ((κ × VertexBallVertex (m + 2) k) → ℝ))
    (hs : ∀ᵐ x ∂μ, ∀ c, VertexBallEigenrelation m k energy (fun v => x (c, v))) :
    (jointVertexBallBuild κ m k energy : _ → _) ∘ jointVertexBallExtract κ m k =ᵐ[μ] id := by
  filter_upwards [hs] with x hx
  funext ⟨c, v⟩
  exact congrFun (vertexBallBuild_extract m k energy hne (fun v => x (c, v)) (hx c)) v

theorem jointEdgeBallBuild_extract_ae (κ : Type*) [Fintype κ] (m k : ℕ) (energy : ℝ)
    (μ : Measure ((κ × EdgeBallVertex (m + 2) k) → ℝ))
    (hs : ∀ᵐ x ∂μ, ∀ c, EdgeBallEigenrelation m k energy (fun v => x (c, v))) :
    (jointEdgeBallBuild κ m k energy : _ → _) ∘ jointEdgeBallExtract κ m k =ᵐ[μ] id := by
  filter_upwards [hs] with x hx
  funext ⟨c, v⟩
  exact congrFun (edgeBallBuild_extract m k energy (fun v => x (c, v)) (hx c)) v

theorem map_jointVertexBallBuild_extract (κ : Type*) [Fintype κ] (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (μ : Measure ((κ × VertexBallVertex (m + 2) k) → ℝ))
    (hs : ∀ᵐ x ∂μ, ∀ c, VertexBallEigenrelation m k energy (fun v => x (c, v))) :
    Measure.map (jointVertexBallBuild κ m k energy) (Measure.map (jointVertexBallExtract κ m k) μ) = μ := by
  rw [Measure.map_map (jointVertexBallBuild κ m k energy).continuous_of_finiteDimensional.measurable
    (jointVertexBallExtract κ m k).continuous_of_finiteDimensional.measurable,
    Measure.map_congr (jointVertexBallBuild_extract_ae κ m k energy hne μ hs), Measure.map_id]

theorem map_jointEdgeBallBuild_extract (κ : Type*) [Fintype κ] (m k : ℕ) (energy : ℝ)
    (μ : Measure ((κ × EdgeBallVertex (m + 2) k) → ℝ))
    (hs : ∀ᵐ x ∂μ, ∀ c, EdgeBallEigenrelation m k energy (fun v => x (c, v))) :
    Measure.map (jointEdgeBallBuild κ m k energy) (Measure.map (jointEdgeBallExtract κ m k) μ) = μ := by
  rw [Measure.map_map (jointEdgeBallBuild κ m k energy).continuous_of_finiteDimensional.measurable
    (jointEdgeBallExtract κ m k).continuous_of_finiteDimensional.measurable,
    Measure.map_congr (jointEdgeBallBuild_extract_ae κ m k energy μ hs), Measure.map_id]

theorem joint_vertex_edge_chart_identity (κ : Type*) (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (a : Fin (m + 2)) :
    (jointEdgeBallExtract κ m (k + 1) : _ → _) ∘ jointCoordinateRestriction κ (edgeInVertexCover m k a) ∘
      jointVertexBallBuild κ m (k + 1) energy =
      (coloredLocalEdgeInnovationEquiv κ m k energy hne a : _ → _) ∘
        innovationLocalProjection (coloredForestSplit κ (Fin (m + 2)) m k) a := by
  funext x ⟨c, j⟩
  have h := congrArg (edgeBallExtract m (k + 1)) (colored_edge_window_reconstruction κ m k energy hne a x c)
  rw [edgeBallExtract_build] at h
  exact (congrFun h j).symm

theorem joint_edge_vertex_chart_identity (κ : Type*) (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (b : Bool) :
    (jointVertexBallExtract κ m k : _ → _) ∘ jointCoordinateRestriction κ (vertexInEdgeCover m k b) ∘
      jointEdgeBallBuild κ m (k + 1) energy =
      (coloredLocalVertexInnovationEquiv κ m k energy hne b : _ → _) ∘
        innovationLocalProjection (coloredForestSplit κ Bool m k) b := by
  funext x ⟨c, j⟩
  have h := congrArg (vertexBallExtract m k) (colored_vertex_window_reconstruction κ m k energy hne b x c)
  rw [vertexBallExtract_build] at h
  exact (congrFun h j).symm

theorem joint_vertex_core_chart_identity (κ : Type*) (m k : ℕ) (energy : ℝ) :
    (jointVertexBallExtract κ m k : _ → _) ∘ jointCoordinateRestriction κ (vertexBallInclusion m k) ∘
      jointVertexBallBuild κ m (k + 1) energy =
      innovationCoreProjection (coloredForestSplit κ (Fin (m + 2)) m k) := by
  funext x ⟨c, j⟩
  change vertexBallExtract m k (fun v => vertexBallBuild m (k + 1) energy
    (fun i => x (c, i)) (vertexBallInclusion m k v)) j =
      x (c, (forestInnovationSplit (Fin (m + 2)) m k).symm (Sum.inl j))
  rw [vertexBallBuild_restrict, vertexBallExtract_build, forestInnovationSplit_symm_old]
  rfl

theorem joint_edge_core_chart_identity (κ : Type*) (m k : ℕ) (energy : ℝ) :
    (jointEdgeBallExtract κ m k : _ → _) ∘ jointCoordinateRestriction κ (edgeBallInclusion m k) ∘
      jointEdgeBallBuild κ m (k + 1) energy = innovationCoreProjection (coloredForestSplit κ Bool m k) := by
  funext x ⟨c, j⟩
  change edgeBallExtract m k (fun v => edgeBallBuild m (k + 1) energy
    (fun i => x (c, i)) (edgeBallInclusion m k v)) j =
      x (c, (forestInnovationSplit Bool m k).symm (Sum.inl j))
  rw [edgeBallBuild_restrict, edgeBallExtract_build, forestInnovationSplit_symm_old]
  rfl

theorem map_chart_of_reconstruction {X Z U T : Type*}
    [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace U] [MeasurableSpace T]
    (μ : Measure X) (extract : X → Z) (build : Z → X) (window : X → U) (out : U → T)
    (chart : Z → T) (hb : Measurable build) (hw : Measurable window) (ho : Measurable out)
    (hrestore : Measure.map build (Measure.map extract μ) = μ)
    (hchart : out ∘ window ∘ build = chart) :
    Measure.map chart (Measure.map extract μ) = Measure.map out (Measure.map window μ) := by
  rw [← hchart, ← Measure.map_map ho (hw.comp hb), ← Measure.map_map hw hb, hrestore]

theorem vertex_physical_edge_marginal (κ : Type*) [Fintype κ] (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (a : Fin (m + 2))
    (μ : Measure ((κ × VertexBallVertex (m + 2) (k + 1)) → ℝ))
    (hs : ∀ᵐ x ∂μ, ∀ c, VertexBallEigenrelation m (k + 1) energy (fun v => x (c, v))) :
    Measure.map ((coloredLocalEdgeInnovationEquiv κ m k energy hne a : _ → _) ∘
      innovationLocalProjection (coloredForestSplit κ (Fin (m + 2)) m k) a)
      (Measure.map (jointVertexBallExtract κ m (k + 1)) μ) =
      Measure.map (jointEdgeBallExtract κ m (k + 1))
        (Measure.map (jointCoordinateRestriction κ (edgeInVertexCover m k a)) μ) :=
  map_chart_of_reconstruction μ _ _ _ _ _
    (jointVertexBallBuild κ m (k + 1) energy).continuous_of_finiteDimensional.measurable
    (jointCoordinateRestriction κ (edgeInVertexCover m k a)).continuous_of_finiteDimensional.measurable
    (jointEdgeBallExtract κ m (k + 1)).continuous_of_finiteDimensional.measurable
    (map_jointVertexBallBuild_extract κ m (k + 1) energy hne μ hs)
    (joint_vertex_edge_chart_identity κ m k energy hne a)

theorem edge_physical_vertex_marginal (κ : Type*) [Fintype κ] (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (b : Bool)
    (μ : Measure ((κ × EdgeBallVertex (m + 2) (k + 1)) → ℝ))
    (hs : ∀ᵐ x ∂μ, ∀ c, EdgeBallEigenrelation m (k + 1) energy (fun v => x (c, v))) :
    Measure.map ((coloredLocalVertexInnovationEquiv κ m k energy hne b : _ → _) ∘
      innovationLocalProjection (coloredForestSplit κ Bool m k) b)
      (Measure.map (jointEdgeBallExtract κ m (k + 1)) μ) =
      Measure.map (jointVertexBallExtract κ m k)
        (Measure.map (jointCoordinateRestriction κ (vertexInEdgeCover m k b)) μ) :=
  map_chart_of_reconstruction μ _ _ _ _ _
    (jointEdgeBallBuild κ m (k + 1) energy).continuous_of_finiteDimensional.measurable
    (jointCoordinateRestriction κ (vertexInEdgeCover m k b)).continuous_of_finiteDimensional.measurable
    (jointVertexBallExtract κ m k).continuous_of_finiteDimensional.measurable
    (map_jointEdgeBallBuild_extract κ m (k + 1) energy μ hs)
    (joint_edge_vertex_chart_identity κ m k energy hne b)

theorem vertex_physical_core_marginal (κ : Type*) [Fintype κ] (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ))
    (μ : Measure ((κ × VertexBallVertex (m + 2) (k + 1)) → ℝ))
    (hs : ∀ᵐ x ∂μ, ∀ c, VertexBallEigenrelation m (k + 1) energy (fun v => x (c, v))) :
    Measure.map (innovationCoreProjection (coloredForestSplit κ (Fin (m + 2)) m k))
      (Measure.map (jointVertexBallExtract κ m (k + 1)) μ) =
      Measure.map (jointVertexBallExtract κ m k)
        (Measure.map (jointCoordinateRestriction κ (vertexBallInclusion m k)) μ) :=
  map_chart_of_reconstruction μ _ _ _ _ _
    (jointVertexBallBuild κ m (k + 1) energy).continuous_of_finiteDimensional.measurable
    (jointCoordinateRestriction κ (vertexBallInclusion m k)).continuous_of_finiteDimensional.measurable
    (jointVertexBallExtract κ m k).continuous_of_finiteDimensional.measurable
    (map_jointVertexBallBuild_extract κ m (k + 1) energy hne μ hs)
    (joint_vertex_core_chart_identity κ m k energy)

theorem edge_physical_core_marginal (κ : Type*) [Fintype κ] (m k : ℕ) (energy : ℝ)
    (μ : Measure ((κ × EdgeBallVertex (m + 2) (k + 1)) → ℝ))
    (hs : ∀ᵐ x ∂μ, ∀ c, EdgeBallEigenrelation m (k + 1) energy (fun v => x (c, v))) :
    Measure.map (innovationCoreProjection (coloredForestSplit κ Bool m k))
      (Measure.map (jointEdgeBallExtract κ m (k + 1)) μ) =
      Measure.map (jointEdgeBallExtract κ m k)
        (Measure.map (jointCoordinateRestriction κ (edgeBallInclusion m k)) μ) :=
  map_chart_of_reconstruction μ _ _ _ _ _
    (jointEdgeBallBuild κ m (k + 1) energy).continuous_of_finiteDimensional.measurable
    (jointCoordinateRestriction κ (edgeBallInclusion m k)).continuous_of_finiteDimensional.measurable
    (jointEdgeBallExtract κ m k).continuous_of_finiteDimensional.measurable
    (map_jointEdgeBallBuild_extract κ m (k + 1) energy μ hs)
    (joint_edge_core_chart_identity κ m k energy)

end GaussianWave.BS
