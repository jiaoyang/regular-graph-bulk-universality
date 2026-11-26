import GaussianWave.BS.BallOverlapAutomorphisms
import GaussianWave.BS.BallPhysicalMarginals
import GaussianWave.BS.TreeEigenWindowSupport

/-! Actual finite C/E window laws of an invariant joint eigenprocess have
all the physical and canonical innovation marginals used by relative SSA. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

def jointTreeWindow {r d : ℕ} {I : Type*} (site : I → RegularTreeVertex d)
    (x : (Fin r × RegularTreeVertex d) → ℝ) : (Fin r × I) → ℝ :=
  fun ci => x (ci.1, site ci.2)

theorem measurable_jointTreeWindow {r d : ℕ} {I : Type*} (site : I → RegularTreeVertex d) :
    Measurable (jointTreeWindow (r := r) site) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

def jointVertexProcessBallLaw {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (k : ℕ) :=
  Measure.map (jointTreeWindow (vertexBallEmbedding (m + 2) k)) μ

def jointEdgeProcessBallLaw {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (k : ℕ) :=
  Measure.map (jointTreeWindow (edgeBallEmbedding m k)) μ

instance jointVertexProcessBallLaw_probability {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ] (k : ℕ) :
    IsProbabilityMeasure (jointVertexProcessBallLaw μ k) :=
  isProbabilityMeasure_map (measurable_jointTreeWindow _).aemeasurable

instance jointEdgeProcessBallLaw_probability {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsProbabilityMeasure μ] (k : ℕ) :
    IsProbabilityMeasure (jointEdgeProcessBallLaw μ k) :=
  isProbabilityMeasure_map (measurable_jointTreeWindow _).aemeasurable

theorem jointTreeWindowLaw_invariant {r d : ℕ} {I : Type*}
    (μ : Measure ((Fin r × RegularTreeVertex d) → ℝ)) (hμ : ChannelTreeInvariant μ)
    (e : regularWordTree d ≃g regularWordTree d) (site : I → RegularTreeVertex d) :
    Measure.map (jointTreeWindow (fun i => e (site i))) μ = Measure.map (jointTreeWindow site) μ := by
  have h := congrArg (Measure.map (jointTreeWindow site)) (hμ e)
  rw [Measure.map_map (measurable_jointTreeWindow site) (measurable_channelTreeRelabel e)] at h
  exact h

theorem jointVertexProcessBallLaw_edge_window {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (hμ : ChannelTreeInvariant μ)
    (k : ℕ) (a : Fin (m + 2)) :
    Measure.map (jointCoordinateRestriction (Fin r) (edgeInVertexCover m k a))
      (jointVertexProcessBallLaw μ (k + 1)) = jointEdgeProcessBallLaw μ (k + 1) := by
  rw [jointVertexProcessBallLaw, jointEdgeProcessBallLaw,
    Measure.map_map (jointCoordinateRestriction (Fin r) (edgeInVertexCover m k a)).continuous_of_finiteDimensional.measurable
      (measurable_jointTreeWindow _)]
  have hf : (jointCoordinateRestriction (Fin r) (edgeInVertexCover m k a) : _ → _) ∘
      jointTreeWindow (vertexBallEmbedding (m + 2) (k + 1)) =
      jointTreeWindow (fun v => regularTreeRootPermutation (m + 2) (rootNeighborPermutation a)
        (edgeBallEmbedding m (k + 1) v)) := by
    funext x ⟨c, v⟩
    exact congrArg (fun u => x (c, u)) (edgeInVertexCover_embedding m k a v)
  rw [hf]
  exact jointTreeWindowLaw_invariant μ hμ _ _

theorem jointEdgeProcessBallLaw_vertex_window {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (hμ : ChannelTreeInvariant μ)
    (k : ℕ) (b : Bool) :
    Measure.map (jointCoordinateRestriction (Fin r) (vertexInEdgeCover m k b))
      (jointEdgeProcessBallLaw μ (k + 1)) = jointVertexProcessBallLaw μ k := by
  rw [jointVertexProcessBallLaw, jointEdgeProcessBallLaw,
    Measure.map_map (jointCoordinateRestriction (Fin r) (vertexInEdgeCover m k b)).continuous_of_finiteDimensional.measurable
      (measurable_jointTreeWindow _)]
  cases b
  · congr 1
    funext x ⟨c, v⟩
    exact congrArg (fun u => x (c, u)) (vertexInEdgeCover_false_embedding m k v)
  · have hf : (jointCoordinateRestriction (Fin r) (vertexInEdgeCover m k true) : _ → _) ∘
        jointTreeWindow (edgeBallEmbedding m (k + 1)) =
        jointTreeWindow (fun v => regularTreeEdgeFlip (m + 1) (vertexBallEmbedding (m + 2) k v)) := by
      funext x ⟨c, v⟩
      exact congrArg (fun u => x (c, u)) (vertexInEdgeCover_true_embedding m k v)
    rw [hf]
    exact jointTreeWindowLaw_invariant μ hμ _ _

theorem jointVertexProcessBallLaw_core {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (k : ℕ) :
    Measure.map (jointCoordinateRestriction (Fin r) (vertexBallInclusion m k))
      (jointVertexProcessBallLaw μ (k + 1)) = jointVertexProcessBallLaw μ k := by
  rw [jointVertexProcessBallLaw, jointVertexProcessBallLaw,
    Measure.map_map (jointCoordinateRestriction (Fin r) (vertexBallInclusion m k)).continuous_of_finiteDimensional.measurable
      (measurable_jointTreeWindow _)]
  congr 1
  funext x ⟨c, v⟩
  exact congrArg (fun u => x (c, u)) (vertexBallEmbedding_inclusion m k v)

theorem jointEdgeProcessBallLaw_core {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (k : ℕ) :
    Measure.map (jointCoordinateRestriction (Fin r) (edgeBallInclusion m k))
      (jointEdgeProcessBallLaw μ (k + 1)) = jointEdgeProcessBallLaw μ k := by
  rw [jointEdgeProcessBallLaw, jointEdgeProcessBallLaw,
    Measure.map_map (jointCoordinateRestriction (Fin r) (edgeBallInclusion m k)).continuous_of_finiteDimensional.measurable
      (measurable_jointTreeWindow _)]
  congr 1
  funext x ⟨c, v⟩
  exact congrArg (fun u => x (c, u)) (edgeBallEmbedding_inclusion m k v)

theorem jointVertexProcessBallLaw_ae_eigenrelation {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ))
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0) :
    ∀ᵐ y ∂jointVertexProcessBallLaw μ k, ∀ c,
      VertexBallEigenrelation m k energy (fun v => y (c, v)) := by
  have hAll : ∀ᵐ x ∂μ, ∀ a u, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0 :=
    (ae_all_iff).mpr (fun a => (ae_all_iff).mpr (hE a))
  have h := map_vertexBall_ae_eigenSpace m k r (fun _ => energy)
    (fun _ => by simpa only [Nat.cast_add, Nat.cast_ofNat] using hne) μ hAll
  filter_upwards [h] with y hy
  intro c
  exact (mem_vertexBallEigenSpace_iff m k energy hne _).mp (hy c)

theorem jointEdgeProcessBallLaw_ae_eigenrelation {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (k : ℕ) (energy : ℝ)
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0) :
    ∀ᵐ y ∂jointEdgeProcessBallLaw μ k, ∀ c,
      EdgeBallEigenrelation m k energy (fun v => y (c, v)) := by
  have hAll : ∀ᵐ x ∂μ, ∀ a u, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0 :=
    (ae_all_iff).mpr (fun a => (ae_all_iff).mpr (hE a))
  have h := map_edgeBall_ae_eigenSpace m k r (fun _ => energy) μ hAll
  filter_upwards [h] with y hy
  intro c
  exact (mem_edgeBallEigenSpace_iff m k energy _).mp (hy c)

def jointVertexInnovationProcessLaw {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (k : ℕ) :=
  Measure.map (jointVertexBallExtract (Fin r) m k) (jointVertexProcessBallLaw μ k)

def jointEdgeInnovationProcessLaw {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (k : ℕ) :=
  Measure.map (jointEdgeBallExtract (Fin r) m k) (jointEdgeProcessBallLaw μ k)

theorem jointVertexInnovationProcessLaw_local {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (hμ : ChannelTreeInvariant μ)
    (k : ℕ) (energy : ℝ) (hne : energy ≠ (m + 2 : ℝ))
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0)
    (a : Fin (m + 2)) :
    Measure.map ((coloredLocalEdgeInnovationEquiv (Fin r) m k energy hne a : _ → _) ∘
      innovationLocalProjection (coloredForestSplit (Fin r) (Fin (m + 2)) m k) a)
      (jointVertexInnovationProcessLaw μ (k + 1)) = jointEdgeInnovationProcessLaw μ (k + 1) := by
  rw [jointVertexInnovationProcessLaw, vertex_physical_edge_marginal (Fin r) m k energy hne a _
    (jointVertexProcessBallLaw_ae_eigenrelation μ (k + 1) energy hne hE),
    jointVertexProcessBallLaw_edge_window μ hμ]
  rfl

theorem jointEdgeInnovationProcessLaw_local {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (hμ : ChannelTreeInvariant μ)
    (k : ℕ) (energy : ℝ) (hne : energy ≠ (m + 2 : ℝ))
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0)
    (b : Bool) :
    Measure.map ((coloredLocalVertexInnovationEquiv (Fin r) m k energy hne b : _ → _) ∘
      innovationLocalProjection (coloredForestSplit (Fin r) Bool m k) b)
      (jointEdgeInnovationProcessLaw μ (k + 1)) = jointVertexInnovationProcessLaw μ k := by
  rw [jointEdgeInnovationProcessLaw, edge_physical_vertex_marginal (Fin r) m k energy hne b _
    (jointEdgeProcessBallLaw_ae_eigenrelation μ (k + 1) energy hE),
    jointEdgeProcessBallLaw_vertex_window μ hμ]
  rfl

theorem jointVertexInnovationProcessLaw_core {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ))
    (k : ℕ) (energy : ℝ) (hne : energy ≠ (m + 2 : ℝ))
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0) :
    Measure.map (innovationCoreProjection (coloredForestSplit (Fin r) (Fin (m + 2)) m k))
      (jointVertexInnovationProcessLaw μ (k + 1)) = jointVertexInnovationProcessLaw μ k := by
  rw [jointVertexInnovationProcessLaw, vertex_physical_core_marginal (Fin r) m k energy hne _
    (jointVertexProcessBallLaw_ae_eigenrelation μ (k + 1) energy hne hE),
    jointVertexProcessBallLaw_core]
  rfl

theorem jointEdgeInnovationProcessLaw_core {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ))
    (k : ℕ) (energy : ℝ)
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0) :
    Measure.map (innovationCoreProjection (coloredForestSplit (Fin r) Bool m k))
      (jointEdgeInnovationProcessLaw μ (k + 1)) = jointEdgeInnovationProcessLaw μ k := by
  rw [jointEdgeInnovationProcessLaw, edge_physical_core_marginal (Fin r) m k energy _
    (jointEdgeProcessBallLaw_ae_eigenrelation μ (k + 1) energy hE), jointEdgeProcessBallLaw_core]
  rfl

end GaussianWave.BS
