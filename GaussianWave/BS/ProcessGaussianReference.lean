import GaussianWave.BS.ProcessBallMarginals
import GaussianWave.BS.JointBallInnovationReference
import GaussianWave.BS.IndependentChannelLaw
import GaussianWave.BS.EdgeBallDistances

/-! Canonical finite reference laws are the actual marginals of the whole
Gaussian process, and exhausting joint balls determine the whole law. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GaussianWave.BS

theorem jointGaussianTreeProcessLaw_vertex_ball (r m k : ℕ) (energy : ℝ) :
    jointVertexProcessBallLaw (jointGaussianTreeProcessLaw r m energy) k =
      independentChannelLaw (fun _ : Fin r => vertexGaussianBallLaw m k energy) := by
  change Measure.map (fun z : (Fin r × RegularTreeVertex (m + 2)) → ℝ =>
      fun av : Fin r × VertexBallVertex (m + 2) k => z (av.1, vertexBallEmbedding (m + 2) k av.2))
    (independentChannelLaw (fun _ : Fin r => (gaussianTreeProcessLaw m energy : Measure _))) = _
  rw [independentChannelLaw_window]
  simp only [gaussianTreeProcessLaw_ball]

theorem jointGaussianTreeProcessLaw_edge_ball (r m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    jointEdgeProcessBallLaw (jointGaussianTreeProcessLaw r m energy) k =
      independentChannelLaw (fun _ : Fin r => edgeGaussianBallLaw m k energy) := by
  change Measure.map (fun z : (Fin r × RegularTreeVertex (m + 2)) → ℝ =>
      fun av : Fin r × EdgeBallVertex (m + 2) k => z (av.1, edgeBallEmbedding m k av.2))
    (independentChannelLaw (fun _ : Fin r => (gaussianTreeProcessLaw m energy : Measure _))) = _
  rw [independentChannelLaw_window]
  simp only [gaussianTreeProcessLaw_edge m k energy he]

theorem jointVertexInnovationReference_process_law (r m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    (jointVertexInnovationReference (Fin r) m k energy he).law =
      jointVertexInnovationProcessLaw (jointGaussianTreeProcessLaw r m energy) k := by
  rw [jointVertexInnovationProcessLaw, jointGaussianTreeProcessLaw_vertex_ball,
    jointVertexInnovationReference_law]
  change _ = Measure.map (fun z : (Fin r × VertexBallVertex (m + 2) k) → ℝ =>
    fun aj : Fin r × VertexBallInnovation (m + 2) k => vertexBallExtract m k (fun v => z (aj.1, v)) aj.2) _
  rw [independentChannelLaw_mapVector _ (vertexBallExtract m k) (measurable_vertexBallExtract m k)]
  simp only [vertexGaussianBallLaw_extract]

theorem jointEdgeInnovationReference_process_law (r m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    (jointEdgeInnovationReference (Fin r) m k energy he).law =
      jointEdgeInnovationProcessLaw (jointGaussianTreeProcessLaw r m energy) k := by
  rw [jointEdgeInnovationProcessLaw, jointGaussianTreeProcessLaw_edge_ball r m k energy he,
    jointEdgeInnovationReference_law]
  change _ = Measure.map (fun z : (Fin r × EdgeBallVertex (m + 2) k) → ℝ =>
    fun aj : Fin r × EdgeBallInnovation (m + 2) k => edgeBallExtract m k (fun v => z (aj.1, v)) aj.2) _
  rw [independentChannelLaw_mapVector _ (edgeBallExtract m k) (measurable_edgeBallExtract m k)]
  simp only [edgeGaussianBallLaw_extract]

theorem jointVertexInnovationReference_build (r m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    Measure.map (jointVertexBallBuild (Fin r) m k energy)
      (jointVertexInnovationReference (Fin r) m k energy he).law =
      jointVertexProcessBallLaw (jointGaussianTreeProcessLaw r m energy) k := by
  rw [jointVertexInnovationReference_law, jointGaussianTreeProcessLaw_vertex_ball]
  change Measure.map (fun z : (Fin r × VertexBallInnovation (m + 2) k) → ℝ =>
    fun av : Fin r × VertexBallVertex (m + 2) k => vertexBallBuild m k energy (fun j => z (av.1, j)) av.2) _ = _
  have hB : Measurable (vertexBallBuild m k energy) :=
    (vertexBallBuildLinear m k energy).continuous_of_finiteDimensional.measurable
  rw [independentChannelLaw_mapVector _ (vertexBallBuild m k energy) hB]
  have hphys : Measure.map (vertexBallBuild m k energy)
      (forestGaussianInnovationLaw m k (Real.sqrt (siblingVariance (m + 2) energy))
        (vertexRootInnovationFactor m energy)) = vertexGaussianBallLaw m k energy :=
    forest_vertex_reference_physical_law m k energy
  simp only [hphys]

theorem joint_treeLaw_eq_of_vertex_marginals {r m : ℕ}
    (μ ν : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ k, jointVertexProcessBallLaw μ k = jointVertexProcessBallLaw ν k) : μ = ν := by
  let P := fun S : Finset (Fin r × RegularTreeVertex (m + 2)) => Measure.map S.restrict μ
  letI (S : Finset (Fin r × RegularTreeVertex (m + 2))) : IsFiniteMeasure (P S) := by
    dsimp only [P]
    infer_instance
  have hμ : IsProjectiveLimit μ P := fun _ => rfl
  have hν : IsProjectiveLimit ν P := by
    intro S
    let k := S.sup (fun av => regularTreeDepth av.2)
    have hd (v : S) : regularTreeDepth v.val.2 ≤ k + 1 :=
      (Finset.le_sup v.property).trans (Nat.le_succ k)
    let site : S → Fin r × VertexBallVertex (m + 2) k := fun v =>
      (v.val.1, treeBallIndexOfDepth (m + 2) k v.val.2 (hd v))
    let T := fun z : (Fin r × VertexBallVertex (m + 2) k) → ℝ => fun v : S => z (site v)
    have hT : Measurable T := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
    have he : S.restrict = T ∘ jointTreeWindow (vertexBallEmbedding (m + 2) k) := by
      funext z v
      exact congrArg (fun u => z (v.val.1, u))
        (treeBallIndexOfDepth_spec (m + 2) k v.val.2 (hd v)).symm
    change Measure.map S.restrict ν = Measure.map S.restrict μ
    rw [he, ← Measure.map_map hT (measurable_jointTreeWindow _),
      ← Measure.map_map hT (measurable_jointTreeWindow _)]
    have hh : jointVertexProcessBallLaw μ k = jointVertexProcessBallLaw ν k := h k
    change Measure.map T (jointVertexProcessBallLaw ν k) = Measure.map T (jointVertexProcessBallLaw μ k)
    rw [hh]
  exact hμ.unique hν

theorem process_eq_jointGaussian_of_innovation_balls {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsFiniteMeasure μ]
    (energy : ℝ) (he : |energy| < (m + 2 : ℝ))
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0)
    (hballs : ∀ k, jointVertexInnovationProcessLaw μ k =
      (jointVertexInnovationReference (Fin r) m k energy he).law) :
    μ = jointGaussianTreeProcessLaw r m energy := by
  apply joint_treeLaw_eq_of_vertex_marginals
  intro k
  have hrestore := map_jointVertexBallBuild_extract (Fin r) m k energy
    (ne_of_lt ((le_abs_self energy).trans_lt he)) (jointVertexProcessBallLaw μ k)
    (jointVertexProcessBallLaw_ae_eigenrelation μ k energy (ne_of_lt ((le_abs_self energy).trans_lt he)) hE)
  change Measure.map (jointVertexBallBuild (Fin r) m k energy) (jointVertexInnovationProcessLaw μ k) =
    jointVertexProcessBallLaw μ k at hrestore
  rw [hballs k] at hrestore
  exact hrestore.symm.trans (jointVertexInnovationReference_build r m k energy he)

end GaussianWave.BS
