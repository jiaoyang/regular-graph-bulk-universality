import GaussianWave.BS.ProcessGaussianReference
import GaussianWave.BS.BallGaussianPropagation

/-! Actual exhausting Gaussian balls determine the complete process law.
This module is the gluing propagation step after entropy comparison has
proved its gaps vanish. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

theorem jointVertexProcessBallLaw_edge_subball {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) (k : ℕ) :
    Measure.map (jointCoordinateRestriction (Fin r) (edgeToVertexBall m k))
      (jointVertexProcessBallLaw μ k) = jointEdgeProcessBallLaw μ k := by
  rw [jointVertexProcessBallLaw, jointEdgeProcessBallLaw,
    Measure.map_map (jointCoordinateRestriction (Fin r) (edgeToVertexBall m k)).continuous_of_finiteDimensional.measurable
      (measurable_jointTreeWindow _)]
  congr 1
  funext x ⟨c, v⟩
  exact congrArg (fun u => x (c, u)) (edgeToVertexBall_embedding m k v)

theorem edge_innovation_gaussian_of_vertex_innovation_gaussian {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ))
    (k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ))
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0)
    (hC : jointVertexInnovationProcessLaw μ k = (jointVertexInnovationReference (Fin r) m k energy he).law) :
    jointEdgeInnovationProcessLaw μ k = (jointEdgeInnovationReference (Fin r) m k energy he).law := by
  have hrestore := map_jointVertexBallBuild_extract (Fin r) m k energy
    (ne_of_lt ((le_abs_self energy).trans_lt he)) (jointVertexProcessBallLaw μ k)
    (jointVertexProcessBallLaw_ae_eigenrelation μ k energy (ne_of_lt ((le_abs_self energy).trans_lt he)) hE)
  change Measure.map (jointVertexBallBuild (Fin r) m k energy) (jointVertexInnovationProcessLaw μ k) =
    jointVertexProcessBallLaw μ k at hrestore
  rw [hC] at hrestore
  have hphysical := hrestore.symm.trans (jointVertexInnovationReference_build r m k energy he)
  have hEdge := congrArg (Measure.map (jointCoordinateRestriction (Fin r) (edgeToVertexBall m k))) hphysical
  rw [jointVertexProcessBallLaw_edge_subball, jointVertexProcessBallLaw_edge_subball] at hEdge
  have hraw := congrArg (Measure.map (jointEdgeBallExtract (Fin r) m k)) hEdge
  exact hraw.trans (jointEdgeInnovationReference_process_law r m k energy he).symm

theorem process_eq_jointGaussian_of_zero_gaps {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ)) [IsFiniteMeasure μ]
    (hμ : ChannelTreeInvariant μ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ))
    (hE : ∀ a u, ∀ᵐ x ∂μ, treeEigenResidual (m + 2) r (fun _ => energy) a u x = 0)
    (C : ∀ k, PositiveEntropyDensity (volume : Measure ((Fin r × VertexBallInnovation (m + 2) k) → ℝ)))
    (E : ∀ k, PositiveEntropyDensity (volume : Measure ((Fin r × EdgeBallInnovation (m + 2) k) → ℝ)))
    (hC : ∀ k, (C k).law = jointVertexInnovationProcessLaw μ k)
    (hEE : ∀ k, (E k).law = jointEdgeInnovationProcessLaw μ k)
    (hC0 : (C 0).law = (jointVertexInnovationReference (Fin r) m 0 energy he).law)
    (hA : ∀ k, (m + 2 : ℝ) * edgeBallRelativeEntropy (Fin r) m (k + 1) energy he (E (k + 1)) -
      ((m + 2 : ℝ) - 1) * vertexBallRelativeEntropy (Fin r) m k energy he (C k) -
      vertexBallRelativeEntropy (Fin r) m (k + 1) energy he (C (k + 1)) = 0)
    (hB : ∀ k, 2 * vertexBallRelativeEntropy (Fin r) m k energy he (C k) -
      edgeBallRelativeEntropy (Fin r) m k energy he (E k) -
      edgeBallRelativeEntropy (Fin r) m (k + 1) energy he (E (k + 1)) = 0) :
    μ = jointGaussianTreeProcessLaw r m energy := by
  have hE0 : (E 0).law = (jointEdgeInnovationReference (Fin r) m 0 energy he).law :=
    (hEE 0).trans (edge_innovation_gaussian_of_vertex_innovation_gaussian μ 0 energy he hE
      ((hC 0).symm.trans hC0))
  have hAll := all_ball_laws_eq_gaussian_of_zero_gaps (Fin r) m energy he C E
    (fun k a => by rw [hC, jointVertexInnovationProcessLaw_local μ hμ k energy
      (ne_of_lt ((le_abs_self energy).trans_lt he)) hE, ← hEE])
    (fun k => by rw [hC, jointVertexInnovationProcessLaw_core μ k energy
      (ne_of_lt ((le_abs_self energy).trans_lt he)) hE, ← hC])
    (fun k b => by rw [hEE, jointEdgeInnovationProcessLaw_local μ hμ k energy
      (ne_of_lt ((le_abs_self energy).trans_lt he)) hE, ← hC])
    (fun k => by rw [hEE, jointEdgeInnovationProcessLaw_core μ k energy hE, ← hEE])
    hC0 hE0 hA hB
  apply process_eq_jointGaussian_of_innovation_balls μ energy he hE
  intro k
  exact (hC k).symm.trans (hAll k).1

end GaussianWave.BS
