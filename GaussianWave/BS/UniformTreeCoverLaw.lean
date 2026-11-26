import GaussianWave.BS.CompactBallProcessExtension
import GaussianWave.BS.FiniteCoverConsistency
import GaussianWave.BS.FiniteAtomicLaws

/-!
# Actual uniform infinite tree-cover sampling law

Uniform local neighbor permutations give compatible finite graph-valued
cover laws. The proved compact process extension constructs their whole
law. Every finite real/vector coloring law is identified with the literal
finite cover sampler, rather than supplied as an adapter field.
-/
noncomputable section
open MeasureTheory
open scoped Topology Classical
namespace GaussianWave.BS
open Reused.Graph Reused.Graph.Configuration

def finiteVertexCoverImageLaw {N m : ℕ} (G : RegularGraph N (m + 2)) (k : ℕ) :
    Measure (VertexBallVertex (m + 2) k → Fin N) :=
  uniformAtomicLaw (vertexGraphCover G k)

theorem finiteVertexCoverImageLaw_isProbability {N m : ℕ} (G : RegularGraph N (m + 2))
    (hN : 0 < N) (k : ℕ) : IsProbabilityMeasure (finiteVertexCoverImageLaw G k) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact uniformAtomicLaw_isProbability _

theorem finiteVertexCoverImageLaw_consistent {N m : ℕ} (G : RegularGraph N (m + 2)) (k : ℕ) :
    Measure.map (fun x : VertexBallVertex (m + 2) (k + 1) → Fin N =>
      fun v => x (vertexBallInclusion m k v)) (finiteVertexCoverImageLaw G (k + 1)) =
        finiteVertexCoverImageLaw G k := by
  apply uniformAtomicLaw_projection (vertexCoverSeedDepthEquiv N m k)
    (vertexGraphCover G (k + 1)) (vertexGraphCover G k) _
    (measurable_pi_lambda _ (fun v => measurable_pi_apply _))
  intro z
  funext v
  rw [vertexGraphCover_restrict]
  have hz := congrArg Prod.fst ((vertexCoverSeedDepthEquiv N m k).apply_symm_apply z)
  change vertexCoverSeedTruncate N m k ((vertexCoverSeedDepthEquiv N m k).symm z) = z.1 at hz
  rw [hz]

theorem exists_uniformTreeCoverLaw {N m : ℕ} (G : RegularGraph N (m + 2)) (hN : 0 < N) :
    ∃ Q : ProbabilityMeasure (RegularTreeVertex (m + 2) → Fin N), ∀ k,
      Measure.map (fun x : RegularTreeVertex (m + 2) → Fin N =>
        fun v => x (vertexBallEmbedding (m + 2) k v)) (Q : Measure _) = finiteVertexCoverImageLaw G k := by
  letI : Inhabited (Fin N) := ⟨⟨0, hN⟩⟩
  letI : MetricSpace (Fin N) := TopologicalSpace.metrizableSpaceMetric (Fin N)
  exact exists_compact_tree_processLaw_of_ball_marginals m
    (fun k => ⟨finiteVertexCoverImageLaw G k, finiteVertexCoverImageLaw_isProbability G hN k⟩)
    (finiteVertexCoverImageLaw_consistent G)

def uniformTreeCoverLaw {N m : ℕ} (G : RegularGraph N (m + 2)) (hN : 0 < N) :
    ProbabilityMeasure (RegularTreeVertex (m + 2) → Fin N) :=
  Classical.choose (exists_uniformTreeCoverLaw G hN)

theorem uniformTreeCoverLaw_ball {N m : ℕ} (G : RegularGraph N (m + 2)) (hN : 0 < N) (k : ℕ) :
    Measure.map (fun x : RegularTreeVertex (m + 2) → Fin N =>
      fun v => x (vertexBallEmbedding (m + 2) k v))
      (uniformTreeCoverLaw G hN : Measure _) = finiteVertexCoverImageLaw G k :=
  Classical.choose_spec (exists_uniformTreeCoverLaw G hN) k

def uniformLiftedTreeLaw {N m r : ℕ} (G : RegularGraph N (m + 2)) (hN : 0 < N)
    (f : Fin r → Fin N → ℝ) : Measure ((Fin r × RegularTreeVertex (m + 2)) → ℝ) :=
  Measure.map (fun x : RegularTreeVertex (m + 2) → Fin N => fun av => f av.1 (x av.2))
    (uniformTreeCoverLaw G hN : Measure _)

theorem measurable_treeColoring {N m r : ℕ} (f : Fin r → Fin N → ℝ) :
    Measurable (fun x : RegularTreeVertex (m + 2) → Fin N => fun av : Fin r × RegularTreeVertex (m + 2) =>
      f av.1 (x av.2)) :=
  measurable_pi_lambda _ (fun av => (measurable_of_finite (f av.1)).comp (measurable_pi_apply av.2))

instance uniformLiftedTreeLaw_probability {N m r : ℕ} (G : RegularGraph N (m + 2)) (hN : 0 < N)
    (f : Fin r → Fin N → ℝ) : IsProbabilityMeasure (uniformLiftedTreeLaw G hN f) :=
  isProbabilityMeasure_map (measurable_treeColoring f).aemeasurable

theorem uniformLiftedTreeLaw_ball {N m r : ℕ} (G : RegularGraph N (m + 2)) (hN : 0 < N)
    (f : Fin r → Fin N → ℝ) (k : ℕ) :
    Measure.map (fun x : (Fin r × RegularTreeVertex (m + 2)) → ℝ =>
      fun av : Fin r × VertexBallVertex (m + 2) k => x (av.1, vertexBallEmbedding (m + 2) k av.2))
      (uniformLiftedTreeLaw G hN f) = finiteVertexCoverLaw G k f := by
  let T := fun x : RegularTreeVertex (m + 2) → Fin N =>
    fun v => x (vertexBallEmbedding (m + 2) k v)
  let C := fun x : VertexBallVertex (m + 2) k → Fin N =>
    fun av : Fin r × VertexBallVertex (m + 2) k => f av.1 (x av.2)
  have hT : Measurable T := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hC : Measurable C := measurable_pi_lambda _
    (fun av => (measurable_of_finite (f av.1)).comp (measurable_pi_apply av.2))
  rw [uniformLiftedTreeLaw, Measure.map_map
    (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)) (measurable_treeColoring f)]
  change Measure.map (C ∘ T) (uniformTreeCoverLaw G hN : Measure _) = _
  rw [← Measure.map_map hC hT, uniformTreeCoverLaw_ball, finiteVertexCoverImageLaw,
    uniformAtomicLaw_map _ C hC]
  rfl

end GaussianWave.BS
