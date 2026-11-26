import GaussianWave.BS.EdgeCoverMarginal

/-! Actual edge-flip invariance of the whole uniform cover law. The proof
uses the proved symmetric E-ball sampler and its genuine C-ball marginal,
then uniqueness on the exhausting finite-coordinate sigma algebra. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GaussianWave.BS
open Reused.Graph Reused.Graph.Configuration

/-- The exhausting actual E-ball marginals determine an entire finite
process measure, without any invariance contract. -/
theorem treeLaw_eq_of_edge_marginals {A : Type*} [MeasurableSpace A] (m : ℕ)
    (μ ν : Measure (RegularTreeVertex (m+2) → A)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ k, Measure.map
      (fun z : RegularTreeVertex (m+2) → A => fun v => z (edgeBallEmbedding m k v)) μ =
      Measure.map (fun z : RegularTreeVertex (m+2) → A => fun v => z (edgeBallEmbedding m k v)) ν) :
    μ=ν := by
  let P := fun S : Finset (RegularTreeVertex (m+2)) => Measure.map S.restrict μ
  letI (S : Finset (RegularTreeVertex (m+2))) : IsFiniteMeasure (P S) := by
    dsimp only [P]
    infer_instance
  have hμ : IsProjectiveLimit μ P := fun _ => rfl
  have hν : IsProjectiveLimit ν P := by
    intro S
    let k := finiteEdgeDepth m S
    let site : S → EdgeBallVertex (m+2) k := fun v =>
      edgeBallIndexOfDepth m k v.val (edgeDepth_le_finiteEdgeDepth m S v)
    let B := fun z : RegularTreeVertex (m+2) → A => fun v => z (edgeBallEmbedding m k v)
    let T := fun z : EdgeBallVertex (m+2) k → A => fun v : S => z (site v)
    have hB : Measurable B := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
    have hT : Measurable T := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
    have he : S.restrict=T ∘ B := by
      funext z v
      exact congrArg z (edgeBallIndexOfDepth_spec m k v.val (edgeDepth_le_finiteEdgeDepth m S v)).symm
    change Measure.map S.restrict ν=Measure.map S.restrict μ
    rw [he,← Measure.map_map hT hB,← Measure.map_map hT hB]
    have hh : Measure.map B μ=Measure.map B ν := h k
    rw [hh]
  exact hμ.unique hν

/-- Exact invariance of the actual uniform infinite cover under the actual
isomorphism reversing the distinguished edge. -/
theorem uniformTreeCoverLaw_edgeFlip_invariant {N m : ℕ} (G : RegularGraph N (m+2)) (hN : 0<N) :
    Measure.map (fun z : RegularTreeVertex (m+2) → Fin N => fun v => z (regularTreeEdgeFlip (m+1) v))
      (uniformTreeCoverLaw G hN : Measure _)=(uniformTreeCoverLaw G hN : Measure _) := by
  let Q := (uniformTreeCoverLaw G hN : Measure (RegularTreeVertex (m+2) → Fin N))
  let T := fun z : RegularTreeVertex (m+2) → Fin N => fun v => z (regularTreeEdgeFlip (m+1) v)
  have hT : Measurable T := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  letI : IsProbabilityMeasure (Measure.map T Q) := isProbabilityMeasure_map hT.aemeasurable
  apply treeLaw_eq_of_edge_marginals m (Measure.map T Q) Q
  intro k
  let B := fun z : RegularTreeVertex (m+2) → Fin N => fun v => z (edgeBallEmbedding m k v)
  let R := fun z : EdgeBallVertex (m+2) k → Fin N => fun v => z (edgeBallReverse m k v)
  have hB : Measurable B := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hR : Measurable R := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have he : B ∘ T=R ∘ B := by
    funext z v
    exact congrArg z (edgeBallEmbedding_reverse m k v)
  change Measure.map B (Measure.map T Q)=Measure.map B Q
  rw [Measure.map_map hB hT,he,← Measure.map_map hR hB]
  have hE : Measure.map B Q=finiteEdgeCoverImageLaw G k := uniformTreeCoverLaw_edge_ball G hN k
  rw [hE]
  exact finiteEdgeCoverImageLaw_reverse G k

/-- The same proved edge-flip symmetry passes to every actual joint
finite-graph eigenvector coloring of the cover. -/
theorem uniformLiftedTreeLaw_edgeFlip_invariant {N m r : ℕ} (G : RegularGraph N (m+2))
    (hN : 0<N) (f : Fin r → Fin N → ℝ) :
    Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => fun av =>
      z (av.1,regularTreeEdgeFlip (m+1) av.2)) (uniformLiftedTreeLaw G hN f)=uniformLiftedTreeLaw G hN f := by
  let C := fun z : RegularTreeVertex (m+2) → Fin N => fun av : Fin r × RegularTreeVertex (m+2) => f av.1 (z av.2)
  let T := fun z : RegularTreeVertex (m+2) → Fin N => fun v => z (regularTreeEdgeFlip (m+1) v)
  let U := fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => fun av : Fin r × RegularTreeVertex (m+2) =>
    z (av.1,regularTreeEdgeFlip (m+1) av.2)
  have hC : Measurable C := measurable_treeColoring f
  have hT : Measurable T := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hU : Measurable U := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have he : U ∘ C=C ∘ T := rfl
  change Measure.map U (Measure.map C (uniformTreeCoverLaw G hN : Measure _))=_
  rw [Measure.map_map hU hC,he,← Measure.map_map hC hT,uniformTreeCoverLaw_edgeFlip_invariant]
  rfl

end GaussianWave.BS
