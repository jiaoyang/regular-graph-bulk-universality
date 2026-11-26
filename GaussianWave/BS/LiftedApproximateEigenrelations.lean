import GaussianWave.BS.LiftedCoverEigenrelations

/-! Approximate graph eigenvectors have their literal empirical squared
residual at every site of the actual uniform cover. Thus graph L2 residual
control supplies the process residual hypothesis used by weak-limit
preservation, without a graph-to-process residual contract. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph Reused.Graph.Configuration

private theorem uniformAtomicLaw_ae_of_forall {A E : Type*} [Fintype A]
    [MeasurableSpace E] [MeasurableSingletonClass E] (mark : A → E) (p : E → Prop)
    (h : ∀ a, p (mark a)) : ∀ᵐ x ∂uniformAtomicLaw mark, p x := by
  rw [ae_iff]
  have hz : (∑ a : A, Measure.dirac (mark a)) {x | ¬p x}=0 := by
    rw [Measure.finset_sum_apply]
    apply Finset.sum_eq_zero
    intro a ha
    have hn : mark a ∉ {x | ¬p x} := by simpa only [Set.mem_setOf_eq,not_not] using h a
    rw [Measure.dirac_apply,Set.indicator_of_not_mem hn]
  simp only [uniformAtomicLaw,Measure.smul_apply,hz,smul_eq_mul,mul_zero]

/-- The actual finite-graph adjacency residual, with literal neighbor ports. -/
def graphEigenResidual {N d : ℕ} (G : RegularGraph N d) (energy : ℝ) (f : Fin N → ℝ) (v : Fin N) : ℝ :=
  (∑ j, f (graphNeighbor G v j))-energy*f v

private theorem integral_uniformLiftedTreeLaw_residual_sq_root {N m r : ℕ}
    (G : RegularGraph N (m+2)) (hN : 0<N) (energy : Fin r → ℝ) (f : Fin r → Fin N → ℝ) (a : Fin r) :
    (∫ x, treeEigenResidual (m+2) r energy a none x^2 ∂uniformLiftedTreeLaw G hN f)=
      (N : ℝ)⁻¹*∑ v, graphEigenResidual G (energy a) (f a) v ^ 2 := by
  let C := fun z : RegularTreeVertex (m+2) → Fin N =>
    fun av : Fin r × RegularTreeVertex (m+2) => f av.1 (z av.2)
  let B := fun z : RegularTreeVertex (m+2) → Fin N => fun v => z (vertexBallEmbedding (m+2) 0 v)
  let F := fun y : VertexBallVertex (m+2) 0 → Fin N =>
    (∑ j, f a (y (vertexBallNeighbor (m+2) 0 j)))-energy a*f a (y (vertexBallRoot (m+2) 0))
  have hC : Measurable C := measurable_treeColoring f
  have hB : Measurable B := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have he (z : RegularTreeVertex (m+2) → Fin N) :
      treeEigenResidual (m+2) r energy a none (C z)=F (B z) := by
    unfold treeEigenResidual
    rw [tree_root_neighbor_sum]
    rfl
  have hF : Measurable (fun y => F y^2) := measurable_of_finite _
  unfold uniformLiftedTreeLaw
  rw [integral_map hC.aemeasurable ((continuous_treeEigenResidual (m+2) r energy a none).pow 2).aestronglyMeasurable]
  simp_rw [he]
  rw [← integral_map hB.aemeasurable hF.aestronglyMeasurable]
  have hb := uniformTreeCoverLaw_ball G hN 0
  change Measure.map B (uniformTreeCoverLaw G hN : Measure _)=_ at hb
  rw [hb]
  have hAE : ∀ᵐ y ∂finiteVertexCoverImageLaw G 0,
      F y=graphEigenResidual G (energy a) (f a) (y (vertexBallRoot (m+2) 0)) := by
    apply uniformAtomicLaw_ae_of_forall (vertexGraphCover G 0)
    intro seed
    change (∑ j, f a (vertexGraphCover G 0 seed (vertexBallNeighbor (m+2) 0 j)))-
      energy a*f a (vertexGraphCover G 0 seed (vertexBallRoot (m+2) 0))=graphEigenResidual G (energy a) (f a) _
    simp only [vertexGraphCover_neighbor,vertexGraphCover_root,graphEigenResidual]
    rw [Equiv.sum_comp seed.2.1 (fun j => f a (graphNeighbor G seed.1 j))]
  calc
    _ = ∫ y, graphEigenResidual G (energy a) (f a) (y (vertexBallRoot (m+2) 0))^2
        ∂finiteVertexCoverImageLaw G 0 := by
      apply integral_congr_ae
      filter_upwards [hAE] with y hy
      rw [hy]
    _ = ∫ v, graphEigenResidual G (energy a) (f a) v^2 ∂finiteUniform (Fin N) := by
      rw [← finiteVertexCoverImageLaw_root G 0,
        integral_map (measurable_pi_apply _).aemeasurable (measurable_of_finite _).aestronglyMeasurable]
    _ = _ := by rw [integral_finiteUniform]; simp only [Fintype.card_fin]

/-- At every actual cover site, the squared residual integral is precisely
the empirical graph squared residual. No eigenvector assumption is needed. -/
theorem integral_uniformLiftedTreeLaw_residual_sq {N m r : ℕ}
    (G : RegularGraph N (m+2)) (hN : 0<N) (energy : Fin r → ℝ) (f : Fin r → Fin N → ℝ)
    (a : Fin r) (u : RegularTreeVertex (m+2)) :
    (∫ x, treeEigenResidual (m+2) r energy a u x^2 ∂uniformLiftedTreeLaw G hN f)=
      (N : ℝ)⁻¹*∑ v, graphEigenResidual G (energy a) (f a) v ^ 2 := by
  let e := regularTreeReroot (m+1) u
  have he : e none=u := regularTreeReroot_root (m+1) u
  let T := fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
    fun av : Fin r × RegularTreeVertex (m+2) => z (av.1,e av.2)
  have hT : Measurable T := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hI := uniformLiftedTreeLaw_invariant G hN f e
  have hh := congrArg (fun μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ) =>
    ∫ x, treeEigenResidual (m+2) r energy a none x^2 ∂μ) hI
  dsimp only at hh
  rw [integral_map hT.aemeasurable ((continuous_treeEigenResidual (m+2) r energy a none).pow 2).aestronglyMeasurable] at hh
  dsimp only [T] at hh
  simp_rw [treeEigenResidual_equivariant,he] at hh
  exact hh.trans (integral_uniformLiftedTreeLaw_residual_sq_root G hN energy f a)

end GaussianWave.BS
