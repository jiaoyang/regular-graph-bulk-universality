import GaussianWave.BS.WholeCoverInvariance
import GaussianWave.BS.Reused.Graph.FiniteUniformIntegration

/-! Every actual uniform-cover coordinate has the literal uniform graph
vertex law. Consequently every joint finite-graph coloring has its actual
empirical coordinate moments everywhere on the infinite tree. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph Reused.Graph.Configuration

/-- The actual finite vertex-cover root has the literal finite-uniform
vertex law, proved by dropping the independent permutation seed. -/
theorem finiteVertexCoverImageLaw_root {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ) :
    Measure.map (fun z : VertexBallVertex (m+2) k → Fin N => z (vertexBallRoot (m+2) k))
      (finiteVertexCoverImageLaw G k)=finiteUniform (Fin N) := by
  rw [finiteVertexCoverImageLaw,uniformAtomicLaw_map _ _ (measurable_pi_apply _)]
  have he : (fun z : VertexBallVertex (m+2) k → Fin N => z (vertexBallRoot (m+2) k)) ∘
      vertexGraphCover G k = fun seed : VertexCoverSeed N m k => seed.1 := rfl
  rw [he]
  change uniformAtomicLaw (fun z : Fin N × (Equiv.Perm (Fin (m+2)) ×
    (Fin (m+2) → BranchCoverOrdering (m+1) k)) => id z.1)=_
  rw [uniformAtomicLaw_prod_fst,uniformAtomicLaw_eq_map,Measure.map_id]

/-- The distinguished root of the constructed whole cover is uniform. -/
theorem uniformTreeCoverLaw_root {N m : ℕ} (G : RegularGraph N (m+2)) (hN : 0<N) :
    Measure.map (fun z : RegularTreeVertex (m+2) → Fin N => z none)
      (uniformTreeCoverLaw G hN : Measure _)=finiteUniform (Fin N) := by
  let C := fun z : RegularTreeVertex (m+2) → Fin N => fun v => z (vertexBallEmbedding (m+2) 0 v)
  let T := fun z : VertexBallVertex (m+2) 0 → Fin N => z (vertexBallRoot (m+2) 0)
  have hC : Measurable C := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hT : Measurable T := measurable_pi_apply _
  have he : (fun z : RegularTreeVertex (m+2) → Fin N => z none)=T ∘ C := rfl
  rw [he,← Measure.map_map hT hC]
  have hb := uniformTreeCoverLaw_ball G hN 0
  change Measure.map C (uniformTreeCoverLaw G hN : Measure _)=_ at hb
  rw [hb]
  exact finiteVertexCoverImageLaw_root G 0

/-- Every actual cover coordinate is uniform, from the proved full tree
invariance and an actual root-to-site isomorphism. -/
theorem uniformTreeCoverLaw_coordinate {N m : ℕ} (G : RegularGraph N (m+2)) (hN : 0<N)
    (u : RegularTreeVertex (m+2)) :
    Measure.map (fun z : RegularTreeVertex (m+2) → Fin N => z u)
      (uniformTreeCoverLaw G hN : Measure _)=finiteUniform (Fin N) := by
  let e := regularTreeReroot (m+1) u
  have he : e none=u := regularTreeReroot_root (m+1) u
  let T := fun z : RegularTreeVertex (m+2) → Fin N => fun v => z (e v)
  have hT : Measurable T := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hI := uniformTreeCoverLaw_invariant G hN e
  have hh := congrArg (Measure.map (fun z : RegularTreeVertex (m+2) → Fin N => z none)) hI
  rw [Measure.map_map (measurable_pi_apply _) hT] at hh
  have hc : (fun z : RegularTreeVertex (m+2) → Fin N => z none) ∘ T=
      fun z : RegularTreeVertex (m+2) → Fin N => z u := by funext z; exact congrArg z he
  rw [hc] at hh
  exact hh.trans (uniformTreeCoverLaw_root G hN)

/-- Joint graph coloring at any cover site is its literal empirical root
vector law; channels are never declared independent. -/
theorem uniformLiftedTreeLaw_site {N m r : ℕ} (G : RegularGraph N (m+2)) (hN : 0<N)
    (f : Fin r → Fin N → ℝ) (u : RegularTreeVertex (m+2)) :
    Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => fun a => z (a,u))
      (uniformLiftedTreeLaw G hN f)=
      Measure.map (fun v : Fin N => fun a => f a v) (finiteUniform (Fin N)) := by
  let C := fun z : RegularTreeVertex (m+2) → Fin N => fun av : Fin r × RegularTreeVertex (m+2) => f av.1 (z av.2)
  let R := fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => fun a => z (a,u)
  let ev := fun z : RegularTreeVertex (m+2) → Fin N => z u
  let mark := fun v : Fin N => fun a => f a v
  have hC : Measurable C := measurable_treeColoring f
  have hR : Measurable R := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have he : R ∘ C=mark ∘ ev := rfl
  have hev : Measurable ev := measurable_pi_apply u
  unfold uniformLiftedTreeLaw
  rw [Measure.map_map hR hC,he,← Measure.map_map (measurable_of_finite mark) hev,
    uniformTreeCoverLaw_coordinate G hN u]

/-- Scalar coordinate law, as an actual finite empirical image. -/
theorem uniformLiftedTreeLaw_coordinate {N m r : ℕ} (G : RegularGraph N (m+2)) (hN : 0<N)
    (f : Fin r → Fin N → ℝ) (a : Fin r) (u : RegularTreeVertex (m+2)) :
    Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => z (a,u))
      (uniformLiftedTreeLaw G hN f)=Measure.map (f a) (finiteUniform (Fin N)) := by
  have h := congrArg (Measure.map (fun z : Fin r → ℝ => z a)) (uniformLiftedTreeLaw_site G hN f u)
  have heval : Measurable (fun z : Fin r → ℝ => z a) := measurable_pi_apply a
  have hsite : Measurable (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => fun a => z (a,u)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  rw [Measure.map_map heval hsite,
    Measure.map_map heval (measurable_of_finite (fun v : Fin N => fun a => f a v))] at h
  exact h

/-- Every scalar empirical moment is integrable on the actual lifted law. -/
theorem integrable_uniformLiftedTreeLaw_coordinate {N m r : ℕ} (G : RegularGraph N (m+2))
    (hN : 0<N) (f : Fin r → Fin N → ℝ) (a : Fin r) (u : RegularTreeVertex (m+2)) (F : ℝ → ℝ)
    (hF : Measurable F) : Integrable (fun z => F (z (a,u))) (uniformLiftedTreeLaw G hN f) := by
  have hfi : Integrable (fun v : Fin N => F (f a v)) (finiteUniform (Fin N)) := by
    apply (integrable_finset_sum_measure.mpr (fun _ _ => integrable_dirac)).smul_measure
    exact ENNReal.inv_ne_top.mpr (by simp [Fintype.card_fin,ne_of_gt hN])
  have hma : AEStronglyMeasurable F (Measure.map (f a) (finiteUniform (Fin N))) := hF.aestronglyMeasurable
  have hmap : Integrable F (Measure.map (f a) (finiteUniform (Fin N))) :=
    (integrable_map_measure hma (measurable_of_finite _).aemeasurable).2 hfi
  rw [← uniformLiftedTreeLaw_coordinate G hN f a u] at hmap
  exact hmap.comp_measurable (measurable_pi_apply _)

/-- Literal empirical moment identity at every actual tree site. -/
theorem integral_uniformLiftedTreeLaw_coordinate {N m r : ℕ} (G : RegularGraph N (m+2))
    (hN : 0<N) (f : Fin r → Fin N → ℝ) (a : Fin r) (u : RegularTreeVertex (m+2)) (F : ℝ → ℝ)
    (hF : Measurable F) :
    (∫ z, F (z (a,u)) ∂uniformLiftedTreeLaw G hN f)=(N : ℝ)⁻¹*∑ v, F (f a v) := by
  have hcoord := uniformLiftedTreeLaw_coordinate G hN f a u
  have h := congrArg (fun μ : Measure ℝ => ∫ x, F x ∂μ) hcoord
  have hev : Measurable (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => z (a,u)) := measurable_pi_apply _
  dsimp only at h
  rw [integral_map hev.aemeasurable hF.aestronglyMeasurable,
    integral_map (measurable_of_finite (f a)).aemeasurable hF.aestronglyMeasurable,
    integral_finiteUniform] at h
  simpa only [Fintype.card_fin] using h

end GaussianWave.BS
