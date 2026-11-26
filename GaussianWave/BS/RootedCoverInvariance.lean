import GaussianWave.BS.FiniteCoverSymmetry
import GaussianWave.BS.RootedBallAutomorphismDecomposition
import GaussianWave.BS.EdgeCoverInvariance

/-! All actual rooted tree automorphisms preserve the literal uniform
cover law, by finite permutation-source reindexing and exhaustion. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GaussianWave.BS
open Reused.Graph Reused.Graph.Configuration

def vertexCoverSeedRootedEquiv (N m k : ℕ) (σ : Equiv.Perm (Fin (m+2)))
    (g : Fin (m+2) → BranchCoverOrdering (m+1) k) : Equiv.Perm (VertexCoverSeed N m k) where
  toFun := fun z => (z.1,z.2.1*σ,fun a => z.2.2 (σ a)*g a)
  invFun := fun z => (z.1,z.2.1*σ⁻¹,fun a => z.2.2 (σ⁻¹ a)*(g (σ⁻¹ a))⁻¹)
  left_inv := by
    rintro ⟨v,τ,h⟩
    refine Prod.ext rfl (Prod.ext (mul_inv_cancel_right τ σ) (funext ?_))
    intro a
    change (h (σ (σ⁻¹ a))*g (σ⁻¹ a))*(g (σ⁻¹ a))⁻¹ = h a
    rw [mul_inv_cancel_right,Equiv.Perm.apply_inv_self]
  right_inv := by
    rintro ⟨v,τ,h⟩
    refine Prod.ext rfl (Prod.ext (inv_mul_cancel_right τ σ) (funext ?_))
    intro a
    change (h (σ⁻¹ (σ a))*(g (σ⁻¹ (σ a)))⁻¹)*g a = h a
    rw [Equiv.Perm.inv_apply_self,inv_mul_cancel_right]

theorem vertexGraphCover_rooted_reindex {N m : ℕ} (G : RegularGraph N (m+2))
    (k : ℕ) (σ : Equiv.Perm (Fin (m+2))) (g : Fin (m+2) → BranchCoverOrdering (m+1) k)
    (seed : VertexCoverSeed N m k) (v : VertexBallVertex (m+2) k) :
    vertexGraphCover G k (vertexCoverSeedRootedEquiv N m k σ g seed) v =
      vertexGraphCover G k seed (rootedBranchAutomorphism (m+1) k σ g v) := by
  cases v with
  | inl u => rfl
  | inr av =>
    exact branchGraphCover_mul G k
      (canonicalPortLabeling G seed.1 (seed.2.1 (σ av.1))).property
      (seed.2.2 (σ av.1)) (g av.1) av.2

theorem finiteVertexCoverImageLaw_rooted_invariant {N m : ℕ} (G : RegularGraph N (m+2))
    (k : ℕ) (σ : Equiv.Perm (Fin (m+2))) (g : Fin (m+2) → BranchCoverOrdering (m+1) k) :
    Measure.map (fun x : VertexBallVertex (m+2) k → Fin N =>
      fun v => x (rootedBranchAutomorphism (m+1) k σ g v))
      (finiteVertexCoverImageLaw G k) = finiteVertexCoverImageLaw G k := by
  rw [finiteVertexCoverImageLaw,uniformAtomicLaw_map _ _
    (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))]
  have he : (fun x : VertexBallVertex (m+2) k → Fin N =>
      fun v => x (rootedBranchAutomorphism (m+1) k σ g v)) ∘ vertexGraphCover G k =
      vertexGraphCover G k ∘ vertexCoverSeedRootedEquiv N m k σ g := by
    funext seed v
    exact (vertexGraphCover_rooted_reindex G k σ g seed v).symm
  rw [he,uniformAtomicLaw_reindex]

theorem uniformTreeCoverLaw_rooted_ball_invariant {N m : ℕ}
    (G : RegularGraph N (m+2)) (hN : 0 < N)
    (e : regularWordTree (m+2) ≃g regularWordTree (m+2)) (hroot : e none = none) (k : ℕ) :
    Measure.map (fun x : RegularTreeVertex (m+2) → Fin N =>
      fun v => x (e (vertexBallEmbedding (m+2) k v))) (uniformTreeCoverLaw G hN : Measure _) =
      finiteVertexCoverImageLaw G k := by
  obtain ⟨σ,g,hg⟩ := exists_rootedRegularTreeRestriction (m+2) k e hroot
  let B := fun x : RegularTreeVertex (m+2) → Fin N =>
    fun v => x (vertexBallEmbedding (m+2) k v)
  let R := fun x : VertexBallVertex (m+2) k → Fin N =>
    fun v => x (rootedBranchAutomorphism (m+1) k σ g v)
  have hB : Measurable B := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hR : Measurable R := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hfun : (fun x : RegularTreeVertex (m+2) → Fin N =>
      fun v => x (e (vertexBallEmbedding (m+2) k v))) = R ∘ B := by
    funext x v
    exact congrArg x (hg v)
  rw [hfun,← Measure.map_map hR hB]
  have hball : Measure.map B (uniformTreeCoverLaw G hN : Measure _) = finiteVertexCoverImageLaw G k :=
    uniformTreeCoverLaw_ball G hN k
  rw [hball]
  exact finiteVertexCoverImageLaw_rooted_invariant G k σ g

theorem treeLaw_eq_of_vertex_marginals {A : Type*} [MeasurableSpace A] (m : ℕ)
    (μ ν : Measure (RegularTreeVertex (m+2) → A)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ k, Measure.map
      (fun z : RegularTreeVertex (m+2) → A => fun v => z (vertexBallEmbedding (m+2) k v)) μ =
      Measure.map (fun z : RegularTreeVertex (m+2) → A => fun v => z (vertexBallEmbedding (m+2) k v)) ν) :
    μ=ν := by
  apply treeLaw_eq_of_edge_marginals m μ ν
  intro k
  let B := fun z : RegularTreeVertex (m+2) → A => fun v => z (vertexBallEmbedding (m+2) k v)
  let T := fun z : VertexBallVertex (m+2) k → A => fun v => z (edgeToVertexBall m k v)
  have hB : Measurable B := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hT : Measurable T := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hcomp : (fun z : RegularTreeVertex (m+2) → A => fun v => z (edgeBallEmbedding m k v)) = T ∘ B := by
    funext z v
    exact congrArg z (edgeToVertexBall_embedding m k v).symm
  rw [hcomp,← Measure.map_map hT hB,← Measure.map_map hT hB,h k]

theorem uniformTreeCoverLaw_rooted_invariant {N m : ℕ}
    (G : RegularGraph N (m+2)) (hN : 0 < N)
    (e : regularWordTree (m+2) ≃g regularWordTree (m+2)) (hroot : e none = none) :
    Measure.map (fun x : RegularTreeVertex (m+2) → Fin N => fun v => x (e v))
      (uniformTreeCoverLaw G hN : Measure _) = (uniformTreeCoverLaw G hN : Measure _) := by
  let Q : Measure (RegularTreeVertex (m+2) → Fin N) := uniformTreeCoverLaw G hN
  let T := fun x : RegularTreeVertex (m+2) → Fin N => fun v => x (e v)
  have hT : Measurable T := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  letI : IsProbabilityMeasure (Measure.map T Q) := isProbabilityMeasure_map hT.aemeasurable
  apply treeLaw_eq_of_vertex_marginals m (Measure.map T Q) Q
  intro k
  rw [Measure.map_map (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)) hT]
  exact (uniformTreeCoverLaw_rooted_ball_invariant G hN e hroot k).trans
    (uniformTreeCoverLaw_ball G hN k).symm

end GaussianWave.BS
