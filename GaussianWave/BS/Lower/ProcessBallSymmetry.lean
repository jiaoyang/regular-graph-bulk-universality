import GaussianWave.BS.Lower.ProcessWindowLaws
import GaussianWave.BS.Lower.PathCodeEdgeMarginal
import GaussianWave.BS.EdgeStabilizerExtension

/-! The actual tree-process automorphism invariance implies every finite
C/E stabilizer and root-neighbor permutation symmetry of its recoloring
laws. No finite-window invariance certificate is an input. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
set_option maxHeartbeats 1000000
namespace GaussianWave.BS.Lower
open GaussianWave.BS

variable {r : ℕ} {F : Type*} [Fintype F]

theorem process_vertex_recolor_stabilizer_invariant (m k : ℕ)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hP : ∀ e : regularWordTree (m+2) ≃g regularWordTree (m+2),
      Measure.map (fun z av => z (av.1,e av.2)) P=P)
    (φ : (Fin r → ℝ) → F → ℝ) (hφm : ∀ b,Measurable (fun x => φ x b))
    (g : VertexBallStabilizer (m+2) k) (w : VertexBallVertex (m+2) k → F) :
    windowRecolorMass (vertexProcessWindow m k P) φ (fun v => w (g⁻¹ • v))=
      windowRecolorMass (vertexProcessWindow m k P) φ w := by
  have hsite (v : VertexBallVertex (m+2) k) :
      regularTreeBranchAutomorphism (m+2) k g (vertexBallEmbedding (m+2) k v)=
        vertexBallEmbedding (m+2) k ((MulAction.toPerm g) v) := by
    cases v with
    | inl t => rfl
    | inr av => exact vertexBallEmbedding_branchAutomorphism (m+2) k g av.1 av.2
  have hμ := processWindowProjection_invariant P (vertexBallEmbedding (m+2) k) (MulAction.toPerm g)
    (regularTreeBranchAutomorphism (m+2) k g).toEquiv (hP (regularTreeBranchAutomorphism (m+2) k g)) hsite
  exact windowRecolorMass_invariant (vertexProcessWindow m k P) (MulAction.toPerm g) hμ φ hφm w

theorem process_edge_recolor_stabilizer_invariant (m k : ℕ)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hP : ∀ e : regularWordTree (m+2) ≃g regularWordTree (m+2),
      Measure.map (fun z av => z (av.1,e av.2)) P=P)
    (φ : (Fin r → ℝ) → F → ℝ) (hφm : ∀ b,Measurable (fun x => φ x b))
    (g : EdgeBallStabilizer (m+2) k) (w : EdgeBallVertex (m+2) k → F) :
    windowRecolorMass (edgeProcessWindow m k P) φ (fun v => w (g⁻¹ • v))=
      windowRecolorMass (edgeProcessWindow m k P) φ w := by
  have hμ := processWindowProjection_invariant P (edgeBallEmbedding m k) (MulAction.toPerm g)
    (edgeBallStabilizerExtension m k g).toEquiv (hP (edgeBallStabilizerExtension m k g)) (edgeBallEmbedding_stabilizerExtension m k g)
  exact windowRecolorMass_invariant (edgeProcessWindow m k P) (MulAction.toPerm g) hμ φ hφm w

theorem vertexBallEmbedding_rootPermutationIso (d k : ℕ) (σ : Equiv.Perm (Fin d))
    (v : VertexBallVertex d k) :
    regularTreeRootPermutation d σ (vertexBallEmbedding d k v)=
      vertexBallEmbedding d k (vertexBallRootPermutationIso d k σ v) := by
  cases v with
  | inl t => rfl
  | inr av =>
      change some (σ av.1,(branchPath (d-1) k av.2).reverse)=
        some (σ av.1,(branchPath (d-1) k (branchAutomorphism (d-1) k 1 av.2)).reverse)
      rw [branchAutomorphism_one]
      rfl

theorem process_vertex_recolor_rootPermutation_invariant (m k : ℕ)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hP : ∀ e : regularWordTree (m+2) ≃g regularWordTree (m+2),
      Measure.map (fun z av => z (av.1,e av.2)) P=P)
    (φ : (Fin r → ℝ) → F → ℝ) (hφm : ∀ b,Measurable (fun x => φ x b))
    (σ : Equiv.Perm (Fin (m+2))) (w : VertexBallVertex (m+2) k → F) :
    windowRecolorMass (vertexProcessWindow m k P) φ (w ∘ (vertexBallRootPermutationIso (m+2) k σ).symm)=
      windowRecolorMass (vertexProcessWindow m k P) φ w := by
  have hμ := processWindowProjection_invariant P (vertexBallEmbedding (m+2) k)
    (vertexBallRootPermutationIso (m+2) k σ).toEquiv (regularTreeRootPermutation (m+2) σ).toEquiv
    (hP (regularTreeRootPermutation (m+2) σ)) (vertexBallEmbedding_rootPermutationIso (m+2) k σ)
  exact windowRecolorMass_invariant (vertexProcessWindow m k P)
    (vertexBallRootPermutationIso (m+2) k σ).toEquiv hμ φ hφm w

end GaussianWave.BS.Lower
