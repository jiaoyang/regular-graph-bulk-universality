import GaussianWave.BS.Lower.ProcessBallSymmetry
import GaussianWave.BS.Lower.PathCodeEdgeMarginal
import GaussianWave.BS.Lower.PathEdgeComparison

/-! The averaged code-edge entropy from the graph counting argument is
exactly the distinguished E-window code entropy of the actual invariant
process. Both marginal consistency and fixed-port symmetry are proved. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
set_option maxHeartbeats 1200000
namespace GaussianWave.BS.Lower
open GaussianWave.BS GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite
open GaussianWave.BS.Reused.Graph.ColorProfiles
open GaussianWave.BS.Reused.Graph.Configuration

def pathCodeEdgeEquiv (q k : ℕ) : (Bool → PathNeighborhoodCode (Fin q) k) ≃
    (Fin (pathNeighborhoodPalette q k) × Fin (pathNeighborhoodPalette q k)) where
  toFun := fun c => (Fintype.equivFin _ (c false),Fintype.equivFin _ (c true))
  invFun := fun c b => (Fintype.equivFin _).symm (if b then c.2 else c.1)
  left_inv := by intro c; funext b; cases b <;> simp
  right_inv := by intro c; apply Prod.ext <;> simp

@[simp] theorem edgeToVertexBall_left_root (m k : ℕ) :
    edgeToVertexBall m k (edgeBallRoot m k false)=vertexBallRoot (m+2) k := by cases k <;> rfl

@[simp] theorem edgeToVertexBall_right_root (m k : ℕ) :
    edgeToVertexBall m k (edgeBallRoot m k true)=vertexBallNeighbor (m+2) k 0 := by cases k <;> rfl

theorem vertexPathPairCode_edge_restrict {q : ℕ} (m k : ℕ)
    (w : VertexBallVertex (m+2) k → Fin q) :
    vertexPathPairCode (m+2) q k 0 w=pathCodeEdgeEquiv q k
      (centerPathCodes (edgeBallGraph m k) k (edgeBallRoot m k) (w ∘ edgeToVertexBall m k)) := by
  apply Prod.ext
  · change (Fintype.equivFin _) (pathNeighborhoodCode (vertexBallGraph (m+2) k) k w (vertexBallRoot (m+2) k))=
      (Fintype.equivFin _) (pathNeighborhoodCode (edgeBallGraph m k) k (w ∘ edgeToVertexBall m k) (edgeBallRoot m k false))
    apply congrArg (Fintype.equivFin _)
    simpa only [edgeToVertexBall_left_root] using (pathNeighborhoodCode_edgeToVertexBall m k w false).symm
  · change (Fintype.equivFin _) (pathNeighborhoodCode (vertexBallGraph (m+2) k) k w (vertexBallNeighbor (m+2) k 0))=
      (Fintype.equivFin _) (pathNeighborhoodCode (edgeBallGraph m k) k (w ∘ edgeToVertexBall m k) (edgeBallRoot m k true))
    apply congrArg (Fintype.equivFin _)
    simpa only [edgeToVertexBall_right_root] using (pathNeighborhoodCode_edgeToVertexBall m k w true).symm

theorem process_code_edge_entropy {q r : ℕ} (m k : ℕ)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure P]
    (hP : ∀ e : regularWordTree (m+2) ≃g regularWordTree (m+2),
      Measure.map (fun z av => z (av.1,e av.2)) P=P)
    (φ : (Fin r → ℝ) → Fin q → ℝ)
    (hφ0 : ∀ x b,0 ≤ φ x b) (hφ1 : ∀ x,∑ b,φ x b=1)
    (hφc : ∀ b,Continuous (fun x => φ x b)) :
    entropy (edgeMassOfStar (pushMass (vertexPathStarCode (m+2) q k)
      (windowRecolorMass (vertexProcessWindow m k P) φ)))=
      entropy (pushMass (centerPathCodes (edgeBallGraph m k) k (edgeBallRoot m k))
        (windowRecolorMass (edgeProcessWindow m k P) φ)) := by
  let pC := windowRecolorMass (vertexProcessWindow m k P) φ
  let pE := windowRecolorMass (edgeProcessWindow m k P) φ
  have hinv := process_vertex_recolor_rootPermutation_invariant m k P hP φ (fun b => (hφc b).measurable)
  rw [vertexPathStarCode_edgeMass_eq (by omega : 0 < m+2) _ hinv]
  have hrestrict : pushMass (fun w : VertexBallVertex (m+2) k → Fin q => w ∘ edgeToVertexBall m k) pC=pE := by
    funext w
    have h := congrFun (process_recolor_edge_marginal m k P φ hφ0 hφ1 hφc) w
    simpa only [pushMass_as_sum,← tsum_fintype] using h
  have hmass : pushMass (vertexPathPairCode (m+2) q k 0) pC=
      pushMass (pathCodeEdgeEquiv q k)
        (pushMass (centerPathCodes (edgeBallGraph m k) k (edgeBallRoot m k)) pE) := by
    rw [← hrestrict,pushMass_comp,pushMass_comp]
    apply congrArg (fun code : (VertexBallVertex (m+2) k → Fin q) →
      (Fin (pathNeighborhoodPalette q k) × Fin (pathNeighborhoodPalette q k)) => pushMass code pC)
    funext w
    exact vertexPathPairCode_edge_restrict m k w
  change entropy (pushMass (vertexPathPairCode (m+2) q k 0) pC)=_
  rw [hmass]
  exact entropy_pushMass_equiv _ _

end GaussianWave.BS.Lower
