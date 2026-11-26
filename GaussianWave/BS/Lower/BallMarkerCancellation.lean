import GaussianWave.BS.Lower.BallPathCoverage
import GaussianWave.BS.FiniteBallStabilizer
import GaussianWave.BS.Lower.PathMarkerCancellation

/-! Actual C/E finite-tree marker entropy cancellation. Every graph action,
center stabilizer, coverage property and group-cardinality identity is
discharged by the constructed finite tree geometry. -/
noncomputable section
open Filter
open scoped BigOperators Classical Topology
set_option maxHeartbeats 1200000
namespace GaussianWave.BS.Lower
open GaussianWave.BS GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

theorem vertexBall_pathCode_action_invariant {F : Type*} (m k : ℕ)
    (g : VertexBallStabilizer (m+2) k) (w : VertexBallVertex (m+2) k → F) :
    centerPathCodes (GaussianWave.BS.vertexBallGraph (m+2) k) k (vertexBallStarCenter (m+2) k)
      (fun v => w (g⁻¹ • v))=
    centerPathCodes (GaussianWave.BS.vertexBallGraph (m+2) k) k (vertexBallStarCenter (m+2) k) w := by
  apply centerPathCodes_action_invariant _ k _ (vertexBallStabilizerGraphIso (m+2) k)
    (fun _ _ => rfl) _ g w
  intro h i
  refine Fin.cases ?_ (fun a => ?_) i
  · exact vertexBallStabilizerGraphIso_root (m+2) k h
  · exact vertexBallStabilizerGraphIso_neighbor (m+2) k h a

theorem vertexBall_pathCode_recover_markers {F M : Type*} (m k : ℕ)
    (w w' : VertexBallVertex (m+2) k → F × M) (hw : Function.Injective (fun v => (w v).2))
    (hc : centerPathCodes (GaussianWave.BS.vertexBallGraph (m+2) k) k (vertexBallStarCenter (m+2) k) w'=
      centerPathCodes (GaussianWave.BS.vertexBallGraph (m+2) k) k (vertexBallStarCenter (m+2) k) w) :
    letI : MulAction (VertexBallStabilizer (m+2) k) (VertexBallVertex (m+2) k → F × M) := arrowAction
    w' ∈ MulAction.orbit (VertexBallStabilizer (m+2) k) w := by
  apply centerPathCodes_recover_of_injective_markers _ k _ (vertexBall_pathCoveredVertex m k)
    (vertexBall_pathCoveredEdge m k) _ w w' hw hc
  intro e he
  exact exists_vertexBallStabilizer_of_graphIso (m+2) k e (he 0) (fun a => he a.succ)

theorem edgeBall_pathCode_action_invariant {F : Type*} (m k : ℕ)
    (g : EdgeBallStabilizer (m+2) k) (w : EdgeBallVertex (m+2) k → F) :
    centerPathCodes (edgeBallGraph m k) k (edgeBallRoot m k) (fun v => w (g⁻¹ • v))=
      centerPathCodes (edgeBallGraph m k) k (edgeBallRoot m k) w :=
  centerPathCodes_action_invariant _ k _ (edgeBallStabilizerGraphIso m k) (fun _ _ => rfl)
    (fun h b => edgeBallStabilizerGraphIso_root m k h b) g w

theorem edgeBall_pathCode_recover_markers {F M : Type*} (m k : ℕ)
    (w w' : EdgeBallVertex (m+2) k → F × M) (hw : Function.Injective (fun v => (w v).2))
    (hc : centerPathCodes (edgeBallGraph m k) k (edgeBallRoot m k) w'=
      centerPathCodes (edgeBallGraph m k) k (edgeBallRoot m k) w) :
    letI : MulAction (EdgeBallStabilizer (m+2) k) (EdgeBallVertex (m+2) k → F × M) := arrowAction
    w' ∈ MulAction.orbit (EdgeBallStabilizer (m+2) k) w :=
  centerPathCodes_recover_of_injective_markers _ k _ (edgeBall_pathCoveredVertex m k)
    (edgeBall_pathCoveredEdge m k) (exists_edgeBallStabilizer_of_graphIso m k) w w' hw hc

local instance markerCDecidableEq (m k : ℕ) : DecidableEq (VertexBallVertex (m+2) k) := Classical.decEq _
local instance markerEDecidableEq (m k : ℕ) : DecidableEq (EdgeBallVertex (m+2) k) := Classical.decEq _

/-- The literal path-code star-minus-edge entropy, centered by the one-root
marker entropy, converges to the original finite-window entropy functional.
Only ordinary invariant probability masses are inputs. -/
theorem ball_path_codes_marker_entropy_cancellation {F : Type*} [Fintype F] [DecidableEq F] (m k : ℕ)
    (pC : (VertexBallVertex (m+2) k → F) → ℝ) (pE : (EdgeBallVertex (m+2) k → F) → ℝ)
    (hpC : ∀ w,0 ≤ pC w) (hpE : ∀ w,0 ≤ pE w) (hsC : ∑ w,pC w=1) (hsE : ∑ w,pE w=1)
    (hinvC : ∀ (g : VertexBallStabilizer (m+2) k) w,pC (fun v => w (g⁻¹ • v))=pC w)
    (hinvE : ∀ (g : EdgeBallStabilizer (m+2) k) w,pE (fun v => w (g⁻¹ • v))=pE w)
    (markers : ℕ → ℕ) (hm : ∀ n,0 < markers n) (hminf : Tendsto markers atTop atTop) :
    Tendsto (fun n => entropy (pushMass
      (centerPathCodes (GaussianWave.BS.vertexBallGraph (m+2) k) k (vertexBallStarCenter (m+2) k))
      (markerDecoratedMass pC (markers n)))-
      (((m+2 : ℕ) : ℝ)/2)*entropy (pushMass (centerPathCodes (edgeBallGraph m k) k (edgeBallRoot m k))
        (markerDecoratedMass pE (markers n)))-Real.log (markers n)) atTop
      (𝓝 (entropy pC-(((m+2 : ℕ) : ℝ)/2)*entropy pE)) := by
  exact good_marker_star_edge_entropy_cancellation
    (GC := VertexBallStabilizer (m+2) k) (GE := EdgeBallStabilizer (m+2) k)
    (VC := VertexBallVertex (m+2) k) (VE := EdgeBallVertex (m+2) k) (F := F)
    pC pE hpC hpE hsC hsE hinvC hinvE
    (m+2) (Fintype.card (BranchCoverOrdering (m+2-1) k))
    (card_vertexBallStabilizer (m+2) k) (card_edgeBallStabilizer (m+2) k)
    (ball_ambient_real_card_balance (m+2) k) markers hm hminf
    (fun n => Fin (m+2+1) → PathNeighborhoodCode (F × Fin (markers n)) k)
    (fun n => Bool → PathNeighborhoodCode (F × Fin (markers n)) k)
    (fun _ => centerPathCodes (GaussianWave.BS.vertexBallGraph (m+2) k) k (vertexBallStarCenter (m+2) k))
    (fun _ => centerPathCodes (edgeBallGraph m k) k (edgeBallRoot m k))
    (fun _ => vertexBall_pathCode_action_invariant m k) (fun _ => edgeBall_pathCode_action_invariant m k)
    (fun _ w hw w' hc => vertexBall_pathCode_recover_markers m k w w' hw hc)
    (fun _ w hw w' hc => edgeBall_pathCode_recover_markers m k w w' hw hc)

end GaussianWave.BS.Lower
