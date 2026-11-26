import GaussianWave.BS.Lower.BallPathCoverage
import GaussianWave.BS.Lower.PathCoverComparison
import GaussianWave.BS.Lower.LocalCoverCycles

/-! Exact compatibility of the two endpoint neighborhood codes between
the actual C/E tree windows. All radius and embedding conditions are proved. -/
noncomputable section
open scoped Classical
set_option maxHeartbeats 1000000
namespace GaussianWave.BS.Lower
open GaussianWave.BS

theorem edgeBallEmbedding_edgeDepth_eq (m k : ℕ) (v : EdgeBallVertex (m+2) k) :
    regularTreeEdgeDepth m (edgeBallEmbedding m k v)=branchDepth (m+1) k v.2 := by
  unfold regularTreeEdgeDepth edgeBallEmbedding
  have h := (treeHalfEquiv (m+1)).apply_symm_apply (v.1,(branchPath (m+1) k v.2).reverse)
  change treeHalfEncode (m+1) (treeHalfDecode (m+1) _)=_ at h
  change (treeHalfEncode (m+1) (treeHalfDecode (m+1) _)).2.length=_
  rw [h,List.length_reverse,branchPath_length]

theorem regularTreeEdgeDepth_le_dist_endpoint (m : ℕ) (b : Bool) (v : RegularTreeVertex (m+2)) :
    regularTreeEdgeDepth m v ≤ (regularWordTree (m+2)).dist
      (if b then some (0,[]) else none) v := by
  let k := regularTreeEdgeDepth m v
  let w := edgeBallIndexOfDepth m k v le_rfl
  have hw : edgeBallEmbedding m k w=v := edgeBallIndexOfDepth_spec m k v le_rfl
  have he : edgeBallEmbedding m k (edgeBallRoot m k b)=(if b then some (0,[]) else none) := by
    cases b <;> simp only [edgeBallEmbedding_left_root,edgeBallEmbedding_right_root,Bool.false_eq_true,if_false,if_true]
  rw [← hw,← he,edgeBallEmbedding_edgeDepth_eq,edgeBallEmbedding_dist]
  rcases w with ⟨c,w⟩
  cases b <;> cases c <;> simp [edgeBallRoot,edgeBallDistance,branchDistance_root] <;> omega

theorem edgeBall_endpoint_ball_subset (m k : ℕ) (b : Bool) (v : RegularTreeVertex (m+2))
    (h : (regularWordTree (m+2)).edist (edgeBallEmbedding m k (edgeBallRoot m k b)) v ≤ (k : ℕ∞)) :
    v ∈ Set.range (edgeBallEmbedding m k) := by
  rw [edgeBallEmbedding_range]
  obtain ⟨p,hp⟩ := (regularWordTree (m+2)).exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (by simp) h)
  have hlen : p.length ≤ k := by exact_mod_cast hp.trans_le h
  have he : edgeBallEmbedding m k (edgeBallRoot m k b)=(if b then some (0,[]) else none) := by
    cases b <;> simp only [edgeBallEmbedding_left_root,edgeBallEmbedding_right_root,Bool.false_eq_true,if_false,if_true]
  exact (regularTreeEdgeDepth_le_dist_endpoint m b v).trans (by rw [← he]; exact (SimpleGraph.dist_le p).trans hlen)

def edgeToVertexBallEmbedding (m k : ℕ) : EdgeBallVertex (m+2) k ↪ VertexBallVertex (m+2) k where
  toFun := edgeToVertexBall m k
  inj' := by
    intro v w hvw
    apply edgeBallEmbedding_injective m k
    rw [← edgeToVertexBall_embedding,← edgeToVertexBall_embedding,hvw]

theorem edgeToVertexBall_graph_comap (m k : ℕ) :
    (vertexBallGraph (m+2) k).comap (edgeToVertexBallEmbedding m k)=edgeBallGraph m k := by
  apply SimpleGraph.ext
  funext v w
  apply propext
  change (regularWordTree (m+2)).Adj (vertexBallEmbedding (m+2) k (edgeToVertexBall m k v))
    (vertexBallEmbedding (m+2) k (edgeToVertexBall m k w)) ↔
    (regularWordTree (m+2)).Adj (edgeBallEmbedding m k v) (edgeBallEmbedding m k w)
  rw [edgeToVertexBall_embedding,edgeToVertexBall_embedding]

theorem pathNeighborhoodCode_edgeToVertexBall {A : Type*} (m k : ℕ)
    (color : VertexBallVertex (m+2) k → A) (b : Bool) :
    pathNeighborhoodCode (edgeBallGraph m k) k (color ∘ edgeToVertexBall m k) (edgeBallRoot m k b)=
      pathNeighborhoodCode (vertexBallGraph (m+2) k) k color (edgeToVertexBall m k (edgeBallRoot m k b)) := by
  rw [← edgeToVertexBall_graph_comap]
  apply pathNeighborhoodCode_comap _ (edgeToVertexBallEmbedding m k) k color (edgeBallRoot m k b)
  intro v hv
  have hglobal := (graphHom_edist_le (vertexBallEmbeddingHom (m+2) k)
    (edgeToVertexBall m k (edgeBallRoot m k b)) v).trans hv
  change (regularWordTree (m+2)).edist
    (vertexBallEmbedding (m+2) k (edgeToVertexBall m k (edgeBallRoot m k b)))
    (vertexBallEmbedding (m+2) k v) ≤ (k : ℕ∞) at hglobal
  rw [edgeToVertexBall_embedding] at hglobal
  obtain ⟨w,hw⟩ := edgeBall_endpoint_ball_subset m k b _ hglobal
  refine ⟨w,vertexBallEmbedding_injective (m+2) k ?_⟩
  change vertexBallEmbedding (m+2) k (edgeToVertexBall m k w)=_
  rw [edgeToVertexBall_embedding,hw]

end GaussianWave.BS.Lower
