import GaussianWave.BS.FiniteBallMetrics
import GaussianWave.BS.FiniteEdgeStabilizer
import GaussianWave.BS.Lower.PathCodeGluing

/-! Every vertex and edge of the actual finite C/E trees is seen by the
radius-k path codes at its central star or central edge. -/
noncomputable section
open scoped Classical
namespace GaussianWave.BS.Lower

theorem pathCoveredVertex_of_dist {V I : Type*} (H : SimpleGraph V) (hc : H.Connected)
    (R : ℕ) (center : I → V) (v : V) (h : ∃ i,H.dist (center i) v ≤ R) :
    PathCoveredVertex H R center v := by
  apply pathCoveredVertex_of_edist
  obtain ⟨i,hi⟩ := h
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist (center i) v
  exact ⟨i,p.edist_le.trans (by exact_mod_cast hp.trans_le hi)⟩

theorem pathCoveredEdge_of_short_dist {V I : Type*} (H : SimpleGraph V) (hc : H.Connected)
    (R : ℕ) (center : I → V) (u v : V) (huv : H.Adj u v)
    (h : ∃ i,H.dist (center i) u+1 ≤ R) : PathCoveredEdge H R center u v := by
  apply pathCoveredEdge_of_short_edist H R center u v huv
  obtain ⟨i,hi⟩ := h
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist (center i) u
  refine ⟨i,(add_le_add_right p.edist_le 1).trans ?_⟩
  exact_mod_cast (show p.length+1 ≤ R by omega)

theorem vertexBall_pathCoveredVertex (m k : ℕ) (v : VertexBallVertex (m+2) k) :
    PathCoveredVertex (GaussianWave.BS.vertexBallGraph (m+2) k) k (vertexBallStarCenter (m+2) k) v :=
  pathCoveredVertex_of_dist _ (vertexBallGraph_connected (m+2) k) k _ v (vertexBallGraph_near_center m k v)

theorem vertexBallNeighbor_embedding (d k : ℕ) (a : Fin d) :
    vertexBallEmbedding d k (vertexBallNeighbor d k a)=some (a,[]) := by cases k <;> rfl

theorem vertexBall_adj_root_neighbor (d k : ℕ) {v : VertexBallVertex d k}
    (h : (GaussianWave.BS.vertexBallGraph d k).Adj (vertexBallRoot d k) v) :
    ∃ a,v=vertexBallNeighbor d k a := by
  change (regularWordTree d).Adj none (vertexBallEmbedding d k v) at h
  obtain ⟨a,ha⟩ := exists_regularTreeNeighbor_of_adj none (vertexBallEmbedding d k v) h
  refine ⟨a,vertexBallEmbedding_injective d k ?_⟩
  rw [vertexBallNeighbor_embedding]
  exact ha.symm

theorem vertexBall_pathCoveredEdge (m k : ℕ) (u v : VertexBallVertex (m+2) k)
    (huv : (GaussianWave.BS.vertexBallGraph (m+2) k).Adj u v) :
    PathCoveredEdge (GaussianWave.BS.vertexBallGraph (m+2) k) k (vertexBallStarCenter (m+2) k) u v := by
  by_cases hu : u=vertexBallRoot (m+2) k
  · subst u
    obtain ⟨a,ha⟩ := vertexBall_adj_root_neighbor (m+2) k huv
    exact Or.inl ⟨0,a.succ,rfl,ha.symm⟩
  by_cases hv : v=vertexBallRoot (m+2) k
  · subst v
    obtain ⟨a,ha⟩ := vertexBall_adj_root_neighbor (m+2) k huv.symm
    exact Or.inl ⟨a.succ,0,ha.symm,rfl⟩
  cases u with
  | inl t => exact (hu (by cases t; rfl)).elim
  | inr av =>
    cases v with
    | inl t => exact (hv (by cases t; rfl)).elim
    | inr bw =>
      rcases av with ⟨a,x⟩
      rcases bw with ⟨b,y⟩
      have hbranch := regularTreeFirstBranch_adj huv (by exact Option.some_ne_none _) (by exact Option.some_ne_none _)
      have hab : a=b := Option.some.inj hbranch
      subst b
      have hd := (regularTree_adj_depth huv).symm
      change regularTreeDepth (vertexBallEmbedding (m+2) k (Sum.inr (a,y)))+1 =
          regularTreeDepth (vertexBallEmbedding (m+2) k (Sum.inr (a,x))) ∨
        regularTreeDepth (vertexBallEmbedding (m+2) k (Sum.inr (a,x)))+1 =
          regularTreeDepth (vertexBallEmbedding (m+2) k (Sum.inr (a,y))) at hd
      simp only [vertexBallEmbedding,regularTreeDepth,List.length_reverse,branchPath_length] at hd
      change (branchDepth (m+1) k y+1)+1=branchDepth (m+1) k x+1 ∨
        (branchDepth (m+1) k x+1)+1=branchDepth (m+1) k y+1 at hd
      have hx := branchDepth_le (m+1) k x
      have hy := branchDepth_le (m+1) k y
      rcases hd with hd | hd
      · apply PathCoveredEdge.symm
        apply pathCoveredEdge_of_short_dist _ (vertexBallGraph_connected (m+2) k) k _ _ _ huv.symm
        refine ⟨a.succ,?_⟩
        change (GaussianWave.BS.vertexBallGraph (m+2) k).dist (vertexBallNeighbor (m+2) k a) (Sum.inr (a,y))+1 ≤ k
        rw [vertexBallGraph_dist_neighbor]
        omega
      · apply pathCoveredEdge_of_short_dist _ (vertexBallGraph_connected (m+2) k) k _ _ _ huv
        refine ⟨a.succ,?_⟩
        change (GaussianWave.BS.vertexBallGraph (m+2) k).dist (vertexBallNeighbor (m+2) k a) (Sum.inr (a,x))+1 ≤ k
        rw [vertexBallGraph_dist_neighbor]
        omega

theorem branchDistance_root (q k : ℕ) (v : BranchVertex q k) :
    branchDistance q k (branchRoot q k) v=branchDepth q k v := by
  have hroot : branchPath q k (branchRoot q k)=[] := by cases k <;> rfl
  rw [branchDistance_eq_word,hroot]
  exact branchPath_length q k v

theorem branchDepth_eq_zero_iff (q k : ℕ) (v : BranchVertex q k) :
    branchDepth q k v=0 ↔ v=branchRoot q k := by
  have hroot : branchPath q k (branchRoot q k)=[] := by cases k <;> rfl
  constructor
  · intro h
    apply branchPath_injective q k
    rw [hroot]
    apply List.length_eq_zero_iff.mp
    rw [branchPath_length,h]
  · rintro rfl
    rw [← branchPath_length,hroot]
    rfl

theorem edgeBallGraph_dist_root_half (m k : ℕ) (b : Bool) (v : BranchVertex (m+1) k) :
    (edgeBallGraph m k).dist (edgeBallRoot m k b) (b,v)=branchDepth (m+1) k v := by
  change (edgeBallParentClosedTree m k).graph.dist (edgeBallRoot m k b) (b,v)=_
  rw [(edgeBallParentClosedTree m k).dist_embedding]
  change (regularWordTree (m+2)).dist (edgeBallEmbedding m k (edgeBallRoot m k b))
    (edgeBallEmbedding m k (b,v)) = _
  rw [edgeBallEmbedding_dist]
  change (if b=b then branchDistance (m+1) k (branchRoot (m+1) k) v else _)=_
  rw [if_pos rfl,branchDistance_root]

theorem edgeBall_pathCoveredVertex (m k : ℕ) (v : EdgeBallVertex (m+2) k) :
    PathCoveredVertex (edgeBallGraph m k) k (edgeBallRoot m k) v := by
  apply pathCoveredVertex_of_dist _ (edgeBallParentClosedTree m k).connected
  rcases v with ⟨b,v⟩
  refine ⟨b,?_⟩
  change (edgeBallGraph m k).dist (edgeBallRoot m k b) (b,v) ≤ k
  rw [edgeBallGraph_dist_root_half]
  exact branchDepth_le (m+1) k v

theorem edgeBall_pathCoveredEdge (m k : ℕ) (u v : EdgeBallVertex (m+2) k)
    (huv : (edgeBallGraph m k).Adj u v) :
    PathCoveredEdge (edgeBallGraph m k) k (edgeBallRoot m k) u v := by
  rcases u with ⟨b,u⟩
  rcases v with ⟨c,v⟩
  by_cases hbc : b=c
  · subst c
    have hd := regularTree_adj_depth huv
    change regularTreeDepth (edgeBallEmbedding m k (b,u))+1=regularTreeDepth (edgeBallEmbedding m k (b,v)) ∨
      regularTreeDepth (edgeBallEmbedding m k (b,v))+1=regularTreeDepth (edgeBallEmbedding m k (b,u)) at hd
    simp only [edgeBallEmbedding_depth_exact,branchPath_length] at hd
    have hu := branchDepth_le (m+1) k u
    have hv := branchDepth_le (m+1) k v
    rcases hd with hd | hd
    · apply pathCoveredEdge_of_short_dist _ (edgeBallParentClosedTree m k).connected k _ _ _ huv
      refine ⟨b,?_⟩
      change (edgeBallGraph m k).dist (edgeBallRoot m k b) (b,u)+1 ≤ k
      rw [edgeBallGraph_dist_root_half]
      omega
    · apply PathCoveredEdge.symm
      apply pathCoveredEdge_of_short_dist _ (edgeBallParentClosedTree m k).connected k _ _ _ huv.symm
      refine ⟨b,?_⟩
      change (edgeBallGraph m k).dist (edgeBallRoot m k b) (b,v)+1 ≤ k
      rw [edgeBallGraph_dist_root_half]
      omega
  · have hdist := SimpleGraph.dist_eq_one_iff_adj.mpr huv
    change (edgeBallParentClosedTree m k).graph.dist (b,u) (c,v)=1 at hdist
    rw [(edgeBallParentClosedTree m k).dist_embedding] at hdist
    change (regularWordTree (m+2)).dist (edgeBallEmbedding m k (b,u)) (edgeBallEmbedding m k (c,v))=1 at hdist
    rw [edgeBallEmbedding_dist] at hdist
    change (if b=c then branchDistance (m+1) k u v else
      branchDepth (m+1) k u+branchDepth (m+1) k v+1)=1 at hdist
    rw [if_neg hbc] at hdist
    have hu : u=branchRoot (m+1) k := (branchDepth_eq_zero_iff (m+1) k u).mp (by omega)
    have hv : v=branchRoot (m+1) k := (branchDepth_eq_zero_iff (m+1) k v).mp (by omega)
    subst u
    subst v
    exact Or.inl ⟨b,c,rfl,rfl⟩

end GaussianWave.BS.Lower
