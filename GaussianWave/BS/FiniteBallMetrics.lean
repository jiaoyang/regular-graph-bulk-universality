import GaussianWave.BS.FiniteBallGraph
import GaussianWave.BS.TreeBallDistances

/-! The induced finite ball has the same distances as the whole tree. -/
noncomputable section
open scoped Classical
namespace GaussianWave.BS

theorem vertexBallGraph_dist_embedding (d k : ℕ) (v w : VertexBallVertex d k) :
    (vertexBallGraph d k).dist v w =
      (regularWordTree d).dist (vertexBallEmbedding d k v) (vertexBallEmbedding d k w) := by
  obtain ⟨p,hp,hpd⟩ := (vertexBallGraph_connected d k).exists_path_of_dist v w
  have h := tree_path_length_eq_dist (regularWordTree_isTree d)
    (p.map (vertexBallEmbeddingHom d k))
    (p.map_isPath_of_injective (vertexBallEmbedding_injective d k) hp)
  simpa only [SimpleGraph.Walk.length_map,hpd] using h

theorem branchDepth_le (q k : ℕ) (v : BranchVertex q k) : branchDepth q k v ≤ k := by
  rw [← branchPath_length]
  exact branchPath_length_le q k v

theorem vertexBallGraph_dist_neighbor (m k : ℕ) (a : Fin (m+2)) (v : BranchVertex (m+1) k) :
    (vertexBallGraph (m+2) k).dist (vertexBallNeighbor (m+2) k a) (Sum.inr (a,v)) =
      branchDepth (m+1) k v := by
  rw [vertexBallGraph_dist_embedding]
  have hroot : branchPath (m+1) k (branchRoot (m+1) k) = [] := by cases k <;> rfl
  change (regularWordTree (m+2)).dist
    (some (a,(branchPath (m+1) k (branchRoot (m+1) k)).reverse))
    (some (a,(branchPath (m+1) k v).reverse)) = _
  rw [hroot]
  have h := regularTree_dist_same_branch (m+1) a [] (branchPath (m+1) k v)
  simpa only [List.reverse_nil,branchWordEmbedding_nil,regularTree_dist_root,
    branchWordEmbedding_depth,branchPath_length] using h

def vertexBallStarCenter (d k : ℕ) (i : Fin (d+1)) : VertexBallVertex d k :=
  Fin.cases (vertexBallRoot d k) (vertexBallNeighbor d k) i

theorem vertexBallGraph_near_center (m k : ℕ) (v : VertexBallVertex (m+2) k) :
    ∃ i : Fin (m+2+1),(vertexBallGraph (m+2) k).dist (vertexBallStarCenter (m+2) k i) v ≤ k := by
  cases v with
  | inl u =>
    refine ⟨0,?_⟩
    cases u
    exact le_trans (le_of_eq SimpleGraph.dist_self) (Nat.zero_le _)
  | inr av =>
    refine ⟨av.1.succ,?_⟩
    change (vertexBallGraph (m+2) k).dist (vertexBallNeighbor (m+2) k av.1) (Sum.inr av) ≤ k
    rw [vertexBallGraph_dist_neighbor]
    exact branchDepth_le (m+1) k av.2

end GaussianWave.BS
