import GaussianWave.BS.FiniteBallGraph
import GaussianWave.BS.BranchFamilyActions
import GaussianWave.BS.TreeAutomorphisms

/-! The concrete star-center stabilizer is exactly the finite branch
permutation group. Both its graph action and completeness are proved. -/
noncomputable section
open scoped Classical
namespace GaussianWave.BS

def vertexBallStabilizerGraphIso (d k : ℕ) (g : VertexBallStabilizer d k) :
    vertexBallGraph d k ≃g vertexBallGraph d k where
  toEquiv := MulAction.toPerm g
  map_rel_iff' := by
    intro v w
    have hc (u : VertexBallVertex d k) :
        regularTreeBranchAutomorphism d k g (vertexBallEmbedding d k u) =
          vertexBallEmbedding d k (g • u) := by
      cases u with
      | inl t => rfl
      | inr av => exact vertexBallEmbedding_branchAutomorphism d k g av.1 av.2
    change (regularWordTree d).Adj (vertexBallEmbedding d k (g • v))
      (vertexBallEmbedding d k (g • w)) ↔
      (regularWordTree d).Adj (vertexBallEmbedding d k v) (vertexBallEmbedding d k w)
    rw [← hc v,← hc w]
    exact (regularTreeBranchAutomorphism d k g).map_rel_iff

@[simp] theorem vertexBallStabilizerGraphIso_apply (d k : ℕ) (g : VertexBallStabilizer d k)
    (v : VertexBallVertex d k) : vertexBallStabilizerGraphIso d k g v = g • v := rfl

@[simp] theorem vertexBallStabilizerGraphIso_root (d k : ℕ) (g : VertexBallStabilizer d k) :
    vertexBallStabilizerGraphIso d k g (vertexBallRoot d k)=vertexBallRoot d k := rfl

@[simp] theorem vertexBallStabilizerGraphIso_neighbor (d k : ℕ) (g : VertexBallStabilizer d k)
    (a : Fin d) : vertexBallStabilizerGraphIso d k g (vertexBallNeighbor d k a)=vertexBallNeighbor d k a := by
  change Sum.inr (a,branchAutomorphism (d-1) k (g a) (branchRoot (d-1) k)) = _
  rw [branchAutomorphism_root]
  rfl

theorem exists_vertexBallStabilizer_of_graphIso (d k : ℕ)
    (e : vertexBallGraph d k ≃g vertexBallGraph d k)
    (hroot : e (vertexBallRoot d k)=vertexBallRoot d k)
    (hneighbors : ∀ a,e (vertexBallNeighbor d k a)=vertexBallNeighbor d k a) :
    ∃ g : VertexBallStabilizer d k,∀ v,g • v=e v := by
  obtain ⟨σ,g,hg⟩ := exists_vertexBallGraphIso_rooted_decomposition d k e hroot
  have hσ (a : Fin d) : σ a=a := by
    have h : rootedBranchAutomorphism (d-1) k σ g (vertexBallNeighbor d k a) =
        e (vertexBallNeighbor d k a) := congrArg (fun p => p (vertexBallNeighbor d k a)) hg
    rw [hneighbors a] at h
    change Sum.inr (σ a,branchAutomorphism (d-1) k (g a) (branchRoot (d-1) k)) =
      Sum.inr (a,branchRoot (d-1) k) at h
    rw [branchAutomorphism_root] at h
    exact congrArg Prod.fst (Sum.inr.inj h)
  have hσeq : σ=1 := Equiv.ext hσ
  subst σ
  refine ⟨g,fun v => ?_⟩
  have h : rootedBranchAutomorphism (d-1) k 1 g v = e v := congrArg (fun p => p v) hg
  exact h

end GaussianWave.BS
