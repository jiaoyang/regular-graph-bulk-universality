import GaussianWave.BS.RootedBallAutomorphismDecomposition
import GaussianWave.BS.BallProcessExtension

/-! Actual induced finite tree balls, their parent walks and intrinsic
graph distances. These convert ordinary finite graph automorphisms into
the explicit prefix-permutation groups. -/
noncomputable section
open scoped Classical
set_option maxHeartbeats 600000
namespace GaussianWave.BS

def vertexBallGraph (d k : ℕ) : SimpleGraph (VertexBallVertex d k) :=
  (regularWordTree d).comap (vertexBallEmbedding d k)

def vertexBallEmbeddingHom (d k : ℕ) : vertexBallGraph d k →g regularWordTree d where
  toFun := vertexBallEmbedding d k
  map_rel' := fun h => h

theorem regularTreeDepth_parent_le {d : ℕ} (v : RegularTreeVertex d) :
    regularTreeDepth (regularTreeParent v) ≤ regularTreeDepth v := by
  cases v with
  | none => exact le_refl _
  | some aw => have h := regularTreeDepth_parent aw.1 aw.2; exact Nat.le_of_lt (Nat.lt_of_add_one_le (le_of_eq h))

def vertexBallParent (d k : ℕ) (v : VertexBallVertex d k) : VertexBallVertex d k :=
  treeBallIndexOfDepth d k (regularTreeParent (vertexBallEmbedding d k v))
    ((regularTreeDepth_parent_le _).trans (vertexBallEmbedding_depth d k v))

@[simp] theorem vertexBallParent_embedding (d k : ℕ) (v : VertexBallVertex d k) :
    vertexBallEmbedding d k (vertexBallParent d k v) = regularTreeParent (vertexBallEmbedding d k v) :=
  treeBallIndexOfDepth_spec _ _ _ _

@[simp] theorem vertexBallParent_root (d k : ℕ) :
    vertexBallParent d k (vertexBallRoot d k) = vertexBallRoot d k := by
  apply vertexBallEmbedding_injective d k
  rw [vertexBallParent_embedding]
  rfl

theorem vertexBallEmbedding_ne_root {d k : ℕ} {v : VertexBallVertex d k}
    (hv : v ≠ vertexBallRoot d k) : vertexBallEmbedding d k v ≠ none := by
  intro he
  exact hv (vertexBallEmbedding_injective d k he)

theorem vertexBallParent_adj {d k : ℕ} {v : VertexBallVertex d k} (hv : v ≠ vertexBallRoot d k) :
    (vertexBallGraph d k).Adj v (vertexBallParent d k v) := by
  change (regularWordTree d).Adj (vertexBallEmbedding d k v) (vertexBallEmbedding d k (vertexBallParent d k v))
  rw [vertexBallParent_embedding]
  exact Or.inl ⟨vertexBallEmbedding_ne_root hv,rfl⟩

theorem vertexBallParent_depth {d k : ℕ} {v : VertexBallVertex d k} (hv : v ≠ vertexBallRoot d k) :
    regularTreeDepth (vertexBallEmbedding d k (vertexBallParent d k v))+1 =
      regularTreeDepth (vertexBallEmbedding d k v) := by
  rw [vertexBallParent_embedding]
  have hn := vertexBallEmbedding_ne_root hv
  cases h : vertexBallEmbedding d k v with
  | none => exact (hn h).elim
  | some aw => exact regularTreeDepth_parent aw.1 aw.2

theorem exists_vertexBallParentWalk (d k : ℕ) (v : VertexBallVertex d k) :
    ∃ p : (vertexBallGraph d k).Walk v (vertexBallRoot d k),
      p.length = regularTreeDepth (vertexBallEmbedding d k v) := by
  have haux (n : ℕ) : ∀ w : VertexBallVertex d k,
      regularTreeDepth (vertexBallEmbedding d k w)=n →
      ∃ p : (vertexBallGraph d k).Walk w (vertexBallRoot d k),p.length=n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn
      by_cases hw : w=vertexBallRoot d k
      · subst w
        refine ⟨.nil,?_⟩
        simpa only [vertexBallEmbedding,vertexBallRoot,regularTreeDepth,SimpleGraph.Walk.length_nil] using hn
      · have hp := vertexBallParent_depth hw
        obtain ⟨p,hpLen⟩ := ih (regularTreeDepth (vertexBallEmbedding d k (vertexBallParent d k w)))
          (by omega) (vertexBallParent d k w) rfl
        refine ⟨.cons (vertexBallParent_adj hw) p,?_⟩
        simp only [SimpleGraph.Walk.length_cons,hpLen]
        omega
  exact haux _ v rfl

theorem vertexBallGraph_connected (d k : ℕ) : (vertexBallGraph d k).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨vertexBallRoot d k,?_⟩
  intro v
  obtain ⟨p,_⟩ := exists_vertexBallParentWalk d k v
  exact ⟨p.reverse⟩

theorem vertexBallGraph_dist_root (d k : ℕ) (v : VertexBallVertex d k) :
    (vertexBallGraph d k).dist (vertexBallRoot d k) v = regularTreeDepth (vertexBallEmbedding d k v) := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := exists_vertexBallParentWalk d k v
    have h := (vertexBallGraph d k).dist_le p.reverse
    simpa only [SimpleGraph.Walk.length_reverse,hp] using h
  · obtain ⟨p,hp⟩ := (vertexBallGraph_connected d k).exists_walk_length_eq_dist (vertexBallRoot d k) v
    have h := regularTreeDepth_le_walk (p.map (vertexBallEmbeddingHom d k))
    change regularTreeDepth (vertexBallEmbedding d k v) ≤
      regularTreeDepth (vertexBallEmbedding d k (vertexBallRoot d k))+
        (p.map (vertexBallEmbeddingHom d k)).length at h
    rw [SimpleGraph.Walk.length_map,hp] at h
    simpa only [vertexBallEmbedding,vertexBallRoot,regularTreeDepth,zero_add] using h

theorem vertexBallGraphIso_dist (d k : ℕ) (e : vertexBallGraph d k ≃g vertexBallGraph d k)
    (v w : VertexBallVertex d k) :
    (vertexBallGraph d k).dist (e v) (e w) = (vertexBallGraph d k).dist v w := by
  have hle (f : vertexBallGraph d k ≃g vertexBallGraph d k) (a b : VertexBallVertex d k) :
      (vertexBallGraph d k).dist (f a) (f b) ≤ (vertexBallGraph d k).dist a b := by
    obtain ⟨p,hp⟩ := (vertexBallGraph_connected d k).exists_walk_length_eq_dist a b
    have h := (vertexBallGraph d k).dist_le (p.map f.toHom)
    simpa only [SimpleGraph.Walk.length_map,hp] using h
  apply le_antisymm (hle e v w)
  simpa only [e.symm_apply_apply] using hle e.symm (e v) (e w)

theorem vertexBallGraphIso_depth (d k : ℕ) (e : vertexBallGraph d k ≃g vertexBallGraph d k)
    (hroot : e (vertexBallRoot d k)=vertexBallRoot d k) (v : VertexBallVertex d k) :
    regularTreeDepth (vertexBallEmbedding d k (e v)) = regularTreeDepth (vertexBallEmbedding d k v) := by
  have h := vertexBallGraphIso_dist d k e (vertexBallRoot d k) v
  rw [hroot,vertexBallGraph_dist_root,vertexBallGraph_dist_root] at h
  exact h

theorem vertexBallGraphIso_parent (d k : ℕ) (e : vertexBallGraph d k ≃g vertexBallGraph d k)
    (hroot : e (vertexBallRoot d k)=vertexBallRoot d k) (v : VertexBallVertex d k) :
    e (vertexBallParent d k v)=vertexBallParent d k (e v) := by
  by_cases hv : v=vertexBallRoot d k
  · subst v
    simp only [vertexBallParent_root,hroot]
  · apply vertexBallEmbedding_injective d k
    rw [vertexBallParent_embedding]
    have h := e.map_rel_iff.mpr (vertexBallParent_adj hv)
    apply regularTree_adj_parent_of_depth_le h
    rw [vertexBallGraphIso_depth d k e hroot,vertexBallGraphIso_depth d k e hroot]
    rw [vertexBallParent_embedding]
    exact regularTreeDepth_parent_le _

theorem vertexBallAncestor_iff_parent_iterate (d k : ℕ) (v w : VertexBallVertex d k) :
    RootedBranchAncestor (d-1) k v w ↔ ∃ n : ℕ,((vertexBallParent d k)^[n]) w=v := by
  rw [vertexBallEmbedding_ancestor_iff]
  have hc : Function.Semiconj (vertexBallEmbedding d k) (vertexBallParent d k) regularTreeParent :=
    vertexBallParent_embedding d k
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n,vertexBallEmbedding_injective d k ?_⟩
    exact (hc.iterate_right n w).trans hn
  · rintro ⟨n,hn⟩
    exact ⟨n,(hc.iterate_right n w).symm.trans (congrArg (vertexBallEmbedding d k) hn)⟩

theorem vertexBallGraphIso_ancestor (d k : ℕ) (e : vertexBallGraph d k ≃g vertexBallGraph d k)
    (hroot : e (vertexBallRoot d k)=vertexBallRoot d k) (v w : VertexBallVertex d k) :
    RootedBranchAncestor (d-1) k (e v) (e w) ↔ RootedBranchAncestor (d-1) k v w := by
  rw [vertexBallAncestor_iff_parent_iterate,vertexBallAncestor_iff_parent_iterate]
  have hc : Function.Semiconj e (vertexBallParent d k) (vertexBallParent d k) :=
    vertexBallGraphIso_parent d k e hroot
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨n,e.injective ((hc.iterate_right n w).trans hn)⟩
  · rintro ⟨n,hn⟩
    exact ⟨n,(hc.iterate_right n w).symm.trans (congrArg e hn)⟩

theorem exists_vertexBallGraphIso_rooted_decomposition (d k : ℕ)
    (e : vertexBallGraph d k ≃g vertexBallGraph d k)
    (hroot : e (vertexBallRoot d k)=vertexBallRoot d k) :
    ∃ (σ : Equiv.Perm (Fin d)) (g : Fin d → BranchCoverOrdering (d-1) k),
      rootedBranchAutomorphism (d-1) k σ g = e.toEquiv := by
  apply exists_rootedBranchAutomorphism
  · intro v
    rw [← vertexBallEmbedding_depth_eq,← vertexBallEmbedding_depth_eq]
    exact vertexBallGraphIso_depth d k e hroot v
  · exact vertexBallGraphIso_ancestor d k e hroot

end GaussianWave.BS
