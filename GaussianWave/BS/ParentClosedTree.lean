import GaussianWave.BS.FiniteBallGraph

/-! Any literal parent-closed embedded subtree has the inherited rooted
geometry. This applies to the two-center edge balls as well as vertex balls. -/
noncomputable section
open scoped Classical
set_option maxHeartbeats 600000
namespace GaussianWave.BS

structure ParentClosedTree (d : ℕ) (V : Type*) where
  embedding : V ↪ RegularTreeVertex d
  root : V
  root_embedding : embedding root = none
  parent : V → V
  parent_embedding : ∀ v,embedding (parent v)=regularTreeParent (embedding v)

namespace ParentClosedTree
variable {d : ℕ} {V : Type*} (S : ParentClosedTree d V)

def graph : SimpleGraph V := (regularWordTree d).comap S.embedding

def embeddingHom : S.graph →g regularWordTree d where
  toFun := S.embedding
  map_rel' := fun h => h

theorem parent_root : S.parent S.root=S.root := by
  apply S.embedding.injective
  rw [S.parent_embedding,S.root_embedding]
  rfl

theorem embedding_ne_root {v : V} (hv : v ≠ S.root) : S.embedding v ≠ none := by
  intro h
  exact hv (S.embedding.injective (h.trans S.root_embedding.symm))

theorem parent_adj {v : V} (hv : v ≠ S.root) : S.graph.Adj v (S.parent v) := by
  change (regularWordTree d).Adj (S.embedding v) (S.embedding (S.parent v))
  rw [S.parent_embedding]
  exact Or.inl ⟨S.embedding_ne_root hv,rfl⟩

theorem parent_depth {v : V} (hv : v ≠ S.root) :
    regularTreeDepth (S.embedding (S.parent v))+1=regularTreeDepth (S.embedding v) := by
  rw [S.parent_embedding]
  cases h : S.embedding v with
  | none => exact (S.embedding_ne_root hv h).elim
  | some aw => exact regularTreeDepth_parent aw.1 aw.2

theorem exists_parentWalk (v : V) : ∃ p : S.graph.Walk v S.root,
    p.length=regularTreeDepth (S.embedding v) := by
  have haux (n : ℕ) : ∀ w,regularTreeDepth (S.embedding w)=n →
      ∃ p : S.graph.Walk w S.root,p.length=n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn
      by_cases hw : w=S.root
      · subst w
        refine ⟨.nil,?_⟩
        simpa only [S.root_embedding,regularTreeDepth,SimpleGraph.Walk.length_nil] using hn
      · have hp := S.parent_depth hw
        obtain ⟨p,hpLen⟩ := ih (regularTreeDepth (S.embedding (S.parent w))) (by omega) (S.parent w) rfl
        refine ⟨.cons (S.parent_adj hw) p,?_⟩
        simp only [SimpleGraph.Walk.length_cons,hpLen]
        omega
  exact haux _ v rfl

theorem connected : S.graph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨S.root,fun v => ?_⟩
  obtain ⟨p,_⟩ := S.exists_parentWalk v
  exact ⟨p.reverse⟩

theorem dist_root (v : V) : S.graph.dist S.root v=regularTreeDepth (S.embedding v) := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := S.exists_parentWalk v
    have h := S.graph.dist_le p.reverse
    simpa only [SimpleGraph.Walk.length_reverse,hp] using h
  · obtain ⟨p,hp⟩ := S.connected.exists_walk_length_eq_dist S.root v
    have h := regularTreeDepth_le_walk (p.map S.embeddingHom)
    change regularTreeDepth (S.embedding v) ≤ regularTreeDepth (S.embedding S.root)+(p.map S.embeddingHom).length at h
    rw [S.root_embedding,SimpleGraph.Walk.length_map,hp] at h
    simpa only [regularTreeDepth,zero_add] using h

theorem dist_embedding (u v : V) : S.graph.dist u v=(regularWordTree d).dist (S.embedding u) (S.embedding v) := by
  obtain ⟨p,hp,hpd⟩ := S.connected.exists_path_of_dist u v
  have h := tree_path_length_eq_dist (regularWordTree_isTree d) (p.map S.embeddingHom)
    (p.map_isPath_of_injective S.embedding.injective hp)
  simpa only [SimpleGraph.Walk.length_map,hpd] using h

theorem iso_dist (e : S.graph ≃g S.graph) (v w : V) : S.graph.dist (e v) (e w)=S.graph.dist v w := by
  have hle (f : S.graph ≃g S.graph) (a b : V) : S.graph.dist (f a) (f b) ≤ S.graph.dist a b := by
    obtain ⟨p,hp⟩ := S.connected.exists_walk_length_eq_dist a b
    have h := S.graph.dist_le (p.map f.toHom)
    simpa only [SimpleGraph.Walk.length_map,hp] using h
  apply le_antisymm (hle e v w)
  simpa only [e.symm_apply_apply] using hle e.symm (e v) (e w)

theorem iso_depth (e : S.graph ≃g S.graph) (he : e S.root=S.root) (v : V) :
    regularTreeDepth (S.embedding (e v))=regularTreeDepth (S.embedding v) := by
  have h := S.iso_dist e S.root v
  rw [he,S.dist_root,S.dist_root] at h
  exact h

theorem iso_parent (e : S.graph ≃g S.graph) (he : e S.root=S.root) (v : V) :
    e (S.parent v)=S.parent (e v) := by
  by_cases hv : v=S.root
  · subst v
    rw [S.parent_root,he,S.parent_root]
  · apply S.embedding.injective
    rw [S.parent_embedding]
    have h := e.map_rel_iff.mpr (S.parent_adj hv)
    apply regularTree_adj_parent_of_depth_le h
    rw [S.iso_depth e he,S.iso_depth e he,S.parent_embedding]
    exact regularTreeDepth_parent_le _

theorem ancestor_iff_parent_iterate (u v : V) :
    RegularTreeAncestor (S.embedding u) (S.embedding v) ↔ ∃ n : ℕ,(S.parent^[n]) v=u := by
  have hc : Function.Semiconj S.embedding S.parent regularTreeParent := S.parent_embedding
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨n,S.embedding.injective ((hc.iterate_right n v).trans hn)⟩
  · rintro ⟨n,hn⟩
    exact ⟨n,(hc.iterate_right n v).symm.trans (congrArg S.embedding hn)⟩

theorem iso_ancestor (e : S.graph ≃g S.graph) (he : e S.root=S.root) (u v : V) :
    RegularTreeAncestor (S.embedding (e u)) (S.embedding (e v)) ↔
      RegularTreeAncestor (S.embedding u) (S.embedding v) := by
  rw [S.ancestor_iff_parent_iterate,S.ancestor_iff_parent_iterate]
  have hc : Function.Semiconj e S.parent S.parent := S.iso_parent e he
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨n,e.injective ((hc.iterate_right n v).trans hn)⟩
  · rintro ⟨n,hn⟩
    exact ⟨n,(hc.iterate_right n v).symm.trans (congrArg e hn)⟩

end ParentClosedTree
end GaussianWave.BS
