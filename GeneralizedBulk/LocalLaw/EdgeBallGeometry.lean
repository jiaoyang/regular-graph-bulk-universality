import GeneralizedBulk.LocalLaw.EdgeBallCoverIso
import GeneralizedBulk.LocalLaw.EdgeBallCharts
import GaussianWave.BS.Lower.CoverInjectivityEvent

/-! Construct the required rooted word-tree isomorphism from actual finite
regular-graph cover injectivity. No tree-ball isomorphism is assumed. -/
noncomputable section
open scoped Classical
namespace GeneralizedBulk.Graph
open GaussianWave.BS GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Graph.Configuration

def rootedWordCoverIso {W : Type*} {G : SimpleGraph W} (m R : ℕ)
    (F : regularWordTree (m+2) →g G)
    (hsurj : ∀ v y, G.Adj (F v) y → ∃ w, (regularWordTree (m+2)).Adj v w ∧ F w = y)
    (hinj : Set.InjOn F (geometryBall (regularWordTree (m+2)) none (R+2))) :
    RootedEdgeBallIso G (F none) (F (some (0,[]))) (m+2) R := by
  let e := (edgeWordBallIso m R).trans
    (coverEdgeBallIso F hsurj none (some (0,[]))
      (regularTreeNeighbor_adj (d := m+2) none (0 : Fin (m+2))) R hinj)
  refine { toIso := e.symm, left := ?_, right := ?_ }
  · apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change F none = F (edgeWordEmbedding m R (edgeTreeRoot (m+2) R 0))
    rw [edgeWordEmbedding_root_zero]
  · apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change F (some (0,[])) = F (edgeWordEmbedding m R (edgeTreeRoot (m+2) R 1))
    rw [edgeWordEmbedding_root_one]

theorem wordTree_depth_le_of_edist_le (d R : ℕ) (x : RegularTreeVertex d)
    (hx : (regularWordTree d).edist none x ≤ (R : ℕ∞)) :
    regularTreeDepth x ≤ R := by
  obtain ⟨p,hp⟩ := (regularWordTree d).exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (by simp) hx)
  have hlen : p.length ≤ R := by exact_mod_cast hp.trans_le hx
  have hdepth := regularTreeDepth_le_walk p
  have hd : regularTreeDepth x ≤ p.length := by
    simpa only [regularTreeDepth,zero_add] using hdepth
  exact hd.trans hlen

def geometryCoverSeed {N m : ℕ} (G : GaussianWave.BS.Reused.Graph.RegularGraph N (m+2))
    (k : ℕ) (a b : Fin N) (hab : G.val.Adj a b) : VertexCoverSeed N m k :=
  (a,Equiv.swap 0 ((canonicalPortLabeling G a).symm ⟨b,hab⟩),fun _ => default)

theorem geometryCoverSeed_right {N m : ℕ} (G : GaussianWave.BS.Reused.Graph.RegularGraph N (m+2))
    (k : ℕ) (a b : Fin N) (hab : G.val.Adj a b) :
    infiniteVertexGraphCover G k (geometryCoverSeed G k a b hab) (some (0,[])) = b := by
  let seed := geometryCoverSeed G k a b hab
  have he := infiniteVertexGraphCover_restrict G k seed (vertexBallNeighbor (m+2) k 0)
  rw [vertexBallNeighbor_embedding] at he
  rw [he,vertexGraphCover_neighbor]
  change graphNeighbor G a ((Equiv.swap 0 ((canonicalPortLabeling G a).symm ⟨b,hab⟩)) 0) = b
  rw [Equiv.swap_apply_left]
  exact congrArg Subtype.val ((canonicalPortLabeling G a).apply_symm_apply ⟨b,hab⟩)

theorem goodCover_infinite_injOn {N m : ℕ} (G : GaussianWave.BS.Reused.Graph.RegularGraph N (m+2))
    (R : ℕ) (a : Fin N) (hgood : GoodVertexCoverRoot G (R+1) a)
    (seed : VertexCoverSeed N m (R+1)) (hseed : seed.1 = a) :
    Set.InjOn (infiniteVertexGraphHom G (R+1) seed)
      (geometryBall (regularWordTree (m+2)) none (R+2)) := by
  intro x hx y hy hxy
  have hxdepth := wordTree_depth_le_of_edist_le (m+2) (R+2) x hx
  have hydepth := wordTree_depth_le_of_edist_le (m+2) (R+2) y hy
  obtain ⟨u,hu⟩ := (Set.ext_iff.mp (vertexBallEmbedding_range (m+2) (R+1)) x).mpr hxdepth
  obtain ⟨v,hv⟩ := (Set.ext_iff.mp (vertexBallEmbedding_range (m+2) (R+1)) y).mpr hydepth
  change infiniteVertexGraphCover G (R+1) seed x = infiniteVertexGraphCover G (R+1) seed y at hxy
  rw [← hu,← hv,infiniteVertexGraphCover_restrict,infiniteVertexGraphCover_restrict] at hxy
  have huv := hgood seed hseed hxy
  exact hu.symm.trans ((congrArg (vertexBallEmbedding (m+2) (R+1)) huv).trans hv)

theorem rootedEdgeBallIso_of_goodCover {N m : ℕ}
    (G : GaussianWave.BS.Reused.Graph.RegularGraph N (m+2))
    (R : ℕ) (a b : Fin N) (hab : G.val.Adj a b)
    (hgood : GoodVertexCoverRoot G (R+1) a) :
    Nonempty (RootedEdgeBallIso G.val a b (m+2) R) := by
  let seed := geometryCoverSeed G (R+1) a b hab
  let F := infiniteVertexGraphHom G (R+1) seed
  have hs := infiniteVertexGraphCover_neighbor_surjective G (R+1) seed
  have hi := goodCover_infinite_injOn G R a hgood seed rfl
  have he : Nonempty (RootedEdgeBallIso G.val (F none) (F (some (0,[]))) (m+2) R) :=
    ⟨rootedWordCoverIso m R F hs hi⟩
  have hleft : F none = a := rfl
  have hright : F (some (0,[])) = b := geometryCoverSeed_right G (R+1) a b hab
  simpa only [hleft,hright] using he

theorem acyclic_ball_of_goodCover {N m : ℕ}
    (G : GaussianWave.BS.Reused.Graph.RegularGraph N (m+2))
    (R : ℕ) (a b : Fin N) (hab : G.val.Adj a b)
    (hgood : GoodVertexCoverRoot G (R+1) a) :
    (G.val.induce (geometryBall G.val a R)).IsAcyclic := by
  let seed := geometryCoverSeed G (R+1) a b hab
  let F := infiniteVertexGraphHom G (R+1) seed
  have hs := infiniteVertexGraphCover_neighbor_surjective G (R+1) seed
  have hi := goodCover_infinite_injOn G R a hgood seed rfl
  have hi' : Set.InjOn F (geometryBall (regularWordTree (m+2)) none (R+1)) := by
    intro x hx y hy hxy
    have hx' : x ∈ geometryBall (regularWordTree (m+2)) none (R+2) :=
      hx.trans (show ((R+1 : ℕ) : ℕ∞) ≤ ((R+2 : ℕ) : ℕ∞) by exact_mod_cast Nat.le_succ (R+1))
    have hy' : y ∈ geometryBall (regularWordTree (m+2)) none (R+2) :=
      hy.trans (show ((R+1 : ℕ) : ℕ∞) ≤ ((R+2 : ℕ) : ℕ∞) by exact_mod_cast Nat.le_succ (R+1))
    exact hi hx' hy' hxy
  let e := coverVertexBallIso F hs none R hi'
  let J : G.val.induce (geometryBall G.val (F none) R) →g regularWordTree (m+2) := {
    toFun := fun v => (e.symm v).val
    map_rel' := fun h => e.symm.toHom.map_adj h }
  have hJ : Function.Injective J := by
    intro x y h
    exact e.symm.injective (Subtype.ext h)
  have hacy := acyclic_of_injective_hom (regularWordTree_isTree (m+2)).IsAcyclic J hJ
  exact hacy

end GeneralizedBulk.Graph
