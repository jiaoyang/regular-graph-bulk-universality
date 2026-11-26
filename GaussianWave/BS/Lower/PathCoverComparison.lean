import GaussianWave.BS.Lower.PathNeighborhoodCode
import GaussianWave.BS.InfiniteCoverPathLifting
import GaussianWave.BS.TreeHomogeneity

/-! Exact comparison of literal path-neighborhood codes on a finite graph
and on its actual sampled finite tree cover. No cover-injectivity premise
is required for this deterministic coding identity. -/
noncomputable section
open scoped Classical
set_option maxHeartbeats 1200000
namespace GaussianWave.BS.Lower
open GaussianWave.BS GaussianWave.BS.Reused.Graph

theorem pathNeighborhoodCode_graphCover {V W A : Type*} {H : SimpleGraph V} {K : SimpleGraph W}
    (F : H →g K) (hsurj : ∀ v y,K.Adj (F v) y → ∃ w,H.Adj v w ∧ F w=y)
    (R : ℕ) (color : W → A) (o : V) :
    pathNeighborhoodCode H R (color ∘ F) o=pathNeighborhoodCode K R color (F o) := by
  funext word
  simp only [pathNeighborhoodCode]
  congr 1
  apply propext
  constructor
  · rintro ⟨p,hp0,hp,hc⟩
    exact ⟨fun i => F (p i),congrArg F hp0,fun j => F.map_rel (hp j),hc⟩
  · rintro ⟨p,hp0,hp,hc⟩
    obtain ⟨q,hq0,hq,hqmap⟩ := graphHom_lift_pathTuple F hsurj word.1.val p hp o hp0.symm
    refine ⟨q,hq0,hq,fun j => ?_⟩
    exact (congrArg color (hqmap j)).trans (hc j)

/-- Restricting to an induced graph containing the entire relevant ball
does not change any bounded-length colored path word. -/
theorem pathNeighborhoodCode_comap {U V A : Type*} (K : SimpleGraph V) (j : U ↪ V)
    (R : ℕ) (color : V → A) (o : U)
    (hball : ∀ v,K.edist (j o) v ≤ (R : ℕ∞) → v ∈ Set.range j) :
    pathNeighborhoodCode (K.comap j) R (color ∘ j) o=pathNeighborhoodCode K R color (j o) := by
  funext word
  simp only [pathNeighborhoodCode]
  congr 1
  apply propext
  constructor
  · rintro ⟨p,hp0,hp,hc⟩
    exact ⟨fun i => j (p i),congrArg j hp0,hp,hc⟩
  · rintro ⟨p,hp0,hp,hc⟩
    have hex (i : Fin (word.1.val+1)) : ∃ u : U,j u=p i := by
      apply Set.mem_range.mp
      apply hball
      rw [← hp0]
      exact (pathTuple_edist_le K word.1.val p hp i).trans (by exact_mod_cast (by omega : i.val ≤ R))
    let q i := (hex i).choose
    have hq i : j (q i)=p i := (hex i).choose_spec
    refine ⟨q,j.injective ((hq 0).trans hp0),fun i => ?_,fun i => ?_⟩
    · change K.Adj (j (q i.castSucc)) (j (q i.succ))
      rw [hq,hq]
      exact hp i
    · exact (congrArg color (hq i)).trans (hc i)

theorem regularTreeDepth_le_of_edist_le (d : ℕ) (o v : RegularTreeVertex d) (R : ℕ)
    (h : (regularWordTree d).edist o v ≤ (R : ℕ∞)) :
    regularTreeDepth v ≤ regularTreeDepth o+R := by
  obtain ⟨p,hp⟩ := (regularWordTree d).exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (by simp) h)
  have hlen : p.length ≤ R := by exact_mod_cast hp.trans_le h
  calc
    _ = (regularWordTree d).dist none v := (regularTree_dist_root d v).symm
    _ ≤ (regularWordTree d).dist none o+(regularWordTree d).dist o v :=
      (regularWordTree_connected d).dist_triangle
    _ ≤ _ := by rw [regularTree_dist_root]; exact Nat.add_le_add_left ((SimpleGraph.dist_le p).trans hlen) _

def vertexBallGraph (d k : ℕ) : SimpleGraph (VertexBallVertex d k) :=
  (regularWordTree d).comap (vertexBallEmbedding d k)

theorem pathNeighborhoodCode_vertexBall {A : Type*} (d k : ℕ)
    (color : RegularTreeVertex d → A) (o : VertexBallVertex d k)
    (ho : regularTreeDepth (vertexBallEmbedding d k o) ≤ 1) :
    pathNeighborhoodCode (vertexBallGraph d k) k (color ∘ vertexBallEmbedding d k) o=
      pathNeighborhoodCode (regularWordTree d) k color (vertexBallEmbedding d k o) := by
  apply pathNeighborhoodCode_comap (regularWordTree d)
    ⟨vertexBallEmbedding d k,vertexBallEmbedding_injective d k⟩ k color o
  intro v hv
  change (regularWordTree d).edist (vertexBallEmbedding d k o) v ≤ (k : ℕ∞) at hv
  change v ∈ Set.range (vertexBallEmbedding d k)
  rw [vertexBallEmbedding_range]
  exact (regularTreeDepth_le_of_edist_le d _ v k hv).trans (by omega)

/-- Exact local-code identity for the literal sampled cover. It remains
valid at colliding roots; collisions matter only for independent recoloring
of distinct graph vertices. -/
theorem pathNeighborhoodCode_vertexGraphCover {N m : ℕ} {A : Type*}
    (G : RegularGraph N (m+2)) (k : ℕ) (seed : VertexCoverSeed N m k)
    (color : Fin N → A) (o : VertexBallVertex (m+2) k)
    (ho : regularTreeDepth (vertexBallEmbedding (m+2) k o) ≤ 1) :
    pathNeighborhoodCode (vertexBallGraph (m+2) k) k (color ∘ vertexGraphCover G k seed) o=
      pathNeighborhoodCode G.val k color (vertexGraphCover G k seed o) := by
  have heq : color ∘ vertexGraphCover G k seed=
      (color ∘ infiniteVertexGraphCover G k seed) ∘ vertexBallEmbedding (m+2) k := by
    funext v
    simp only [Function.comp_apply,infiniteVertexGraphCover_restrict]
  rw [heq,pathNeighborhoodCode_vertexBall (m+2) k _ o ho]
  have h := pathNeighborhoodCode_graphCover (infiniteVertexGraphHom G k seed)
    (infiniteVertexGraphCover_neighbor_surjective G k seed) k color (vertexBallEmbedding (m+2) k o)
  change pathNeighborhoodCode (regularWordTree (m+2)) k (color ∘ infiniteVertexGraphCover G k seed)
      (vertexBallEmbedding (m+2) k o)=pathNeighborhoodCode G.val k color
        (infiniteVertexGraphCover G k seed (vertexBallEmbedding (m+2) k o)) at h
  rw [infiniteVertexGraphCover_restrict] at h
  exact h

end GaussianWave.BS.Lower
