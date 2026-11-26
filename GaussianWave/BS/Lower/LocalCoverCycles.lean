import GaussianWave.BS.Lower.ReducedCycle
import GaussianWave.BS.Lower.LocalCycleMass
import GaussianWave.BS.InfiniteCoverSampling

/-! A collision of a genuine locally injective cover in a finite-radius ball
forces one of the literal near-cycle copies counted by `LocalCycleMass`. -/
noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1200000

namespace GaussianWave.BS.Lower
open GaussianWave.BS GaussianWave.BS.Reused.Graph GaussianWave.BS.Reused.Graph.Configuration

section GeneralLocalCover
variable {T V : Type*} {H : SimpleGraph T} {K : SimpleGraph V}

/-- Graph homomorphisms do not increase the extended graph distance. -/
theorem graphHom_edist_le (F : H →g K) (u v : T) : K.edist (F u) (F v) ≤ H.edist u v := by
  change _ ≤ ⨅ p : H.Walk u v,(p.length : ℕ∞)
  apply le_iInf
  intro p
  exact (p.map F).edist_le.trans_eq (by rw [SimpleGraph.Walk.length_map])

/-- Local injectivity prevents immediate backtracking in the image of any
actual source path. -/
theorem local_cover_path_no_backtracking (F : H →g K)
    (hlocal : ∀ v,Set.InjOn F (H.neighborSet v)) {u v : T} (p : H.Walk u v) (hp : p.IsPath)
    (i : ℕ) (hi : i+2 ≤ p.length) : F (p.getVert i) ≠ F (p.getVert (i+2)) := by
  intro he
  have hleft : H.Adj (p.getVert (i+1)) (p.getVert i) := H.symm (p.adj_getVert_succ (by omega))
  have hright : H.Adj (p.getVert (i+1)) (p.getVert (i+2)) := by
    simpa only [Nat.add_assoc] using p.adj_getVert_succ (i := i+1) (by omega)
  have hpre := hlocal (p.getVert (i+1)) hleft hright he
  have hidx := hp.getVert_injOn (by change i ≤ p.length; omega) (by change i+2 ≤ p.length; omega) hpre
  omega

/-- Every vertex of a finite walk is within its total length of the start. -/
theorem walk_support_edist_le {u v w : T} (p : H.Walk u v) (hw : w ∈ p.support) :
    H.edist u w ≤ (p.length : ℕ∞) := by
  exact (p.takeUntil w hw).edist_le.trans (by exact_mod_cast p.length_takeUntil_le hw)

end GeneralLocalCover

/-- A local-cover collision anywhere in the radius-`R` source ball forces
an injective cycle of length at most `2R` within distance `R` of the image
root. The source need not be assumed to be a tree. -/
theorem local_cover_collision_near_short_cycle {T : Type*} (H : SimpleGraph T)
    {N d : ℕ} (G : RegularGraph N d) (F : H →g G.val)
    (hlocal : ∀ v,Set.InjOn F (H.neighborSet v)) (o x y : T) (R : ℕ)
    (hxy : x ≠ y) (hx : H.edist o x ≤ (R : ℕ∞)) (hy : H.edist o y ≤ (R : ℕ∞))
    (hcollision : F x = F y) :
    ∃ n : ℕ,n+3 ≤ 2*R ∧ NearPattern (SimpleGraph.cycleGraph (n+3)) G R (F o) := by
  obtain ⟨px,hpx⟩ := H.exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (by simp) hx)
  obtain ⟨py,hpy⟩ := H.exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (by simp) hy)
  have hpxlen : px.length ≤ R := by exact_mod_cast (hpx.trans_le hx)
  have hpylen : py.length ≤ R := by exact_mod_cast (hpy.trans_le hy)
  let q := px.reverse.append py
  let p := q.bypass
  have hp : p.IsPath := q.bypass_isPath
  have hplen : p.length ≤ 2*R := by
    calc
      _ ≤ q.length := q.length_bypass_le
      _ = px.length+py.length := by simp only [q,SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse]
      _ ≤ _ := by omega
  have hppos : 0 < p.length := Nat.pos_of_ne_zero
    (fun he => hxy (SimpleGraph.Walk.eq_of_length_eq_zero he))
  have hnear (j : ℕ) : G.val.edist (F (p.getVert j)) (F o) ≤ (R : ℕ∞) := by
    have hs : p.getVert j ∈ q.support := q.support_bypass_subset (p.getVert_mem_support j)
    have hdist : H.edist o (p.getVert j) ≤ (R : ℕ∞) := by
      rcases ((px.reverse).mem_support_append_iff py).mp hs with hleft | hright
      · have hmem : p.getVert j ∈ px.support := by
          simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hleft
        exact (walk_support_edist_le px hmem).trans (by exact_mod_cast hpxlen)
      · exact (walk_support_edist_le py hright).trans (by exact_mod_cast hpylen)
    rw [SimpleGraph.edist_comm]
    exact (graphHom_edist_le F o (p.getVert j)).trans hdist
  have hclosed : F (p.getVert 0) = F (p.getVert p.length) := by
    simpa only [SimpleGraph.Walk.getVert_zero,SimpleGraph.Walk.getVert_length] using hcollision
  obtain ⟨l,hl3,hlL,f,hfmap,hfrange⟩ := closed_nonbacktracking_chain_contains_cycle G.val
    (fun i => F (p.getVert i)) p.length hppos hclosed
    (fun i hi => F.map_adj (p.adj_getVert_succ hi))
    (fun i hi => local_cover_path_no_backtracking F hlocal p hp i hi)
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' hl3
  refine ⟨n,hlL.trans hplen,f,hfmap,⟨0,by omega⟩,?_⟩
  obtain ⟨j,hj,he⟩ := hfrange ⟨0,by omega⟩
  rw [he]
  exact hnear j

/-- Literal root distance in the word tree is bounded by the stored word
length; hence finite ball embeddings really lie in the stated graph ball. -/
theorem regularWordTree_edist_root_le_depth (d : ℕ) (v : RegularTreeVertex d) :
    (regularWordTree d).edist none v ≤ (regularTreeDepth v : ℕ∞) := by
  cases v with
  | none => simp [regularTreeDepth,SimpleGraph.edist_eq_zero_iff]
  | some aw =>
    rcases aw with ⟨a,w⟩
    induction w with
    | nil =>
      have h := (SimpleGraph.edist_eq_one_iff_adj).mpr (regularTreeNeighbor_adj none a)
      simpa only [regularTreeNeighbor,regularTreeDepth,List.length_nil,Nat.zero_add,Nat.cast_one] using h.le
    | cons b w ih =>
      have hstep : (regularWordTree d).edist (some (a,w)) (some (a,b::w)) = 1 :=
        (SimpleGraph.edist_eq_one_iff_adj).mpr (regularTreeNeighbor_adj (some (a,w)) (some b))
      calc
        _ ≤ (regularWordTree d).edist none (some (a,w))+
            (regularWordTree d).edist (some (a,w)) (some (a,b::w)) := SimpleGraph.edist_triangle
        _ ≤ (regularTreeDepth (some (a,w)) : ℕ∞)+1 := by rw [hstep]; exact add_le_add_right ih _
        _ = _ := by norm_num [regularTreeDepth,Nat.cast_add,add_assoc]

/-- Exact collision-to-cycle adapter for the actual finite cover sampler. -/
theorem finite_vertex_cover_collision_near_short_cycle {N m : ℕ}
    (G : RegularGraph N (m+2)) (k : ℕ) (seed : VertexCoverSeed N m k)
    (hcollision : ¬Function.Injective (vertexGraphCover G k seed)) :
    ∃ n : ℕ,n+3 ≤ 2*(k+1) ∧ NearPattern (SimpleGraph.cycleGraph (n+3)) G (k+1) seed.1 := by
  unfold Function.Injective at hcollision
  push_neg at hcollision
  obtain ⟨x,y,hF,hxy⟩ := hcollision
  let F := infiniteVertexGraphHom G k seed
  have hx : (regularWordTree (m+2)).edist none (vertexBallEmbedding (m+2) k x) ≤ (k+1 : ℕ∞) :=
    (regularWordTree_edist_root_le_depth (m+2) _).trans (by exact_mod_cast vertexBallEmbedding_depth (m+2) k x)
  have hy : (regularWordTree (m+2)).edist none (vertexBallEmbedding (m+2) k y) ≤ (k+1 : ℕ∞) :=
    (regularWordTree_edist_root_le_depth (m+2) _).trans (by exact_mod_cast vertexBallEmbedding_depth (m+2) k y)
  have hxy' : vertexBallEmbedding (m+2) k x ≠ vertexBallEmbedding (m+2) k y :=
    fun he => hxy (vertexBallEmbedding_injective (m+2) k he)
  have hF' : F (vertexBallEmbedding (m+2) k x) = F (vertexBallEmbedding (m+2) k y) := by
    change infiniteVertexGraphCover G k seed _ = infiniteVertexGraphCover G k seed _
    rw [infiniteVertexGraphCover_restrict,infiniteVertexGraphCover_restrict]
    exact hF
  exact local_cover_collision_near_short_cycle (regularWordTree (m+2)) G F
    (infiniteVertexGraphCover_local_injective G k seed) none _ _ (k+1) hxy' hx hy hF'

end GaussianWave.BS.Lower
