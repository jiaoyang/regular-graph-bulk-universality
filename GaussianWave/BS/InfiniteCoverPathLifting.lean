import GaussianWave.BS.InfiniteCoverSampling

/-! Actual neighbor-surjectivity and finite-path lifting for the constructed
infinite extension of a finite cover sampler. -/
noncomputable section
open scoped Classical
namespace GaussianWave.BS
open Reused.Graph Reused.Graph.Configuration

theorem infiniteVertexGraphCover_neighbor_surjective {N m : ℕ}
    (G : RegularGraph N (m+2)) (k : ℕ) (seed : VertexCoverSeed N m k)
    (v : RegularTreeVertex (m+2)) (y : Fin N)
    (hy : G.val.Adj (infiniteVertexGraphCover G k seed v) y) :
    ∃ w : RegularTreeVertex (m+2),(regularWordTree (m+2)).Adj v w ∧
      infiniteVertexGraphCover G k seed w = y := by
  let F := infiniteVertexGraphCover G k seed
  let h := infiniteVertexGraphHom G k seed
  let f : RegularTreeNeighborIndex (m+2) v → G.val.neighborSet (F v) := fun i =>
    ⟨F (regularTreeNeighbor v i),h.map_rel (regularTreeNeighbor_adj v i)⟩
  have hfi : Function.Injective f := by
    intro i j hij
    exact infiniteVertexGraphCover_neighbor_injective G k seed v (congrArg Subtype.val hij)
  have hc : Fintype.card (RegularTreeNeighborIndex (m+2) v) =
      Fintype.card (G.val.neighborSet (F v)) := by
    calc
      _ = m+2 := by cases v <;> simp [RegularTreeNeighborIndex,Nat.add_assoc]
      _ = _ := by
        simpa only [Fintype.card_fin,SimpleGraph.neighborSet] using
          Fintype.card_congr (canonicalPortLabeling G (F v))
  have hfs := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi,hc⟩).2
  obtain ⟨i,hi⟩ := hfs ⟨y,hy⟩
  exact ⟨regularTreeNeighbor v i,regularTreeNeighbor_adj v i,congrArg Subtype.val hi⟩

/-- Every finite adjacent sequence lifts from any chosen preimage of its
initial vertex. The proof constructs the lift one actual neighbor at a time. -/
theorem graphHom_lift_pathTuple {V W : Type*} {H : SimpleGraph V} {G : SimpleGraph W}
    (F : H →g G)
    (hsurj : ∀ v y,G.Adj (F v) y → ∃ w,H.Adj v w ∧ F w=y)
    (n : ℕ) (p : Fin (n+1) → W) (hp : ∀ j : Fin n,G.Adj (p j.castSucc) (p j.succ))
    (v : V) (hv : F v=p 0) :
    ∃ q : Fin (n+1) → V,q 0=v ∧ (∀ j : Fin n,H.Adj (q j.castSucc) (q j.succ)) ∧
      ∀ j,F (q j)=p j := by
  induction n generalizing v with
  | zero =>
    refine ⟨fun _ => v,rfl,fun j => Fin.elim0 j,?_⟩
    intro j
    have hj : j=0 := Fin.ext (by omega)
    simpa only [hj] using hv
  | succ n ih =>
    have hadj : G.Adj (F v) (p (1 : Fin (n+2))) := by
      rw [hv]
      exact hp 0
    obtain ⟨w,hw,hFw⟩ := hsurj v _ hadj
    let tail : Fin (n+1) → W := fun j => p j.succ
    have ht : ∀ j : Fin n,G.Adj (tail j.castSucc) (tail j.succ) := fun j => hp j.succ
    obtain ⟨q,hq0,hqadj,hqmap⟩ := ih tail ht w hFw
    refine ⟨Fin.cons v q,rfl,?_,?_⟩
    · intro j
      induction j using Fin.cases with
      | zero => simpa only [Fin.cons_zero,Fin.cons_succ,hq0] using hw
      | succ j => exact hqadj j
    · intro j
      induction j using Fin.cases with
      | zero => exact hv
      | succ j => exact hqmap j

end GaussianWave.BS
