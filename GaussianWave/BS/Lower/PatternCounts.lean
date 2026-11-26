import GaussianWave.BS.Lower.RegularGraphEdges
import GaussianWave.BS.Reused.Graph.FiniteUniformIntegration

/-! Expected finite subgraph counts in the actual uniform simple regular
graph. This extends the protected-edge switching estimate to injective
labeled copies, in particular to short cycles. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
set_option maxHeartbeats 200000

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Graph

variable {m N d : ℕ}

/-- Mapping a graph along an injective vertex map preserves its edges,
including their actual finite number. -/
def mappedEdgeEquiv (H : SimpleGraph (Fin m)) (f : Fin m ↪ Fin N) :
    H.edgeSet ≃ (H.map f).edgeSet := by
  let g := SimpleGraph.Embedding.map f H
  refine Equiv.ofBijective g.mapEdgeSet ⟨g.mapEdgeSet.injective,?_⟩
  rintro ⟨⟨u,v⟩,he⟩
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj f H u v).mp he
  exact ⟨⟨s(x,y),hxy⟩,Subtype.ext rfl⟩

theorem mapped_edge_card (H : SimpleGraph (Fin m)) (f : Fin m ↪ Fin N) :
    (H.map f).edgeFinset.card = H.edgeFinset.card := by
  rw [SimpleGraph.edgeFinset_card,SimpleGraph.edgeFinset_card]
  exact (Fintype.card_congr (mappedEdgeEquiv H f)).symm

theorem mapped_edge_natCard (H : SimpleGraph (Fin m)) (f : Fin m ↪ Fin N) :
    Nat.card (H.map f).edgeSet = Nat.card H.edgeSet :=
  (Nat.card_congr (mappedEdgeEquiv H f)).symm

/-- Number of injective vertex embeddings whose entire pattern is present.
The real-valued definition makes finite expectation identities direct. -/
def patternCount (H : SimpleGraph (Fin m)) (G : RegularGraph N d) : ℝ :=
  ∑ f : Fin m ↪ Fin N,if H.map f ≤ G.val then 1 else 0

theorem patternCount_nonneg (H : SimpleGraph (Fin m)) (G : RegularGraph N d) :
    0 ≤ patternCount H G := by
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

/-- The expected count is the sum of the actual finite pattern-inclusion
probabilities. -/
theorem integral_patternCount_eq_sum [Nonempty (RegularGraph N d)]
    (H : SimpleGraph (Fin m)) :
    (∫ G,patternCount H G ∂regularGraphLaw N d) =
      ∑ f : Fin m ↪ Fin N,(regularGraphLaw N d).real {G | H.map f ≤ G.val} := by
  letI := regularGraphLaw_isProbability N d
  have hi (f : Fin m ↪ Fin N) :
      Integrable (fun G : RegularGraph N d => if H.map f ≤ G.val then (1 : ℝ) else 0)
        (regularGraphLaw N d) := by
    simpa only [Set.indicator,Set.mem_setOf_eq] using
      (integrable_const (1 : ℝ) (μ := regularGraphLaw N d)).indicator
        ((Set.toFinite {G | H.map f ≤ G.val}).measurableSet)
  simp only [patternCount]
  rw [integral_finset_sum _ (fun f _ => hi f)]
  apply Finset.sum_congr rfl
  intro f hf
  simpa only [Set.indicator,Set.mem_setOf_eq] using
    (integral_indicator_one (μ := regularGraphLaw N d)
      ((Set.toFinite {G | H.map f ≤ G.val}).measurableSet))

/-- Actual expected copies of an arbitrary fixed finite graph, proved from
the literal uniform-simple-graph law. -/
theorem integral_patternCount_le [Nonempty (RegularGraph N d)]
    (H : SimpleGraph (Fin m)) (hN : 0 < N) (hd : 0 < d)
    (hsize : 2*(4*d+2*d^2+2*(Nat.card H.edgeSet)) ≤ N*d) :
    (∫ G,patternCount H G ∂regularGraphLaw N d) ≤
      (N : ℝ)^m*(2*(d : ℝ)/(N : ℝ))^(Nat.card H.edgeSet) := by
  have hp (f : Fin m ↪ Fin N) :
      (regularGraphLaw N d).real {G | H.map f ≤ G.val} ≤
        (2*(d : ℝ)/(N : ℝ))^(Nat.card H.edgeSet) := by
    have hc := mapped_edge_natCard H f
    have hs : 2*(4*d+2*d^2+2*(Nat.card (H.map f).edgeSet)) ≤ N*d := by
      rw [hc]
      exact hsize
    have hprob := prescribed_graph_probability_natCard (N := N) (d := d) (H.map f) hN hd hs
    rw [hc] at hprob
    exact hprob
  rw [integral_patternCount_eq_sum]
  calc
    _ ≤ ∑ _f : Fin m ↪ Fin N,(2*(d : ℝ)/(N : ℝ))^(Nat.card H.edgeSet) :=
      Finset.sum_le_sum (fun f _ => hp f)
    _ = (Fintype.card (Fin m ↪ Fin N) : ℝ)*(2*(d : ℝ)/(N : ℝ))^(Nat.card H.edgeSet) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hc : Fintype.card (Fin m ↪ Fin N) ≤ N^m := by
        simpa only [Fintype.card_fun,Fintype.card_fin] using
          (Fintype.card_le_of_injective (fun f : Fin m ↪ Fin N => (f : Fin m → Fin N))
            Function.Embedding.coe_injective)
      exact_mod_cast hc

/-- A cycle of length at least three has exactly as many edges as vertices. -/
theorem cycleGraph_edge_card (n : ℕ) :
    (Nat.card (SimpleGraph.cycleGraph (n+3)).edgeSet) = n+3 := by
  have h := (SimpleGraph.cycleGraph (n+3)).sum_degrees_eq_twice_card_edges
  simp only [SimpleGraph.cycleGraph_degree_three_le,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,
    SimpleGraph.edgeFinset_card,Fintype.card_eq_nat_card] at h
  have hf : Nat.card (Fin (n+3)) = n+3 := by simp only [Nat.card_eq_fintype_card,Fintype.card_fin]
  rw [hf] at h
  omega

/-- Every fixed short-cycle length has a bounded expected number of actual
injective labeled copies, uniformly in the size of the simple regular graph. -/
theorem integral_cycleCount_le [Nonempty (RegularGraph N d)]
    (n : ℕ) (hN : 0 < N) (hd : 0 < d)
    (hsize : 2*(4*d+2*d^2+2*(n+3)) ≤ N*d) :
    (∫ G,patternCount (SimpleGraph.cycleGraph (n+3)) G ∂regularGraphLaw N d) ≤
      (2*(d : ℝ))^(n+3) := by
  have hs : 2*(4*d+2*d^2+2*(Nat.card (SimpleGraph.cycleGraph (n+3)).edgeSet)) ≤ N*d := by
    rw [cycleGraph_edge_card]
    exact hsize
  have h := integral_patternCount_le (SimpleGraph.cycleGraph (n+3)) hN hd hs
  rw [cycleGraph_edge_card] at h
  apply h.trans_eq
  rw [← mul_pow]
  congr 1
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp

end GaussianWave.BS.Lower
