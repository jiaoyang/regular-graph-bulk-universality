import GeneralizedBulk.Graph.QuantizedProfiles
import GeneralizedBulk.Entropy.FiniteSampleMap

/-! Literal uniformly sampled stars and edges have exactly the mean color
profiles appearing in the common graph entropy inequality. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration
open ColorProfiles Entropy

def sampledStarWord {N d q : ℕ} (G : RegularGraph N d) (c : VertexColoring N q)
    (z : Fin N × Equiv.Perm (Fin d)) : StarWord d q :=
  (starWordPerm z.2).symm (orderedStarWord (graphNeighbor G) c z.1)

def sampledEdgeWord {N d q : ℕ} (G : RegularGraph N d) (c : VertexColoring N q)
    (z : Fin N × Fin d) : Fin q × Fin q := (c z.1,c (graphNeighbor G z.1 z.2))

theorem graphStarProfile_sample_average {N d q : ℕ} (G : RegularGraph N d) (c : VertexColoring N q)
    (s : StarWord d q) : graphStarProfile G c s =
      ∑ z : Fin N × Equiv.Perm (Fin d),uniformSampleWeight _ z*(if sampledStarWord G c z = s then 1 else 0) := by
  change symmetrizedMass (histogram N (orderedStarWord (graphNeighbor G) c)) s = _
  rw [symmetrizedMass_vertex_sum]
  simp only [uniformSampleWeight,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,mul_inv_rev,
    Fintype.sum_prod_type,← Finset.mul_sum,sampledStarWord,Equiv.symm_apply_eq]

theorem graphEdgeProfile_sample_average {N d q m : ℕ} (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m) (c : VertexColoring N q) (ab : Fin q × Fin q) :
    graphEdgeProfile G c ab =
      ∑ z : Fin N × Fin d,uniformSampleWeight _ z*(if sampledEdgeWord G c z = ab then 1 else 0) := by
  rw [graphEdgeProfile_vertex_sum G hN hd hNd]
  simp only [uniformSampleWeight,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,
    Fintype.sum_prod_type,← Finset.mul_sum,sampledEdgeWord,Prod.ext_iff]

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem mean_graphStarProfile_eq_sample_law {N d q : ℕ} (G : RegularGraph N d)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (c : Ω → VertexColoring N q) (hc : Measurable c) :
    meanProfile μ (fun x => graphStarProfile G (c x)) =
      lawMass (finiteSampleLaw μ (uniformSampleWeight (Fin N × Equiv.Perm (Fin d)))
        (fun z x => sampledStarWord G (c x) z)) id := by
  funext s
  have hm (z : Fin N × Equiv.Perm (Fin d)) : Measurable (fun x => sampledStarWord G (c x) z) :=
    (measurable_of_finite (fun v => sampledStarWord G v z)).comp hc
  have hi (z : Fin N × Equiv.Perm (Fin d)) : Integrable (fun x => if sampledStarWord G (c x) z = s then (1 : ℝ) else 0) μ := by
    convert (integrable_const (1 : ℝ) (μ := μ)).indicator (hm z (measurableSet_singleton s)) using 1
    funext x
    simp only [Set.indicator,Set.mem_preimage,Set.mem_singleton_iff]
  unfold meanProfile
  simp_rw [graphStarProfile_sample_average]
  rw [integral_finset_sum (f := fun z x => uniformSampleWeight _ z*(if sampledStarWord G (c x) z = s then 1 else 0))
    Finset.univ (fun z hz => (hi z).const_mul _)]
  rw [lawMass_finiteSampleLaw μ _ (uniformSampleWeight_nonneg _) _ hm id measurable_id]
  apply Finset.sum_congr rfl
  intro z hz
  rw [integral_const_mul]
  congr 1
  simpa only [Set.indicator,Set.mem_preimage,Set.mem_singleton_iff,Function.comp_id,Function.id_comp] using
    (integral_indicator_one (μ := μ) (hm z (measurableSet_singleton s)))

set_option maxHeartbeats 1000000 in
theorem mean_graphEdgeProfile_eq_sample_law {N d q m : ℕ} (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (c : Ω → VertexColoring N q) (hc : Measurable c) :
    meanProfile μ (fun x => graphEdgeProfile G (c x)) =
      lawMass (finiteSampleLaw μ (uniformSampleWeight (Fin N × Fin d))
        (fun z x => sampledEdgeWord G (c x) z)) id := by
  funext ab
  have hm (z : Fin N × Fin d) : Measurable (fun x => sampledEdgeWord G (c x) z) :=
    (measurable_of_finite (fun v => sampledEdgeWord G v z)).comp hc
  have hi (z : Fin N × Fin d) : Integrable (fun x => if sampledEdgeWord G (c x) z = ab then (1 : ℝ) else 0) μ := by
    convert (integrable_const (1 : ℝ) (μ := μ)).indicator (hm z (measurableSet_singleton ab)) using 1
    funext x
    simp only [Set.indicator,Set.mem_preimage,Set.mem_singleton_iff]
  unfold meanProfile
  simp_rw [graphEdgeProfile_sample_average G hN hd hNd]
  rw [integral_finset_sum (f := fun z x => uniformSampleWeight _ z*(if sampledEdgeWord G (c x) z = ab then 1 else 0))
    Finset.univ (fun z hz => (hi z).const_mul _)]
  rw [lawMass_finiteSampleLaw μ _ (uniformSampleWeight_nonneg _) _ hm id measurable_id]
  apply Finset.sum_congr rfl
  intro z hz
  rw [integral_const_mul]
  congr 1
  simpa only [Set.indicator,Set.mem_preimage,Set.mem_singleton_iff,Function.comp_id,Function.id_comp] using
    (integral_indicator_one (μ := μ) (hm z (measurableSet_singleton ab)))

end GeneralizedBulk.Graph.Configuration
