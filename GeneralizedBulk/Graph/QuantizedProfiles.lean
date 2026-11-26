import GeneralizedBulk.Graph.RandomColoringEntropy
import GeneralizedBulk.Entropy.SoftEdgeBoundaryError

/-! The exact bridge from componentwise quantization to the finite graph
color profiles used by the common counting event. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration
open ColorProfiles Entropy

theorem graphNeighbor_sum {N d : ℕ} (G : RegularGraph N d) (f : Fin N → ℝ) :
    (∑ v,∑ j,f (graphNeighbor G v j)) = (d : ℝ)*∑ v,f v := by
  calc
    _ = ∑ z : Stub N d,f ((graphReferencePairing G).val z).1 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro j hj
      change f (graphNeighbor G v j) = f ((labelingPairing G (canonicalPortLabeling G)).val (v,j)).1
      rw [labelingPairing_root]
      rfl
    _ = ∑ z : Stub N d,f z.1 := Equiv.sum_comp (graphReferencePairing G).val (fun z : Stub N d => f z.1)
    _ = _ := by simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum]

theorem graphEdgeProfile_vertex_sum {N d q m : ℕ} (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m) (c : VertexColoring N q) (ab : Fin q × Fin q) :
    graphEdgeProfile G c ab = ((N*d : ℕ) : ℝ)⁻¹*
      ∑ v,∑ j : Fin d,if c v = ab.1 ∧ c (graphNeighbor G v j) = ab.2 then (1 : ℝ) else 0 := by
  change edgeMassOfStar (symmetrizedMass (histogram N (orderedStarWord (graphNeighbor G) c))) ab = _
  rw [← configurationEdgeMass_eq_star_marginal hN hd hNd]
  simp only [configurationEdgeMass,normalizedCounts,← hNd,wordEdgeCount_eq_vertex_sum,Nat.cast_sum,
    wordPortCount,Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    orderedStarWord,Fin.cases_zero,Fin.cases_succ]
  ring

variable {k N d q : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
  [MeasurableSpace B] [MeasurableSingletonClass B]

def edgeColorEquiv (e : (Fin k → B) ≃ Fin q) : (Fin k × Fin 2 → B) ≃ (Fin q × Fin q) where
  toFun w := (e (fun r => w (r,0)),e (fun r => w (r,1)))
  invFun ab := fun i => if i.2 = 0 then e.symm ab.1 i.1 else e.symm ab.2 i.1
  left_inv w := by
    funext i
    rcases i with ⟨r,j⟩
    fin_cases j <;> simp
  right_inv ab := by simp

def quantizedVertexColor (e : (Fin k → B) ≃ Fin q) (J : ℝ → B)
    (z : Fin k × Fin N → ℝ) (v : Fin N) : Fin q := e (fun r => J (z (r,v)))

theorem measurable_quantizedVertexColor (e : (Fin k → B) ≃ Fin q) (J : ℝ → B) (hJ : Measurable J)
    (a : Fin k × Fin N → ℝ) : Measurable (fun x => quantizedVertexColor e J (a+x)) := by
  apply measurable_pi_lambda
  intro v
  apply (measurable_of_finite e).comp
  apply measurable_pi_lambda
  intro r
  exact hJ.comp (by fun_prop)

theorem edgeColorEquiv_quantized (e : (Fin k → B) ≃ Fin q) (J : ℝ → B)
    (z : Fin k × Fin N → ℝ) (u v : Fin N) :
    edgeColorEquiv e (fun i => J (z (i.1,if i.2 = 0 then u else v))) =
      (quantizedVertexColor e J z u,quantizedVertexColor e J z v) := by
  simp [edgeColorEquiv,quantizedVertexColor]

set_option maxHeartbeats 1500000 in
theorem quantized_graphEdgeProfile_eq {m : ℕ} (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m)
    (e : (Fin k → B) ≃ Fin q) (J : ℝ → B) (a x : Fin k × Fin N → ℝ)
    (word : Fin k × Fin 2 → B) :
    graphEdgeProfile G (quantizedVertexColor e J (a+x)) (edgeColorEquiv e word) =
      quantizedHardEdgeAverage (graphNeighbor G) J a word x := by
  rw [graphEdgeProfile_vertex_sum G hN hd hNd]
  unfold quantizedHardEdgeAverage softEdgeAverage edgeLabelProduct
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro j hj
  change (if quantizedVertexColor e J (a+x) u = (edgeColorEquiv e word).1 ∧
      quantizedVertexColor e J (a+x) (graphNeighbor G u j) = (edgeColorEquiv e word).2 then (1 : ℝ) else 0) =
    hardWordProbability J (fun i => (a+x) (i.1,if i.2 = 0 then u else graphNeighbor G u j)) word
  rw [hardWordProbability_eq_dirac]
  have he : (word = (fun i => J ((a+x) (i.1,if i.2 = 0 then u else graphNeighbor G u j)))) ↔
      quantizedVertexColor e J (a+x) u = (edgeColorEquiv e word).1 ∧
        quantizedVertexColor e J (a+x) (graphNeighbor G u j) = (edgeColorEquiv e word).2 := by
    rw [← (edgeColorEquiv e).injective.eq_iff,edgeColorEquiv_quantized]
    constructor
    · intro h
      exact ⟨(congrArg Prod.fst h).symm,(congrArg Prod.snd h).symm⟩
    · intro h
      exact Prod.ext h.1.symm h.2.symm
  simp only [he]

end GeneralizedBulk.Graph.Configuration
