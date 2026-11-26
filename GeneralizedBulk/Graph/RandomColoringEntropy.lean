import GeneralizedBulk.Graph.GraphColoringEntropy
import GeneralizedBulk.Entropy.FiniteLawIntegral
import GeneralizedBulk.Entropy.ProfileEntropy

/-! The common graph-counting event controls every actual random coloring,
including colorings produced by one fully correlated Gaussian vector. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration
open ColorProfiles Entropy Entropy.Finite

def graphStarProfile {N d q : ℕ} (G : RegularGraph N d) (c : VertexColoring N q) : StarWord d q → ℝ :=
  symmetrizedMass (orderedProfile (graphNeighbor G) c)

def graphEdgeProfile {N d q : ℕ} (G : RegularGraph N d) (c : VertexColoring N q) : Fin q × Fin q → ℝ :=
  edgeMassOfStar (graphStarProfile G c)

theorem graphStarProfile_nonneg {N d q : ℕ} (G : RegularGraph N d) (c : VertexColoring N q)
    (s : StarWord d q) : 0 ≤ graphStarProfile G c s := by
  unfold graphStarProfile symmetrizedMass
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun π hπ => profileMass_nonneg _ _))

theorem graphStarProfile_sum {N d q : ℕ} (G : RegularGraph N d) (hN : 0 < N)
    (c : VertexColoring N q) : (∑ s,graphStarProfile G c s) = 1 := by
  have he (π : Equiv.Perm (Fin d)) :
      (∑ s,profileMass (orderedProfile (graphNeighbor G) c) (starWordPerm π s)) = 1 := by
    rw [Equiv.sum_comp]
    exact orderedProfile_mass_sum hN _ _
  unfold graphStarProfile symmetrizedMass
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

theorem sum_wordPortCount {d q : ℕ} (s : StarWord d q) :
    (∑ ab : Fin q × Fin q,(wordPortCount s ab.1 ab.2 : ℝ)) = d := by
  simp only [wordPortCount,Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero]
  rw [Finset.sum_comm]
  have he (j : Fin d) : (∑ ab : Fin q × Fin q,if s 0 = ab.1 ∧ s j.succ = ab.2 then (1 : ℝ) else 0) = 1 := by
    have he (ab : Fin q × Fin q) : (s 0 = ab.1 ∧ s j.succ = ab.2) ↔ (s 0,s j.succ) = ab := by
      constructor
      · intro h; exact Prod.ext h.1 h.2
      · intro h; exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩
    simp only [he]
    simp
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

theorem graphEdgeProfile_nonneg {N d q : ℕ} (G : RegularGraph N d) (c : VertexColoring N q)
    (ab : Fin q × Fin q) : 0 ≤ graphEdgeProfile G c ab := by
  unfold graphEdgeProfile edgeMassOfStar
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun s hs => mul_nonneg (graphStarProfile_nonneg G c s) (by positivity)))

theorem graphEdgeProfile_sum {N d q : ℕ} (G : RegularGraph N d) (hN : 0 < N) (hd : 0 < d)
    (c : VertexColoring N q) : (∑ ab,graphEdgeProfile G c ab) = 1 := by
  unfold graphEdgeProfile edgeMassOfStar
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp_rw [← Finset.mul_sum,sum_wordPortCount]
  rw [← Finset.sum_mul,graphStarProfile_sum G hN c,one_mul]
  exact inv_mul_cancel₀ (by positivity)

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1500000 in
theorem random_coloring_entropy_integral_bound {N d q m : ℕ} (G : RegularGraph N d)
    (C t : ℝ) (M : ℕ) (hG : GraphProfileGood (q := q) (m := m) C t M G)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (c : Ω → VertexColoring N q) (hc : Measurable c) :
    entropy (lawMass μ c) ≤
      (∫ x,symmetricProfileExponent (N := N) (m := m) C (graphStarProfile G (c x)) ∂μ)+
        3*paletteLog N d q+t+simplicityCost N d M := by
  let P := symmetrizedProfileColor (q := q) (graphNeighbor G)
  have hp := lawMass_nonneg μ c
  have hs : (∑ v,lawMass μ c v) = 1 := by
    simpa only [tsum_fintype] using (lawMass_hasSum μ c hc).tsum_eq
  have h := graph_coloring_entropy_bound G C t M hG (lawMass μ c) hp hs
  have he : (∑ profile : symmetrizedProfiles N d q,
      pushMass P (lawMass μ c) profile*symmetricProfileExponent (N := N) (m := m) C profile.val) =
      ∫ x,symmetricProfileExponent (N := N) (m := m) C (graphStarProfile G (c x)) ∂μ := by
    simp_rw [finite_pushMass_lawMass μ c hc P]
    exact finite_law_expectation μ (P ∘ c) ((measurable_of_finite P).comp hc) _
  rw [he] at h
  exact h

set_option maxHeartbeats 1500000 in
theorem random_coloring_entropy_mean_bound {N d q m : ℕ} (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (C t : ℝ) (M : ℕ)
    (hG : GraphProfileGood (q := q) (m := m) C t M G)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (c : Ω → VertexColoring N q) (hc : Measurable c) :
    entropy (lawMass μ c) ≤
      (N : ℝ)*entropy (meanProfile μ (fun x => graphStarProfile G (c x)))-
        (m : ℝ)*entropy (meanProfile μ (fun x => graphEdgeProfile G (c x)))+
        (m : ℝ)*(3+Real.log (q*q : ℕ))*
          Real.sqrt (∫ x,totalVariation (graphEdgeProfile G (c x))
            (meanProfile μ (fun x => graphEdgeProfile G (c x))) ∂μ)+
        ((q : ℝ)^2/2+2)*(C+Real.log (2*m+1))+
        3*paletteLog N d q+t+simplicityCost N d M := by
  let S := fun x => graphStarProfile G (c x)
  let E := fun x => graphEdgeProfile G (c x)
  have hSm (s) : Measurable (fun x => S x s) := (measurable_of_finite (fun v => graphStarProfile G v s)).comp hc
  have hEm (ab) : Measurable (fun x => E x ab) := (measurable_of_finite (fun v => graphEdgeProfile G v ab)).comp hc
  have hSp : ∀ x s,0 ≤ S x s := fun x s => graphStarProfile_nonneg G (c x) s
  have hEp : ∀ x ab,0 ≤ E x ab := fun x ab => graphEdgeProfile_nonneg G (c x) ab
  have hSs : ∀ x,∑ s,S x s = 1 := fun x => graphStarProfile_sum G hN (c x)
  have hEs : ∀ x,∑ ab,E x ab = 1 := fun x => graphEdgeProfile_sum G hN hd (c x)
  have hSi := integrable_profile_entropy μ S hSm hSp hSs
  have hEi := integrable_profile_entropy μ E hEm hEp hEs
  have hstar := integral_profile_entropy_le_mean μ S hSm hSp hSs
  have hedge := entropy_mean_sub_integral_le_holder μ E hEm hEp hEs
  simp only [Fintype.card_prod,Fintype.card_fin] at hedge
  have h := random_coloring_entropy_integral_bound G C t M hG μ c hc
  have hint : (∫ x,symmetricProfileExponent (N := N) (m := m) C (S x) ∂μ) =
      (N : ℝ)*(∫ x,entropy (S x) ∂μ)-(m : ℝ)*(∫ x,entropy (E x) ∂μ)+
        ((q : ℝ)^2/2+2)*(C+Real.log (2*m+1)) := by
    change (∫ x,(N : ℝ)*entropy (S x)-(m : ℝ)*entropy (E x)+_ ∂μ) = _
    have hiadd := integral_add ((hSi.const_mul (N : ℝ)).sub (hEi.const_mul (m : ℝ)))
      (integrable_const (((q : ℝ)^2/2+2)*(C+Real.log (2*m+1))))
    have hisub := integral_sub (hSi.const_mul (N : ℝ)) (hEi.const_mul (m : ℝ))
    simp only [Pi.add_apply,Pi.sub_apply] at hiadd hisub
    rw [hiadd,hisub,integral_const_mul,integral_const_mul,integral_const]
    simp only [measureReal_univ_eq_one,one_smul]
  change entropy (lawMass μ c) ≤ (∫ x,symmetricProfileExponent (N := N) (m := m) C (S x) ∂μ)+
    3*paletteLog N d q+t+simplicityCost N d M at h
  rw [hint] at h
  have hstar' := mul_le_mul_of_nonneg_left hstar (show (0 : ℝ) ≤ N by positivity)
  have hedge' := mul_le_mul_of_nonneg_left hedge (show (0 : ℝ) ≤ m by positivity)
  change entropy (lawMass μ c) ≤ _
  nlinarith

end GeneralizedBulk.Graph.Configuration
