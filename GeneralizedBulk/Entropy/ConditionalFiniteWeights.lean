import GeneralizedBulk.Entropy.FiniteContinuity

/-! Actual conditional finite weights, including zero-mass fallback laws.
All mixture and normalization identities are exact at masses zero and one. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy

variable {S : Type*} [Fintype S]

def subsetWeightMass (weight : S → ℝ) (s : S → Prop) : ℝ := ∑ i,if s i then weight i else 0

def conditionalFiniteWeight (weight : S → ℝ) (s : S → Prop) (i : S) : ℝ :=
  if subsetWeightMass weight s = 0 then weight i else if s i then weight i/subsetWeightMass weight s else 0

theorem subsetWeightMass_nonneg (weight : S → ℝ) (hw : ∀ i,0 ≤ weight i) (s : S → Prop) :
    0 ≤ subsetWeightMass weight s := Finset.sum_nonneg (fun i hi => by split_ifs <;> simp [hw])

theorem subsetWeightMass_le_one (weight : S → ℝ) (hw : ∀ i,0 ≤ weight i)
    (hsum : ∑ i,weight i = 1) (s : S → Prop) : subsetWeightMass weight s ≤ 1 := by
  apply (Finset.sum_le_sum (fun i (hi : i ∈ Finset.univ) => show (if s i then weight i else 0) ≤ weight i by
    split_ifs <;> simp [hw])).trans_eq hsum

theorem subsetWeightMass_compl (weight : S → ℝ) (hsum : ∑ i,weight i = 1) (s : S → Prop) :
    subsetWeightMass weight (fun i => ¬ s i) = 1-subsetWeightMass weight s := by
  have he : subsetWeightMass weight (fun i => ¬ s i)+subsetWeightMass weight s = 1 := by
    rw [subsetWeightMass,subsetWeightMass,← Finset.sum_add_distrib,← hsum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hs : s i <;> simp [hs]
  linarith

theorem restricted_weight_zero_of_mass_zero (weight : S → ℝ) (hw : ∀ i,0 ≤ weight i)
    (s : S → Prop) (hz : subsetWeightMass weight s = 0) (i : S) : (if s i then weight i else 0) = 0 := by
  have h := Finite.vector_eq_zero_of_sum_zero (fun i => if s i then weight i else 0)
    (fun i => by dsimp only; split_ifs <;> simp [hw]) hz
  exact congrFun h i

theorem conditionalFiniteWeight_nonneg (weight : S → ℝ) (hw : ∀ i,0 ≤ weight i) (s : S → Prop) (i : S) :
    0 ≤ conditionalFiniteWeight weight s i := by
  unfold conditionalFiniteWeight
  split_ifs <;> first | exact hw i | exact div_nonneg (hw i) (subsetWeightMass_nonneg weight hw s) | rfl

theorem conditionalFiniteWeight_sum (weight : S → ℝ) (hw : ∀ i,0 ≤ weight i)
    (hsum : ∑ i,weight i = 1) (s : S → Prop) : (∑ i,conditionalFiniteWeight weight s i) = 1 := by
  by_cases hz : subsetWeightMass weight s = 0
  · simpa only [conditionalFiniteWeight,if_pos hz] using hsum
  · have he (i : S) : conditionalFiniteWeight weight s i = (if s i then weight i else 0)/subsetWeightMass weight s := by
      unfold conditionalFiniteWeight
      rw [if_neg hz]
      split_ifs <;> simp
    simp only [he,← Finset.sum_div]
    change subsetWeightMass weight s/subsetWeightMass weight s = 1
    exact div_self hz

theorem mass_mul_conditionalFiniteWeight (weight : S → ℝ) (hw : ∀ i,0 ≤ weight i)
    (s : S → Prop) (i : S) :
    subsetWeightMass weight s*conditionalFiniteWeight weight s i = if s i then weight i else 0 := by
  by_cases hz : subsetWeightMass weight s = 0
  · rw [hz,zero_mul,restricted_weight_zero_of_mass_zero weight hw s hz i]
  · unfold conditionalFiniteWeight
    rw [if_neg hz]
    split_ifs
    · field_simp
    · simp

theorem conditionalFiniteWeight_split (weight : S → ℝ) (hw : ∀ i,0 ≤ weight i)
    (hsum : ∑ i,weight i = 1) (bad : S → Prop) (i : S) :
    (1-subsetWeightMass weight bad)*conditionalFiniteWeight weight (fun i => ¬ bad i) i+
      subsetWeightMass weight bad*conditionalFiniteWeight weight bad i = weight i := by
  rw [← subsetWeightMass_compl weight hsum bad,mass_mul_conditionalFiniteWeight weight hw,
    mass_mul_conditionalFiniteWeight weight hw]
  by_cases hi : bad i <;> simp [hi]

def conditionalSubtypeWeight (weight : S → ℝ) (s : S → Prop) (i : {i : S // s i}) : ℝ :=
  weight i.val/subsetWeightMass weight s

theorem conditionalSubtypeWeight_nonneg (weight : S → ℝ) (hw : ∀ i,0 ≤ weight i) (s : S → Prop)
    (i : {i : S // s i}) : 0 ≤ conditionalSubtypeWeight weight s i :=
  div_nonneg (hw i.val) (subsetWeightMass_nonneg weight hw s)

theorem conditionalSubtypeWeight_sum (weight : S → ℝ) (s : S → Prop)
    (hs : subsetWeightMass weight s ≠ 0) : (∑ i,conditionalSubtypeWeight weight s i) = 1 := by
  unfold conditionalSubtypeWeight
  rw [← Finset.sum_div]
  have he : (∑ i : {i : S // s i},weight i.val) = subsetWeightMass weight s := by
    simpa only [tsum_fintype,Set.indicator,Set.mem_setOf_eq,subsetWeightMass] using
      tsum_subtype {i : S | s i} weight
  rw [he,div_self hs]

end GeneralizedBulk.Entropy
