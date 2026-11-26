import Mathlib

/-! Deterministic product sensitivity for bounded soft label probabilities. -/
noncomputable section
open scoped BigOperators

namespace GeneralizedBulk.Entropy

theorem abs_prod_sub_prod_le_sum {A : Type*} [Fintype A] (f g : A → ℝ)
    (hf0 : ∀ a,0 ≤ f a) (hf1 : ∀ a,f a ≤ 1)
    (hg0 : ∀ a,0 ≤ g a) (hg1 : ∀ a,g a ≤ 1) :
    |(∏ a,f a)-(∏ a,g a)| ≤ ∑ a,|f a-g a| := by
  classical
  have haux : ∀ s : Finset A, |(∏ a ∈ s,f a)-(∏ a ∈ s,g a)| ≤ ∑ a ∈ s,|f a-g a| := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.sum_insert ha]
      have hfp : |∏ i ∈ s,f i| ≤ 1 := by
        rw [abs_of_nonneg (Finset.prod_nonneg (fun i hi => hf0 i))]
        exact Finset.prod_le_one (fun i hi => hf0 i) (fun i hi => hf1 i)
      have hga : |g a| ≤ 1 := by rw [abs_of_nonneg (hg0 a)]; exact hg1 a
      calc
        _ = |(f a-g a)*(∏ i ∈ s,f i)+g a*((∏ i ∈ s,f i)-(∏ i ∈ s,g i))| := by congr 1; ring
        _ ≤ |f a-g a| *|∏ i ∈ s,f i| +|g a| *|(∏ i ∈ s,f i)-(∏ i ∈ s,g i)| := by
          simpa only [abs_mul] using abs_add ((f a-g a)*(∏ i ∈ s,f i))
            (g a*((∏ i ∈ s,f i)-(∏ i ∈ s,g i)))
        _ ≤ |f a-g a| *1+1*(∑ i ∈ s,|f i-g i|) := by
          apply add_le_add (mul_le_mul_of_nonneg_left hfp (abs_nonneg _))
          exact (mul_le_mul_of_nonneg_right hga (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left ih (by norm_num))
        _ = _ := by ring
  exact haux Finset.univ

end GeneralizedBulk.Entropy
