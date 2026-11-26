import Mathlib

/-! Combining proved full and marginal quadratic entropy errors. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy

theorem entropy_deficit_quadratic_error {C : Type*} [Fintype C]
    (E U r : ℝ) (Ei Vi ri : C → ℝ)
    (hfull : |E - (1 / 2 : ℝ) * U| ≤ r)
    (hmarginal : ∀ c, |Ei c - (1 / 2 : ℝ) * Vi c| ≤ ri c) :
    |(E - (1 / 2 : ℝ) * ∑ c, Ei c) -
      (1 / 2 : ℝ) * (U - (1 / 2 : ℝ) * ∑ c, Vi c)| ≤ r + (1 / 2 : ℝ) * ∑ c, ri c := by
  have he : (E - (1 / 2 : ℝ) * ∑ c, Ei c) -
      (1 / 2 : ℝ) * (U - (1 / 2 : ℝ) * ∑ c, Vi c) =
      (E - (1 / 2 : ℝ) * U) - (1 / 2 : ℝ) * ∑ c, (Ei c - (1 / 2 : ℝ) * Vi c) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [he]
  calc
    _ ≤ |E - (1 / 2 : ℝ) * U| + |(1 / 2 : ℝ) * ∑ c, (Ei c - (1 / 2 : ℝ) * Vi c)| := abs_sub _ _
    _ = |E - (1 / 2 : ℝ) * U| + (1 / 2 : ℝ) * |∑ c, (Ei c - (1 / 2 : ℝ) * Vi c)| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ r + (1 / 2 : ℝ) * ∑ c, |Ei c - (1 / 2 : ℝ) * Vi c| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      gcongr with c
      exact hmarginal c

end GeneralizedBulk.Entropy
