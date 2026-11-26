import Mathlib.Analysis.SpecialFunctions.Stirling

/-! A single logarithmic error bound for every factorial, including zero.
This is the uniform input needed when palette-cell counts can vanish. -/
noncomputable section
open scoped BigOperators

namespace GeneralizedBulk.Entropy

def logFactorialMain (n : ℕ) : ℝ := (n : ℝ) * Real.log n - n

theorem exists_log_factorial_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |Real.log (n.factorial) - logFactorialMain n| ≤ C + Real.log (n + 1) := by
  obtain ⟨c, hc⟩ := Stirling.log_stirlingSeq_bounded_by_constant
  let u := Real.log (Stirling.stirlingSeq 1)
  let C := |c| + |u| + |Real.log 2|
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro n
  cases n with
  | zero => simp [logFactorialMain]; dsimp [C]; positivity
  | succ n =>
    have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hu : Real.log (Stirling.stirlingSeq (n + 1)) ≤ u := by
      exact Stirling.log_stirlingSeq'_antitone (Nat.zero_le n)
    have hl := hc n
    have hseq : |Real.log (Stirling.stirlingSeq (n + 1))| ≤ |c| + |u| := by
      apply abs_le.mpr
      constructor
      · linarith [neg_abs_le c, abs_nonneg u]
      · linarith [le_abs_self u, abs_nonneg c]
    have he : Real.log ((n + 1).factorial) - logFactorialMain (n + 1) =
        Real.log (Stirling.stirlingSeq (n + 1)) +
          (1 / 2 : ℝ) * (Real.log 2 + Real.log (n + 1 : ℕ)) := by
      have hf := Stirling.log_stirlingSeq_formula (n + 1)
      rw [Real.log_div (ne_of_gt hn) (ne_of_gt (Real.exp_pos 1)), Real.log_exp,
        Real.log_mul (by norm_num) (ne_of_gt hn)] at hf
      dsimp [logFactorialMain]
      linarith
    have hln : 0 ≤ Real.log (n + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    have hln' : Real.log (n + 1 : ℕ) ≤ Real.log ((n + 1 : ℕ) + 1) :=
      Real.log_le_log hn (by norm_num)
    rw [he]
    calc
      _ ≤ |Real.log (Stirling.stirlingSeq (n + 1))| +
          |(1 / 2 : ℝ) * (Real.log 2 + Real.log (n + 1 : ℕ))| := abs_add _ _
      _ ≤ |c| + |u| + (1 / 2 : ℝ) * (|Real.log 2| + Real.log (n + 1 : ℕ)) := by
        apply add_le_add hseq
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact mul_le_mul_of_nonneg_left ((abs_add _ _).trans_eq
          (by rw [abs_of_nonneg hln])) (by norm_num)
      _ ≤ C + Real.log ((n + 1 : ℕ) + 1) := by
        dsimp [C]
        linarith [abs_nonneg (Real.log 2)]

end GeneralizedBulk.Entropy
