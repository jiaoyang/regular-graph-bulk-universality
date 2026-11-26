import GeneralizedBulk.Entropy.CountableShannon

/-! Actual exponential reference summability on finite integer vectors. -/
noncomputable section
open scoped BigOperators

namespace GeneralizedBulk.Entropy

def integerEnergy {m : ℕ} (j : Fin m → ℤ) : ℝ := ∑ i,|(j i : ℝ)|

theorem summable_integer_exp_abs : Summable (fun j : ℤ => Real.exp (-|(j : ℝ)|)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · convert Real.summable_exp_neg_nat using 1
    funext n
    simp only [Int.cast_natCast,abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  · convert Real.summable_exp_neg_nat using 1
    funext n
    simp only [Int.cast_neg,Int.cast_natCast,abs_neg,abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]

set_option maxHeartbeats 1000000 in
theorem summable_integer_reference (m : ℕ) : Summable (fun j : Fin m → ℤ => Real.exp (-integerEnergy j)) := by
  induction m with
  | zero =>
    letI : Fintype (Fin 0 → ℤ) := Fintype.ofSubsingleton 0
    exact Summable.of_finite
  | succ m ih =>
    have h := summable_integer_exp_abs.mul_of_nonneg ih
      (fun j => le_of_lt (Real.exp_pos _)) (fun j => le_of_lt (Real.exp_pos _))
    apply (Fin.consEquiv (fun _ : Fin (m+1) => ℤ)).summable_iff.mp
    convert h using 1
    funext j
    simp only [Function.comp_def,integerEnergy,Fin.sum_univ_succ,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ,
      neg_add_rev,Real.exp_add]
    ring

def integerEntropyConstant (m : ℕ) : ℝ := ∑' j : Fin m → ℤ,Real.exp (-integerEnergy j)

theorem integerEntropyConstant_nonneg (m : ℕ) : 0 ≤ integerEntropyConstant m :=
  tsum_nonneg (fun j => le_of_lt (Real.exp_pos _))

theorem summable_integer_entropy {m : ℕ} (p : (Fin m → ℤ) → ℝ)
    (hp : ∀ j,0 ≤ p j) (hsum : HasSum p 1)
    (hmoment : Summable (fun j => p j*integerEnergy j)) :
    Summable (fun j => Real.negMulLog (p j)) :=
  summable_entropy_of_reference_energy p integerEnergy hp hsum hmoment (summable_integer_reference m)

theorem integer_entropy_le_first_moment {m : ℕ} (p : (Fin m → ℤ) → ℝ)
    (hp : ∀ j,0 ≤ p j) (hsum : HasSum p 1)
    (hmoment : Summable (fun j => p j*integerEnergy j)) :
    countableEntropy p ≤ integerEntropyConstant m+(∑' j,p j*integerEnergy j) :=
  countableEntropy_le_reference_energy p integerEnergy hp hsum hmoment (summable_integer_reference m)

end GeneralizedBulk.Entropy
