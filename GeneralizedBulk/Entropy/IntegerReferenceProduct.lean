import GeneralizedBulk.Entropy.IntegerShannon

/-! The integer reference partition function factorizes exactly, giving an
entropy-energy constant that grows linearly with the number of coordinates. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy

def integerReferenceMass : ℝ := ∑' j : ℤ,Real.exp (-|(j : ℝ)|)

theorem integerReferenceMass_ge_one : 1 ≤ integerReferenceMass := by
  have h := summable_integer_exp_abs.le_tsum (0 : ℤ) (fun j hj => le_of_lt (Real.exp_pos _))
  simpa only [Int.cast_zero,abs_zero,neg_zero,Real.exp_zero,integerReferenceMass] using h

set_option maxHeartbeats 1000000 in
theorem integerEntropyConstant_eq_pow (m : ℕ) : integerEntropyConstant m = integerReferenceMass^m := by
  induction m with
  | zero =>
    letI : Fintype (Fin 0 → ℤ) := Fintype.ofSubsingleton 0
    simp [integerEntropyConstant,integerEnergy]
  | succ m ih =>
    let f : ℤ → ℝ := fun j => Real.exp (-|(j : ℝ)|)
    let g : (Fin m → ℤ) → ℝ := fun j => Real.exp (-integerEnergy j)
    have hp := summable_integer_exp_abs.mul_of_nonneg (summable_integer_reference m)
      (fun j => le_of_lt (Real.exp_pos _)) (fun j => le_of_lt (Real.exp_pos _))
    have hmul := summable_integer_exp_abs.tsum_mul_tsum (summable_integer_reference m) hp
    have he := (Fin.consEquiv (fun _ : Fin (m+1) => ℤ)).tsum_eq
      (fun j : Fin (m+1) → ℤ => Real.exp (-integerEnergy j))
    have hfun : (fun j : ℤ × (Fin m → ℤ) => Real.exp (-integerEnergy ((Fin.consEquiv (fun _ : Fin (m+1) => ℤ)) j))) =
        (fun j : ℤ × (Fin m → ℤ) => Real.exp (-|(j.1 : ℝ)|)*Real.exp (-integerEnergy j.2)) := by
      funext j
      simp only [integerEnergy,Fin.sum_univ_succ,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ,neg_add_rev,Real.exp_add]
      ring
    rw [hfun] at he
    change _ = integerEntropyConstant (m+1) at he
    rw [← he,← hmul]
    change integerReferenceMass*integerEntropyConstant m = integerReferenceMass^(m+1)
    rw [ih,pow_succ]
    ring

def linearIntegerEntropyConstant (m : ℕ) : ℝ := 1+(m : ℝ)*Real.log integerReferenceMass

theorem linearIntegerEntropyConstant_nonneg (m : ℕ) : 0 ≤ linearIntegerEntropyConstant m := by
  have hlog : 0 ≤ Real.log integerReferenceMass := Real.log_nonneg integerReferenceMass_ge_one
  unfold linearIntegerEntropyConstant
  positivity

theorem integer_normalized_reference_hasSum (m : ℕ) :
    HasSum (fun j : Fin m → ℤ => Real.exp (-(integerEnergy j+(m : ℝ)*Real.log integerReferenceMass))) 1 := by
  have hZ : 0 < integerReferenceMass := lt_of_lt_of_le zero_lt_one integerReferenceMass_ge_one
  have h := (summable_integer_reference m).hasSum.mul_left
    (Real.exp (-((m : ℝ)*Real.log integerReferenceMass)))
  have he : Real.exp (-((m : ℝ)*Real.log integerReferenceMass))*integerEntropyConstant m = 1 := by
    rw [integerEntropyConstant_eq_pow,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hZ]
    exact inv_mul_cancel₀ (pow_ne_zero m (ne_of_gt hZ))
  change HasSum _ (Real.exp (-((m : ℝ)*Real.log integerReferenceMass))*integerEntropyConstant m) at h
  rw [he] at h
  convert h using 1
  funext j
  rw [neg_add,Real.exp_add]
  ring

theorem integer_entropy_le_linear_first_moment {m : ℕ} (p : (Fin m → ℤ) → ℝ)
    (hp : ∀ j,0 ≤ p j) (hsum : HasSum p 1)
    (hmoment : Summable (fun j => p j*integerEnergy j)) :
    countableEntropy p ≤ linearIntegerEntropyConstant m+(∑' j,p j*integerEnergy j) := by
  let c := (m : ℝ)*Real.log integerReferenceMass
  have hs : Summable (fun j => p j*(integerEnergy j+c)) := by
    simp_rw [mul_add]
    exact hmoment.add (hsum.summable.mul_right c)
  have h := countableEntropy_le_reference_energy p (fun j => integerEnergy j+c) hp hsum hs
    (integer_normalized_reference_hasSum m).summable
  have href : (∑' j : Fin m → ℤ,Real.exp (-(integerEnergy j+c))) = 1 :=
    (integer_normalized_reference_hasSum m).tsum_eq
  rw [href] at h
  have he : (∑' j,p j*(integerEnergy j+c)) = (∑' j,p j*integerEnergy j)+c := by
    simp_rw [mul_add]
    rw [hmoment.tsum_add (hsum.summable.mul_right c),tsum_mul_right,hsum.tsum_eq,one_mul]
  rw [he] at h
  dsimp only [linearIntegerEntropyConstant,c] at h ⊢
  linarith

end GeneralizedBulk.Entropy
