import GaussianWave.BS.GaussianNoiseProjection

/-!
# Determinant weights of the descendant innovation blocks

The same branch determinant occurs once for each root branch in either
vertex or edge balls.  The cancellation of these repeated factors is exact.
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

def branchNoiseWeight (m : ℕ) (energy : ℝ) : (k : ℕ) → BranchInnovation (m + 1) k → ℝ
  | 0, j => Empty.elim j
  | k + 1, j => Sum.elim
      (fun _ => siblingVariance (m + 2) energy * (branchEnergyCoefficients (m + 1) energy k).1)
      (fun aj => branchNoiseWeight m energy k aj.2) j

theorem branchOrthoNoiseEnergy_eq_weighted_sum (m k : ℕ) (energy : ℝ)
    (z : BranchInnovation (m + 1) k → ℝ) :
    branchOrthoNoiseEnergy m energy k z = ∑ j, branchNoiseWeight m energy k j * z j ^ 2 := by
  induction k with
  | zero => simp [branchOrthoNoiseEnergy, BranchInnovation]
  | succ k ih =>
      change siblingVariance (m + 2) energy * (branchEnergyCoefficients (m + 1) energy k).1 *
        (∑ i : Fin m, z (Sum.inl i) ^ 2) +
        (∑ a, branchOrthoNoiseEnergy m energy k (fun j => z (Sum.inr (a, j)))) =
        ∑ j : Fin m ⊕ (Fin (m + 1) × BranchInnovation (m + 1) k),
          branchNoiseWeight m energy (k + 1) j * z j ^ 2
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, branchNoiseWeight,
        Sum.elim_inl, Sum.elim_inr, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      exact ih _

def branchNoiseDeterminant (m k : ℕ) (energy : ℝ) : ℝ :=
  ∏ j : BranchInnovation (m + 1) k, branchNoiseWeight m energy k j

@[simp] theorem branchNoiseDeterminant_zero (m : ℕ) (energy : ℝ) :
    branchNoiseDeterminant m 0 energy = 1 := by simp [branchNoiseDeterminant, BranchInnovation]

theorem branchNoiseDeterminant_succ (m k : ℕ) (energy : ℝ) :
    branchNoiseDeterminant m (k + 1) energy =
      (siblingVariance (m + 2) energy * (branchEnergyCoefficients (m + 1) energy k).1) ^ m *
        branchNoiseDeterminant m k energy ^ (m + 1) := by
  unfold branchNoiseDeterminant
  change (∏ j : Fin m ⊕ (Fin (m + 1) × BranchInnovation (m + 1) k), _) = _
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, branchNoiseWeight,
    Sum.elim_inl, Sum.elim_inr, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem branchEnergy_root_coefficient_ge_one (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) : 1 ≤ (branchEnergyCoefficients (m + 1) energy k).1 := by
  have h := branchMeanEnergy_eq_profile_sum m k energy he 1 0
  simp only [branchMeanEnergy, one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_one, mul_zero, add_zero] at h
  rw [h]
  have hs := Finset.single_le_sum
    (f := fun n => (m + 1 : ℝ) ^ n * (branchMeanA (m + 1) energy n) ^ 2)
    (s := Finset.range (k + 1)) (a := 0)
    (fun n _ => mul_nonneg (pow_nonneg (by positivity) n) (sq_nonneg _)) (by simp)
  simpa only [pow_zero, branchMeanA, one_pow, mul_one] using hs

theorem branchNoiseWeight_pos (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (j : BranchInnovation (m + 1) k) :
    0 < branchNoiseWeight m energy k j := by
  induction k with
  | zero => exact Empty.elim j
  | succ k ih =>
      cases j with
      | inl i =>
          apply mul_pos
          · exact siblingVariance_pos (m + 2) (by omega) energy (by
              simpa only [Nat.cast_add, Nat.cast_ofNat] using he)
          · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
              (branchEnergy_root_coefficient_ge_one m k energy he)
      | inr aj => exact ih aj.2

theorem branchNoiseDeterminant_pos (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) : 0 < branchNoiseDeterminant m k energy :=
  Finset.prod_pos (fun j _ => branchNoiseWeight_pos m k energy he j)

/-- Exact cancellation of the common descendant determinant multiplicities. -/
theorem branchNoiseDeterminant_log_balance (m k : ℕ) (energy : ℝ) :
    Real.log (branchNoiseDeterminant m k energy ^ (m + 2)) -
      (m + 2 : ℝ) / 2 * Real.log (branchNoiseDeterminant m k energy ^ 2) = 0 := by
  rw [Real.log_pow, Real.log_pow]
  push_cast
  ring

end GaussianWave.BS
