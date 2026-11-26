import GaussianWave.BS.Reused.Entropy.FiniteShannon
import GaussianWave.BS.Reused.Entropy.StirlingUniform
import GaussianWave.BS.Reused.Graph.PairingStirling

/-! The entropy exponent for arbitrary finite directed edge-type counts. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Entropy
open Finite Graph.Configuration

variable {A : Type*} [Fintype A]

def normalizedCounts (L : ℕ) (n : A → ℕ) (a : A) : ℝ := n a / L

theorem factorialMain_count_identity (L : ℕ) (hL : 0 < L) (k : ℕ) :
    logFactorialMain k = (k : ℝ) * Real.log L - k -
      (L : ℝ) * Real.negMulLog ((k : ℝ) / L) := by
  by_cases hk : k = 0
  · subst k; simp [logFactorialMain, Real.negMulLog]
  have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  rw [Real.negMulLog, Real.log_div (ne_of_gt hk') (ne_of_gt hL')]
  dsimp [logFactorialMain]
  field_simp
  ring

theorem sum_factorialMain_counts (L : ℕ) (hL : 0 < L) (n : A → ℕ) (hsum : ∑ a, n a = L) :
    (∑ a, logFactorialMain (n a)) =
      (L : ℝ) * Real.log L - L - (L : ℝ) * entropy (normalizedCounts L n) := by
  simp_rw [factorialMain_count_identity L hL]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Nat.cast_sum, hsum, entropy, normalizedCounts]

set_option maxHeartbeats 1000000 in
theorem sum_log_factorial_upper (C : ℝ)
    (hC : ∀ k : ℕ, |Real.log k.factorial - logFactorialMain k| ≤ C + Real.log (k + 1))
    (L : ℕ) (n : A → ℕ) (hn : ∀ a, n a ≤ L) :
    (∑ a, Real.log (n a).factorial) ≤ (∑ a, logFactorialMain (n a)) +
      Fintype.card A * (C + Real.log (L + 1)) := by
  calc
    _ ≤ ∑ a, (logFactorialMain (n a) + (C + Real.log (L + 1))) := by
      apply Finset.sum_le_sum
      intro a ha
      have h := (abs_le.mp (hC (n a))).2
      have hl : Real.log ((n a : ℝ) + 1) ≤ Real.log ((L : ℝ) + 1) :=
        Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (hn a) 1)
      linarith
    _ = _ := by simp [Finset.sum_add_distrib]; ring

theorem pairing_log_lower_of_factorial_error (C : ℝ)
    (hC : ∀ k : ℕ, |Real.log k.factorial - logFactorialMain k| ≤ C + Real.log (k + 1))
    (m : ℕ) :
    logPairingMain m - 2 * (C + Real.log (2 * m + 1)) ≤ Real.log (pairingCount m) := by
  have h1 := (abs_le.mp (hC (2 * m))).1
  have h2 := (abs_le.mp (hC m)).2
  have hl : Real.log ((m : ℝ) + 1) ≤ Real.log (2 * (m : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by nlinarith [show (0 : ℝ) ≤ m by positivity])
  rw [log_pairingCount, ← factorialMain_pairing]
  push_cast at h1 h2 ⊢
  linarith

theorem configuration_entropy_exponent_bound (C : ℝ)
    (hC : ∀ k : ℕ, |Real.log k.factorial - logFactorialMain k| ≤ C + Real.log (k + 1))
    (m : ℕ) (hm : 0 < m) (n : A → ℕ) (hsum : ∑ a, n a = 2 * m) :
    (1 / 2 : ℝ) * (∑ a, Real.log (n a).factorial) - Real.log (pairingCount m) ≤
      -(m : ℝ) * entropy (normalizedCounts (2 * m) n) +
        ((Fintype.card A : ℝ) / 2 + 2) * (C + Real.log (2 * m + 1)) := by
  have hn : ∀ a, n a ≤ 2 * m := by
    intro a
    rw [← hsum]
    exact Finset.single_le_sum (fun a ha => Nat.zero_le _) (Finset.mem_univ a)
  have hf := sum_log_factorial_upper C hC (2 * m) n hn
  have hp := pairing_log_lower_of_factorial_error C hC m
  rw [sum_factorialMain_counts (2 * m) (by positivity) n hsum] at hf
  dsimp [logPairingMain] at hp
  push_cast at hf hp ⊢
  nlinarith

end GaussianWave.BS.Reused.Entropy
