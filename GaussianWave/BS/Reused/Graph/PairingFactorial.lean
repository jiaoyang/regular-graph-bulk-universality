import GaussianWave.BS.Reused.Graph.PairingRestriction

/-! Exact factorial conversion for the proved finite matching count. -/
noncomputable section
open scoped BigOperators

namespace GaussianWave.BS.Reused.Graph.Configuration

theorem pairingCount_pos (m : ℕ) : 0 < pairingCount m := by
  induction m with
  | zero => simp [pairingCount]
  | succ m ih => exact Nat.mul_pos (by omega) ih

theorem pairingCount_factorial (m : ℕ) :
    (2 ^ m * m.factorial) * pairingCount m = (2 * m).factorial := by
  induction m with
  | zero => simp [pairingCount]
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ, pow_succ,
      Nat.factorial_succ, pairingCount]
    calc
      _ = (2 * m + 1 + 1) * (2 * m + 1) *
          ((2 ^ m * m.factorial) * pairingCount m) := by ring
      _ = _ := by rw [ih]; ring

theorem log_pairingCount (m : ℕ) :
    Real.log (pairingCount m) = Real.log ((2 * m).factorial) -
      (m : ℝ) * Real.log 2 - Real.log (m.factorial) := by
  have hp : (0 : ℝ) < pairingCount m := by exact_mod_cast pairingCount_pos m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have he : ((2 : ℝ) ^ m * m.factorial) * pairingCount m = (2 * m).factorial := by
    exact_mod_cast pairingCount_factorial m
  have hlog := congrArg Real.log he
  rw [Real.log_mul (by positivity) (ne_of_gt hp),
    Real.log_mul (by positivity) (ne_of_gt hf), Real.log_pow] at hlog
  linarith

end GaussianWave.BS.Reused.Graph.Configuration
