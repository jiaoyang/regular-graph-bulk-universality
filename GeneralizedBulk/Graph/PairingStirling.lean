import GeneralizedBulk.Graph.PairingFactorial
import GeneralizedBulk.Entropy.StirlingUniform

/-! Uniform logarithmic error for the actual configuration-model denominator. -/
noncomputable section

namespace GeneralizedBulk.Graph.Configuration
open GeneralizedBulk.Entropy

def logPairingMain (m : ℕ) : ℝ := (m : ℝ) * Real.log (2 * m : ℕ) - m

theorem factorialMain_pairing (m : ℕ) :
    logFactorialMain (2 * m) - (m : ℝ) * Real.log 2 - logFactorialMain m = logPairingMain m := by
  by_cases hm : m = 0
  · subst m; simp [logFactorialMain, logPairingMain]
  have hp : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hl : Real.log (2 * m : ℕ) = Real.log 2 + Real.log m := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (ne_of_gt hp)]
  dsimp [logFactorialMain, logPairingMain]
  rw [hl]
  push_cast
  ring

theorem exists_log_pairing_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ,
      |Real.log (pairingCount m) - logPairingMain m| ≤ C + 2 * Real.log (2 * m + 1) := by
  obtain ⟨C,hC,h⟩ := exists_log_factorial_error_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro m
  rw [log_pairingCount, ← factorialMain_pairing]
  have he : Real.log ((2 * m).factorial) - (m : ℝ) * Real.log 2 - Real.log m.factorial -
      (logFactorialMain (2 * m) - (m : ℝ) * Real.log 2 - logFactorialMain m) =
      (Real.log ((2 * m).factorial) - logFactorialMain (2 * m)) -
        (Real.log m.factorial - logFactorialMain m) := by ring
  rw [he]
  have hlog : Real.log (m + 1) ≤ Real.log (2 * m + 1) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show m + 1 ≤ 2 * m + 1 by omega))
  calc
    _ ≤ |Real.log ((2 * m).factorial) - logFactorialMain (2 * m)| +
        |Real.log m.factorial - logFactorialMain m| := abs_sub _ _
    _ ≤ (C + Real.log (2 * m + 1)) + (C + Real.log (m + 1))  := by
      have h1 := h (2 * m)
      have h2 := h m
      push_cast at h1 h2 ⊢
      exact add_le_add h1 h2
    _ ≤ _ := by linarith

end GeneralizedBulk.Graph.Configuration
