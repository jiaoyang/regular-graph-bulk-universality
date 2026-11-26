import GeneralizedBulk.Graph.ConfigurationProfiles
import GeneralizedBulk.Graph.ColoredPairingBound

/-! The actual configuration profile count with its entropy leading term. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration
open Entropy.Finite ColorProfiles

def edgeFactorialLog {N d q : ℕ} (w : Fin N → StarWord d q) : ℝ :=
  (1 / 2 : ℝ) * ∑ a : Fin q, ∑ b : Fin q, Real.log ((wordEdgeCount w a b).factorial)

theorem log_factorial_product {q : ℕ} (m : Fin q → Fin q → ℕ) :
    Real.log (∏ a : Fin q, ∏ b : Fin q, ((m a b).factorial : ℝ)) =
      ∑ a : Fin q, ∑ b : Fin q, Real.log ((m a b).factorial) := by
  rw [Real.log_prod _ _ (by intro a ha; exact ne_of_gt (Finset.prod_pos (fun b hb => by positivity)))]
  apply Finset.sum_congr rfl
  intro a ha
  exact Real.log_prod _ _ (fun b hb => by positivity)

theorem coloredPairing_card_le_exp {α : Type*} [Fintype α] [DecidableEq α]
    {f g : α → ℕ} (q : ℕ) (hf : ∀ x, f x < q) (hg : ∀ x, g x < q) :
    (Fintype.card (ColoredPairing f g) : ℝ) ≤ Real.exp ((1 / 2 : ℝ) *
      ∑ a : Fin q, ∑ b : Fin q, Real.log ((Fintype.card (ColorBlock f g a b)).factorial)) := by
  by_cases hc : Fintype.card (ColoredPairing f g) = 0
  · rw [hc, Nat.cast_zero]; exact le_of_lt (Real.exp_pos _)
  have hp : (0 : ℝ) < Fintype.card (ColoredPairing f g) := by exact_mod_cast Nat.pos_of_ne_zero hc
  have hsq : (Fintype.card (ColoredPairing f g) : ℝ) ^ 2 ≤
      ∏ a : Fin q, ∏ b : Fin q, ((Fintype.card (ColorBlock f g a b)).factorial : ℝ) := by
    exact_mod_cast coloredPairing_card_sq_le q hf hg
  have hlog := Real.log_le_log (sq_pos_of_pos hp) hsq
  rw [Real.log_pow, log_factorial_product] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  apply (Real.log_le_iff_le_exp hp).mp
  linarith

theorem edgeFactorialLog_of_typeClass {N d q : ℕ} {w z : Fin N → StarWord d q}
    (hz : z ∈ typeClass w) : edgeFactorialLog z = edgeFactorialLog w := by
  unfold edgeFactorialLog
  simp_rw [wordEdgeCount_of_typeClass hz]

set_option maxHeartbeats 1000000 in
theorem profileColorings_card_le_exp {N d q : ℕ} (hN : 0 < N) (w : Fin N → StarWord d q) :
    (Fintype.card (profileColorings w) : ℝ) ≤
      Real.exp ((N : ℝ) * entropy (empiricalWordMass w) + edgeFactorialLog w) := by
  have hc : (Fintype.card (profileColorings w) : ℝ) ≤
      ∑ z : {z : Fin N → StarWord d q // z ∈ typeClass w},
        (Fintype.card (ColoredPairing (wordSource z.val) (wordTarget z.val)) : ℝ) := by
    exact_mod_cast profileColorings_card_le w
  have hs : ∀ z : {z : Fin N → StarWord d q // z ∈ typeClass w},
      (Fintype.card (ColoredPairing (wordSource z.val) (wordTarget z.val)) : ℝ) ≤
        Real.exp (edgeFactorialLog w) := by
    intro z
    have h := coloredPairing_card_le_exp (f := wordSource z.val) (g := wordTarget z.val) q
      (fun h => (z.val h.1 0).isLt)
      (fun h => (z.val h.1 h.2.succ).isLt)
    change _ ≤ Real.exp (edgeFactorialLog z.val) at h
    rw [edgeFactorialLog_of_typeClass z.property] at h
    exact h
  calc
    _ ≤ _ := hc
    _ ≤ ∑ z : {z : Fin N → StarWord d q // z ∈ typeClass w}, Real.exp (edgeFactorialLog w) :=
      Finset.sum_le_sum (fun z hz => hs z)
    _ = (typeClass w).card * Real.exp (edgeFactorialLog w) := by simp
    _ ≤ Real.exp ((N : ℝ) * entropy (empiricalWordMass w)) * Real.exp (edgeFactorialLog w) := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
      exact (Real.log_le_iff_le_exp (by
        exact_mod_cast Finset.card_pos.mpr (show (typeClass w).Nonempty from ⟨w, by simp [typeClass]⟩))).mp
        (log_typeClass_card_le_entropy hN w)
    _ = _ := (Real.exp_add _ _).symm

end GeneralizedBulk.Graph.Configuration
