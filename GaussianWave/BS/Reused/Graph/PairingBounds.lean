import GaussianWave.BS.Reused.Graph.PairingFactorial

/-! Uniform counting bounds for arbitrary finite matching blocks. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Graph.Configuration

set_option maxHeartbeats 1000000 in
theorem pairing_fin_card_sq_le_factorial (n : ℕ) :
    Fintype.card (Pairing (Fin n)) ^ 2 ≤ n.factorial := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      have hc : Fintype.card (Pairing (Fin 0)) = 1 := by
        simpa only [Nat.mul_zero, pairingCount] using pairing_fin_card 0
      simp [hc]
    by_cases hp : Nonempty (Pairing (Fin n))
    · let p := Classical.choice hp
      let a : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
      let b : Fin n := p.val a
      have hab : a ≠ b := (p.property.2 a).symm
      have hn2 : 2 ≤ n := by
        have hcard : 2 ≤ Fintype.card (Fin n) := Fintype.card_le_of_injective
          (fun z : Fin 2 => if z = 0 then a else b) (by
            intro z w hzw
            fin_cases z <;> fin_cases w <;> simp_all)
        simpa using hcard
      have hrem : Fintype.card (Remainder a b) = n - 2 := by
        rw [remainder_card a b hab, Fintype.card_fin]
      have he := Fintype.card_congr (conjugateEquiv (Fintype.equivFinOfCardEq hrem))
      have hr := ih (n - 2) (by omega)
      rw [pairing_card_recursion a b hab, he, Fintype.card_fin, mul_pow]
      calc
        _ ≤ (n - 1) ^ 2 * (n - 2).factorial := Nat.mul_le_mul_left _ hr
        _ ≤ n * (n - 1) * (n - 2).factorial := by
          apply Nat.mul_le_mul_right
          simpa only [pow_two] using Nat.mul_le_mul_right (n - 1) (Nat.sub_le n 1)
        _ = n.factorial := by
          have hn' : n = (n - 2) + 2 := by omega
          conv_rhs => rw [hn', Nat.factorial_succ, Nat.factorial_succ]
          have h0 : n - 2 + 1 + 1 = n := by omega
          have h1 : n - 2 + 1 = n - 1 := by omega
          rw [h0, h1]
          ring
    · haveI : IsEmpty (Pairing (Fin n)) := not_nonempty_iff.mp hp
      simp

theorem pairing_card_sq_le_factorial (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card (Pairing α) ^ 2 ≤ (Fintype.card α).factorial := by
  have he := Fintype.card_congr (conjugateEquiv (Fintype.equivFin α))
  rw [he]
  exact pairing_fin_card_sq_le_factorial _

theorem equiv_card_le_factorial (α β : Type*) [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] :
    Fintype.card (α ≃ β) ≤ (Fintype.card α).factorial := by
  by_cases h : Nonempty (α ≃ β)
  · let e := Classical.choice h
    let E : (α ≃ β) ≃ Equiv.Perm α :=
      { toFun := fun f => f.trans e.symm
        invFun := fun f => f.trans e
        left_inv := by intro f; ext x; simp
        right_inv := by intro f; ext x; simp }
    rw [Fintype.card_congr E, Fintype.card_perm]
  · haveI : IsEmpty (α ≃ β) := not_nonempty_iff.mp h
    simp

theorem equiv_card_le_factorial_right (α β : Type*) [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] :
    Fintype.card (α ≃ β) ≤ (Fintype.card β).factorial := by
  by_cases h : Nonempty (α ≃ β)
  · let e := Classical.choice h
    exact (equiv_card_le_factorial α β).trans_eq (congrArg Nat.factorial (Fintype.card_congr e))
  · haveI : IsEmpty (α ≃ β) := not_nonempty_iff.mp h
    simp

end GaussianWave.BS.Reused.Graph.Configuration
