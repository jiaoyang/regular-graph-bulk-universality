import Mathlib

/-! Exact first- and two-position averages of uniform finite permutations. -/
noncomputable section
open scoped BigOperators

namespace GeneralizedBulk.Graph

theorem sum_perm_eval_eq {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (i j : α) :
    (∑ σ : Equiv.Perm α, f (σ i)) = ∑ σ : Equiv.Perm α, f (σ j) := by
  have h := Equiv.sum_comp (Equiv.mulRight (Equiv.swap i j))
    (fun σ : Equiv.Perm α => f (σ i))
  change (∑ σ : Equiv.Perm α, f ((σ * Equiv.swap i j) i)) = ∑ σ : Equiv.Perm α, f (σ i) at h
  simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using h.symm

theorem card_mul_sum_perm_eval {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (i : α) :
    (Fintype.card α : ℝ) * (∑ σ : Equiv.Perm α, f (σ i)) =
      (Fintype.card (Equiv.Perm α) : ℝ) * ∑ j, f j := by
  calc
    _ = ∑ j : α, ∑ σ : Equiv.Perm α, f (σ j) := by
      simp_rw [← sum_perm_eval_eq f i]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ σ : Equiv.Perm α, ∑ j : α, f (σ j) := Finset.sum_comm
    _ = ∑ σ : Equiv.Perm α, ∑ j : α, f j := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact Equiv.sum_comp σ f
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem sum_perm_eval {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → ℝ) (i : α) :
    (∑ σ : Equiv.Perm α, f (σ i)) =
      (Fintype.card (Equiv.Perm α) : ℝ) / Fintype.card α * ∑ j, f j := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h := card_mul_sum_perm_eval f i
  field_simp
  nlinarith only [h]

theorem exists_perm_pair {α : Type*} [DecidableEq α] (i j a b : α)
    (hij : i ≠ j) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm α, σ i = a ∧ σ j = b := by
  let τ := Equiv.swap i a
  have hτi : τ i = a := Equiv.swap_apply_left i a
  have hτj : τ j ≠ a := by
    intro h
    apply hij
    exact τ.injective (hτi.trans h.symm)
  refine ⟨Equiv.swap (τ j) b * τ, ?_, ?_⟩
  · change Equiv.swap (τ j) b (τ i) = a
    rw [hτi, Equiv.swap_apply_of_ne_of_ne hτj.symm hab]
  · change Equiv.swap (τ j) b (τ j) = b
    exact Equiv.swap_apply_left _ _

theorem sum_perm_pair_eq {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α → ℝ) (i j a b : α) (hij : i ≠ j) (hab : a ≠ b) :
    (∑ σ : Equiv.Perm α, f (σ i) (σ j)) =
      ∑ σ : Equiv.Perm α, f (σ a) (σ b) := by
  obtain ⟨τ, hτi, hτj⟩ := exists_perm_pair i j a b hij hab
  have h := Equiv.sum_comp (Equiv.mulRight τ)
    (fun σ : Equiv.Perm α => f (σ i) (σ j))
  change (∑ σ : Equiv.Perm α, f ((σ * τ) i) ((σ * τ) j)) =
    ∑ σ : Equiv.Perm α, f (σ i) (σ j) at h
  simpa only [Equiv.Perm.mul_apply, hτi, hτj] using h.symm

theorem sum_offdiagonal_const {α : Type*} [Fintype α] [DecidableEq α] (c : ℝ) :
    (∑ a : α, ∑ b : α, if a = b then 0 else c) =
      (Fintype.card α : ℝ) * (Fintype.card α - 1) * c := by
  have hi (a : α) : (∑ b : α, if a = b then 0 else c) = (Fintype.card α : ℝ) * c - c := by
    calc
      _ = ∑ b : α, (c - (if a = b then c else 0)) := by
        apply Finset.sum_congr rfl
        intro b hb
        split_ifs <;> simp
      _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp_rw [hi]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem card_mul_sum_perm_pair {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α → ℝ) (i j : α) (hij : i ≠ j) :
    ((Fintype.card α : ℝ) * (Fintype.card α - 1)) *
      (∑ σ : Equiv.Perm α, f (σ i) (σ j)) =
      (Fintype.card (Equiv.Perm α) : ℝ) *
        ∑ a : α, ∑ b : α, if a = b then 0 else f a b := by
  have heq (a b : α) :
      (if a = b then 0 else ∑ σ : Equiv.Perm α, f (σ i) (σ j)) =
        if a = b then 0 else ∑ σ : Equiv.Perm α, f (σ a) (σ b) := by
    by_cases hab : a = b
    · simp only [hab, ↓reduceIte]
    · simp only [hab, ↓reduceIte]
      exact sum_perm_pair_eq f i j a b hij hab
  have hcomm (a b : α) :
      (if a = b then 0 else ∑ σ : Equiv.Perm α, f (σ a) (σ b)) =
        ∑ σ : Equiv.Perm α, if a = b then 0 else f (σ a) (σ b) := by
    by_cases hab : a = b <;> simp only [hab, ↓reduceIte, Finset.sum_const_zero]
  have hinvariant (σ : Equiv.Perm α) :
      (∑ a : α, ∑ b : α, if a = b then 0 else f (σ a) (σ b)) =
        ∑ a : α, ∑ b : α, if a = b then 0 else f a b := by
    calc
      _ = ∑ a : α, ∑ b : α, if σ a = σ b then 0 else f (σ a) (σ b) := by
        simp only [σ.injective.eq_iff]
      _ = ∑ a : α, ∑ b : α, if σ a = b then 0 else f (σ a) b := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Equiv.sum_comp σ (fun b => if σ a = b then 0 else f (σ a) b)
      _ = _ := Equiv.sum_comp σ (fun a => ∑ b : α, if a = b then 0 else f a b)
  calc
    _ = ∑ a : α, ∑ b : α, if a = b then 0 else ∑ σ : Equiv.Perm α, f (σ i) (σ j) := by
      rw [sum_offdiagonal_const]
    _ = ∑ a : α, ∑ b : α, if a = b then 0 else ∑ σ : Equiv.Perm α, f (σ a) (σ b) := by
      simp_rw [heq]
    _ = ∑ a : α, ∑ b : α, ∑ σ : Equiv.Perm α, if a = b then 0 else f (σ a) (σ b) := by
      simp_rw [hcomm]
    _ = ∑ σ : Equiv.Perm α, ∑ a : α, ∑ b : α, if a = b then 0 else f (σ a) (σ b) := by
      calc
        _ = ∑ a : α, ∑ σ : Equiv.Perm α, ∑ b : α, if a = b then 0 else f (σ a) (σ b) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by simp_rw [hinvariant]; simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem sum_perm_pair {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 2 ≤ Fintype.card α) (f : α → α → ℝ) (i j : α) (hij : i ≠ j) :
    (∑ σ : Equiv.Perm α, f (σ i) (σ j)) =
      (Fintype.card (Equiv.Perm α) : ℝ) /
        ((Fintype.card α : ℝ) * (Fintype.card α - 1)) *
          ∑ a : α, ∑ b : α, if a = b then 0 else f a b := by
  have hc : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hcard
  have h0 : (Fintype.card α : ℝ) ≠ 0 := by linarith
  have h1 : (Fintype.card α : ℝ) - 1 ≠ 0 := by linarith
  have h := card_mul_sum_perm_pair f i j hij
  field_simp
  nlinarith only [h]

end GeneralizedBulk.Graph
