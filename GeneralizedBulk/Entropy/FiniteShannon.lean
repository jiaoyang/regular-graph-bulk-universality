import Mathlib

/-!
# Finite Shannon entropy proved from concavity of `−x log x`

This module supplies the finite-mixture and coloring-to-profile support bounds
used by the graph counting argument. Entropies are literal finite sums; no
entropy comparison is assumed as an external probabilistic input.
-/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy.Finite

def entropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ := ∑ a, Real.negMulLog (p a)

theorem entropy_concave_mixture {ι α : Type*} [Fintype ι] [Fintype α]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (p : ι → α → ℝ) (hp : ∀ i a, 0 ≤ p i a) :
    (∑ i, w i * entropy (p i)) ≤ entropy (fun a => ∑ i, w i * p i a) := by
  calc
    _ = ∑ a : α, ∑ i : ι, w i * Real.negMulLog (p i a) := by
      simp only [entropy, Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.le_map_sum
        (t := Finset.univ) (w := w) (p := fun i => p i a)
        (fun i hi => hw i) hsum (fun i hi => hp i a)

theorem entropy_equiv {α : Type*} [Fintype α] (p : α → ℝ) (e : α ≃ α) :
    entropy (p ∘ e) = entropy p := Equiv.sum_comp e (fun a => Real.negMulLog (p a))

/-- The unnormalized finite support bound; its total mass may be zero. -/
theorem entropy_sum_bound {α : Type*} [Fintype α] (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    entropy p ≤ Real.negMulLog (∑ a, p a) + (∑ a, p a) * Real.log (Fintype.card α) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · letI := hα
    simp [entropy]
  · letI := hα
    let m : ℝ := Fintype.card α
    have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos
    have hm0 : m ≠ 0 := hm.ne'
    have hsumw : (∑ a : α, m⁻¹) = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ hm0
    have hj := Real.concaveOn_negMulLog.le_map_sum (t := (Finset.univ : Finset α))
      (w := fun _ => m⁻¹) (p := p) (fun a ha => inv_nonneg.mpr hm.le) hsumw (fun a ha => hp a)
    have hj' : m⁻¹ * entropy p ≤ Real.negMulLog (m⁻¹ * ∑ a, p a) := by
      simpa only [smul_eq_mul, ← Finset.mul_sum, entropy] using hj
    have hscaled := mul_le_mul_of_nonneg_left hj' hm.le
    have hleft : m * (m⁻¹ * entropy p) = entropy p := by rw [← mul_assoc, mul_inv_cancel₀ hm0, one_mul]
    have hright : m * Real.negMulLog (m⁻¹ * ∑ a, p a) =
        Real.negMulLog (∑ a, p a) + (∑ a, p a) * Real.log m := by
      rw [Real.negMulLog_mul]
      simp only [Real.negMulLog_def, Real.log_inv]
      field_simp
      ring
    rw [hleft, hright] at hscaled
    exact hscaled

theorem entropy_le_log_card {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) : entropy p ≤ Real.log (Fintype.card α) := by
  simpa only [hsum, Real.negMulLog_one, one_mul, zero_add] using entropy_sum_bound p hp

def pushMass {α β : Type*} [Fintype α] (f : α → β) (p : α → ℝ) (b : β) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a => f a = b), p a

theorem pushMass_nonneg {α β : Type*} [Fintype α] (f : α → β) (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (b : β) : 0 ≤ pushMass f p b :=
  Finset.sum_nonneg (fun a ha => hp a)

theorem pushMass_sum {α β : Type*} [Fintype α] [Fintype β] (f : α → β) (p : α → ℝ) :
    (∑ b, pushMass f p b) = ∑ a, p a := by
  exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := f) (fun a ha => Finset.mem_univ _) p

/-- Finite fiber support bounds prove the coloring/profile chain inequality
directly, including empty fibers and zero-mass profiles. -/
theorem entropy_partition_bound {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    entropy p ≤ entropy (pushMass f p) +
      ∑ b, pushMass f p b * Real.log (Finset.univ.filter (fun a => f a = b)).card := by
  have hfiber (b : β) :
      (∑ a ∈ Finset.univ.filter (fun a => f a = b), Real.negMulLog (p a)) ≤
        Real.negMulLog (pushMass f p b) +
          pushMass f p b * Real.log (Finset.univ.filter (fun a => f a = b)).card := by
    have h := entropy_sum_bound (fun a : (Finset.univ.filter (fun a => f a = b)) => p a.val)
      (fun a => hp a.val)
    simpa only [entropy, pushMass, Fintype.card_coe,
      Finset.sum_coe_sort (Finset.univ.filter (fun a => f a = b)) p,
      Finset.sum_coe_sort (Finset.univ.filter (fun a => f a = b)) (fun a => Real.negMulLog (p a))] using h
  calc
    _ = ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), Real.negMulLog (p a) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
        (g := f) (fun a ha => Finset.mem_univ _) (fun a => Real.negMulLog (p a))
    _ ≤ ∑ b, (Real.negMulLog (pushMass f p b) +
        pushMass f p b * Real.log (Finset.univ.filter (fun a => f a = b)).card) :=
      Finset.sum_le_sum (fun b hb => hfiber b)
    _ = _ := by rw [Finset.sum_add_distrib]; rfl

theorem entropy_profile_support_bound {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    entropy p ≤ Real.log (Fintype.card β) +
      ∑ b, pushMass f p b * Real.log (Finset.univ.filter (fun a => f a = b)).card := by
  have h := entropy_partition_bound f p hp
  have hq := entropy_le_log_card (pushMass f p) (pushMass_nonneg f p hp)
    ((pushMass_sum f p).trans hsum)
  linarith

end GeneralizedBulk.Entropy.Finite
