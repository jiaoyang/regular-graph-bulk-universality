import GeneralizedBulk.Graph.ColorProfiles
import GeneralizedBulk.Graph.TypeClassEntropy

/-! Symmetrized empirical star profiles forget every vertex's port labeling. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.ColorProfiles

@[simp] theorem neighborSlotPerm_trans {d : ℕ} (π τ : Equiv.Perm (Fin d)) :
    neighborSlotPerm (π.trans τ) = (neighborSlotPerm π).trans (neighborSlotPerm τ) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [neighborSlotPerm]

@[simp] theorem neighborSlotPerm_symm {d : ℕ} (π : Equiv.Perm (Fin d)) :
    neighborSlotPerm π.symm = (neighborSlotPerm π).symm := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [neighborSlotPerm]

theorem starWordPerm_trans {d q : ℕ} (π τ : Equiv.Perm (Fin d)) (s : StarWord d q) :
    starWordPerm (π.trans τ) s = starWordPerm π (starWordPerm τ s) := by
  funext i
  simp [starWordPerm,Function.comp_def]

theorem starWordPerm_symm {d q : ℕ} (π : Equiv.Perm (Fin d)) :
    starWordPerm (q := q) π.symm = (starWordPerm π).symm := by
  ext s i
  simp [starWordPerm,Function.comp_def]

theorem profileMass_histogram {N d q : ℕ} (w : Fin N → StarWord d q) (s : StarWord d q) :
    profileMass (histogram N w) s = empiricalWordMass w s := by
  unfold profileMass histogram empiricalWordMass wordCount
  dsimp only
  congr 3
  ext v
  simp


theorem empiricalWordMass_vertex_sum {A : Type*} [Fintype A] [DecidableEq A]
    {N : ℕ} (w : Fin N → A) (a : A) :
    empiricalWordMass w a = (N : ℝ)⁻¹ * ∑ v, if w v = a then (1 : ℝ) else 0 := by
  simp only [empiricalWordMass,wordCount,Finset.card_eq_sum_ones,Finset.sum_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  ring

theorem symmetrizedMass_vertex_sum {N d q : ℕ} (w : Fin N → StarWord d q) (s : StarWord d q) :
    symmetrizedMass (histogram N w) s =
      (Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹ * (N : ℝ)⁻¹ *
        ∑ v, ∑ π : Equiv.Perm (Fin d), if w v = starWordPerm π s then (1 : ℝ) else 0 := by
  simp only [symmetrizedMass,profileMass_histogram,empiricalWordMass_vertex_sum]
  rw [← Finset.mul_sum,Finset.sum_comm]
  ring

def permLeftTranslate {d : ℕ} (τ : Equiv.Perm (Fin d)) :
    Equiv.Perm (Equiv.Perm (Fin d)) where
  toFun π := τ.symm.trans π
  invFun π := τ.trans π
  left_inv π := by ext j; simp [Equiv.trans_apply]
  right_inv π := by ext j; simp [Equiv.trans_apply]

theorem orbit_indicator_sum_invariant {d q : ℕ} (τ : Equiv.Perm (Fin d)) (w s : StarWord d q) :
    (∑ π : Equiv.Perm (Fin d), if starWordPerm τ w = starWordPerm π s then (1 : ℝ) else 0) =
      ∑ π : Equiv.Perm (Fin d), if w = starWordPerm π s then (1 : ℝ) else 0 := by
  have he (π : Equiv.Perm (Fin d)) : starWordPerm τ w = starWordPerm π s ↔
      w = starWordPerm (τ.symm.trans π) s := by
    rw [Equiv.apply_eq_iff_eq_symm_apply,← starWordPerm_symm,starWordPerm_trans]
  simp_rw [he]
  exact Equiv.sum_comp (permLeftTranslate τ)
    (fun π => if w = starWordPerm π s then (1 : ℝ) else 0)

theorem symmetrizedMass_local_port_invariant {N d q : ℕ}
    (w : Fin N → StarWord d q) (τ : Fin N → Equiv.Perm (Fin d)) :
    symmetrizedMass (histogram N (fun v => starWordPerm (τ v) (w v))) =
      symmetrizedMass (histogram N w) := by
  funext s
  rw [symmetrizedMass_vertex_sum,symmetrizedMass_vertex_sum]
  simp_rw [orbit_indicator_sum_invariant]

end GeneralizedBulk.Graph.ColorProfiles
