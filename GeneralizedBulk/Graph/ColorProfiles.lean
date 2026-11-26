import Mathlib

/-!
# Actual finite ordered and symmetrized color profiles

Profiles are literal histograms of star words. Their palette-dependent count
bound holds simultaneously for every neighbor array and coloring. This is the
deterministic combinatorial part of the common graph counting event.
-/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.ColorProfiles

abbrev StarWord (d q : ℕ) := Fin (d + 1) → Fin q
abbrev CountProfile (N d q : ℕ) := StarWord d q → Fin (N + 1)

def histogram {A : Type*} [Fintype A] (N : ℕ) (word : Fin N → A) : A → Fin (N + 1) :=
  fun a => ⟨(Finset.univ.filter (fun v => word v = a)).card,
    lt_of_le_of_lt (Finset.card_filter_le _ _) (by simp)⟩

theorem histogram_sum {A : Type*} [Fintype A] (N : ℕ) (word : Fin N → A) :
    (∑ a : A, (histogram N word a).val) = N := by
  have h := Finset.card_eq_sum_card_fiberwise (f := word)
    (s := (Finset.univ : Finset (Fin N))) (t := (Finset.univ : Finset A))
    (fun v hv => Finset.mem_univ _)
  simpa only [histogram, Finset.card_univ, Fintype.card_fin] using h.symm

theorem countProfile_card (N d q : ℕ) :
    Fintype.card (CountProfile N d q) = (N + 1) ^ (q ^ (d + 1)) := by
  simp only [CountProfile, StarWord, Fintype.card_fun, Fintype.card_fin]

def orderedStarWord {N d q : ℕ} (neighbor : Fin N → Fin d → Fin N)
    (color : Fin N → Fin q) (v : Fin N) : StarWord d q :=
  Fin.cases (color v) (fun j => color (neighbor v j))

def orderedProfile {N d q : ℕ} (neighbor : Fin N → Fin d → Fin N)
    (color : Fin N → Fin q) : CountProfile N d q := histogram N (orderedStarWord neighbor color)

theorem orderedProfile_sum {N d q : ℕ} (neighbor : Fin N → Fin d → Fin N)
    (color : Fin N → Fin q) : (∑ s : StarWord d q, (orderedProfile neighbor color s).val) = N :=
  histogram_sum N _

def profileMass {N d q : ℕ} (p : CountProfile N d q) (s : StarWord d q) : ℝ := (p s).val / (N : ℝ)

theorem profileMass_nonneg {N d q : ℕ} (p : CountProfile N d q) (s : StarWord d q) :
    0 ≤ profileMass p s := by unfold profileMass; positivity

theorem orderedProfile_mass_sum {N d q : ℕ} (hN : 0 < N)
    (neighbor : Fin N → Fin d → Fin N) (color : Fin N → Fin q) :
    (∑ s : StarWord d q, profileMass (orderedProfile neighbor color) s) = 1 := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  simp only [profileMass, ← Finset.sum_div, ← Nat.cast_sum, orderedProfile_sum]
  exact div_self hN0

def neighborSlotPerm {d : ℕ} (π : Equiv.Perm (Fin d)) : Equiv.Perm (Fin (d + 1)) where
  toFun := Fin.cases 0 (fun j => (π j).succ)
  invFun := Fin.cases 0 (fun j => (π.symm j).succ)
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

def starWordPerm {d q : ℕ} (π : Equiv.Perm (Fin d)) : Equiv.Perm (StarWord d q) where
  toFun s := s ∘ neighborSlotPerm π
  invFun s := s ∘ (neighborSlotPerm π).symm
  left_inv s := by funext i; simp
  right_inv s := by funext i; simp

def symmetrizedMass {N d q : ℕ} (p : CountProfile N d q) (s : StarWord d q) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹ * ∑ π : Equiv.Perm (Fin d), profileMass p (starWordPerm π s)

def symmetrizedProfiles (N d q : ℕ) : Finset (StarWord d q → ℝ) :=
  Finset.univ.image (fun p : CountProfile N d q => symmetrizedMass p)

/-- The number of symmetrized profiles is bounded by the number of ordered
integer count vectors, uniformly in every graph and coloring. -/
theorem symmetrizedProfiles_card_le (N d q : ℕ) :
    (symmetrizedProfiles N d q).card ≤ (N + 1) ^ (q ^ (d + 1)) := by
  exact (Finset.card_image_le).trans_eq (by rw [Finset.card_univ, countProfile_card])

theorem symmetrizedProfile_mem {N d q : ℕ} (neighbor : Fin N → Fin d → Fin N)
    (color : Fin N → Fin q) :
    symmetrizedMass (orderedProfile neighbor color) ∈ symmetrizedProfiles N d q :=
  Finset.mem_image.mpr ⟨orderedProfile neighbor color, Finset.mem_univ _, rfl⟩

def orderedColoringCount {N d q : ℕ} (neighbor : Fin N → Fin d → Fin N) (p : CountProfile N d q) : ℕ :=
  (Finset.univ.filter (fun color : Fin N → Fin q => orderedProfile neighbor color = p)).card

def symmetrizedColoringCount {N d q : ℕ} (neighbor : Fin N → Fin d → Fin N)
    (p : StarWord d q → ℝ) : ℕ :=
  (Finset.univ.filter (fun color : Fin N → Fin q => symmetrizedMass (orderedProfile neighbor color) = p)).card

end GeneralizedBulk.Graph.ColorProfiles
