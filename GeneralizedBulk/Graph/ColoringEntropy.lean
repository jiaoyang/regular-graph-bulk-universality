import GeneralizedBulk.Graph.ColorProfiles
import GeneralizedBulk.Entropy.FiniteShannon

/-! The literal coloring-to-profile Shannon inequality with its palette-size error. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.ColorProfiles
open Entropy.Finite

def symmetrizedProfileColor {N d q : ℕ} (neighbor : Fin N → Fin d → Fin N)
    (color : Fin N → Fin q) : symmetrizedProfiles N d q :=
  ⟨symmetrizedMass (orderedProfile neighbor color), symmetrizedProfile_mem neighbor color⟩

theorem symmetrizedProfiles_nonempty (N d q : ℕ) : (symmetrizedProfiles N d q).Nonempty := by
  let p : CountProfile N d q := fun _ => 0
  exact ⟨symmetrizedMass p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩⟩

theorem log_symmetrizedProfiles_card_le (N d q : ℕ) :
    Real.log (Fintype.card (symmetrizedProfiles N d q)) ≤
      (q ^ (d + 1) : ℕ) * Real.log (N + 1) := by
  have hc : 0 < (symmetrizedProfiles N d q).card := Finset.card_pos.mpr (symmetrizedProfiles_nonempty N d q)
  have h : Real.log ((symmetrizedProfiles N d q).card : ℝ) ≤
      Real.log (((N + 1) ^ (q ^ (d + 1)) : ℕ) : ℝ) := Real.log_le_log (by exact_mod_cast hc)
    (by exact_mod_cast symmetrizedProfiles_card_le N d q)
  rw [Fintype.card_coe]
  simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one] using h

theorem symmetrizedProfile_fiber_card {N d q : ℕ} (neighbor : Fin N → Fin d → Fin N)
    (p : symmetrizedProfiles N d q) :
    (Finset.univ.filter (fun color : Fin N → Fin q => symmetrizedProfileColor neighbor color = p)).card =
      symmetrizedColoringCount neighbor p.val := by
  congr 1
  ext color
  simp only [symmetrizedColoringCount, Finset.mem_filter, Finset.mem_univ, true_and,
    symmetrizedProfileColor, Subtype.ext_iff]

set_option maxHeartbeats 2000000 in
/-- For any finite coloring distribution, the whole coloring entropy is at
most the palette-dependent profile error plus the expected log number of
colorings with the realized symmetrized profile. -/
theorem coloring_entropy_profile_bound {N d q : ℕ} (neighbor : Fin N → Fin d → Fin N)
    (p : (Fin N → Fin q) → ℝ) (hp : ∀ color, 0 ≤ p color) (hsum : ∑ color, p color = 1) :
    entropy p ≤ (q ^ (d + 1) : ℕ) * Real.log (N + 1) +
      ∑ profile : symmetrizedProfiles N d q,
        pushMass (symmetrizedProfileColor neighbor) p profile *
          Real.log (symmetrizedColoringCount neighbor profile.val) := by
  apply (entropy_profile_support_bound (symmetrizedProfileColor neighbor) p hp hsum).trans
  apply add_le_add (log_symmetrizedProfiles_card_le N d q)
  apply Finset.sum_le_sum
  intro profile hprofile
  apply le_of_eq
  congr 2
  norm_cast
  unfold symmetrizedColoringCount
  congr 1
  ext color
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    symmetrizedProfileColor, Subtype.ext_iff]

end GeneralizedBulk.Graph.ColorProfiles
