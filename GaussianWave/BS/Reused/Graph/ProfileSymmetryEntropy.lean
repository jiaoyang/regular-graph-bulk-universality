import GaussianWave.BS.Reused.Graph.ColorProfiles
import GaussianWave.BS.Reused.Entropy.FiniteShannon

/-! Symmetrizing neighbor ports increases the literal finite star entropy. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Graph.ColorProfiles
open Entropy.Finite

theorem entropy_symmetrizedMass {N d q : ℕ} (p : CountProfile N d q) :
    entropy (profileMass p) ≤ entropy (symmetrizedMass p) := by
  let K : ℝ := Fintype.card (Equiv.Perm (Fin d))
  have hK : 0 < K := by dsimp [K]; exact_mod_cast Fintype.card_pos
  have hsum : (∑ _π : Equiv.Perm (Fin d), K⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (ne_of_gt hK)
  have h := entropy_concave_mixture (fun _π : Equiv.Perm (Fin d) => K⁻¹)
    (fun _ => inv_nonneg.mpr hK.le) hsum
    (fun π s => profileMass p (starWordPerm π s))
    (fun π s => profileMass_nonneg p _)
  have he (π : Equiv.Perm (Fin d)) :
      entropy (fun s => profileMass p (starWordPerm π s)) = entropy (profileMass p) :=
    entropy_equiv (profileMass p) (starWordPerm π)
  simp_rw [he] at h
  have hleft : (∑ _π : Equiv.Perm (Fin d), K⁻¹ * entropy (profileMass p)) = entropy (profileMass p) := by
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [hleft] at h
  convert h using 1
  congr 1
  funext s
  simp only [symmetrizedMass, ← Finset.mul_sum, K]

end GaussianWave.BS.Reused.Graph.ColorProfiles
