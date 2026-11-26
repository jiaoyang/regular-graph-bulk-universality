import GaussianWave.BS.Reused.Graph.EmpiricalSymmetry
import GaussianWave.BS.Reused.Graph.ProfileUniform
import GaussianWave.BS.Reused.Graph.ProfileSymmetryEntropy

/-! The directed edge marginal is preserved by neighbor-port symmetrization. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Graph.Configuration
open ColorProfiles Entropy Entropy.Finite

theorem wordPortCount_permutation {d q : ℕ} (π : Equiv.Perm (Fin d))
    (s : StarWord d q) (a b : Fin q) :
    wordPortCount (starWordPerm π s) a b = wordPortCount s a b := by
  unfold wordPortCount
  apply Finset.card_bij (fun j hj => π j)
  · intro j hj
    simpa [starWordPerm,neighborSlotPerm] using hj
  · intro j hj k hk he
    exact π.injective he
  · intro j hj
    refine ⟨π.symm j,?_,π.apply_symm_apply j⟩
    simpa [starWordPerm,neighborSlotPerm] using hj

theorem symmetrizedMass_port_average {N d q : ℕ} (p : CountProfile N d q) (a b : Fin q) :
    (∑ s : StarWord d q, symmetrizedMass p s * wordPortCount s a b) =
      ∑ s : StarWord d q, profileMass p s * wordPortCount s a b := by
  let K : ℝ := Fintype.card (Equiv.Perm (Fin d))
  have hK : K ≠ 0 := by dsimp [K]; exact_mod_cast Fintype.card_ne_zero
  have he (π : Equiv.Perm (Fin d)) :
      (∑ s : StarWord d q, profileMass p (starWordPerm π s) * wordPortCount s a b) =
        ∑ s : StarWord d q, profileMass p s * wordPortCount s a b := by
    calc
      _ = ∑ s : StarWord d q, profileMass p (starWordPerm π s) *
          wordPortCount (starWordPerm π s) a b := by simp_rw [wordPortCount_permutation]
      _ = _ := Equiv.sum_comp (starWordPerm π)
        (fun s => profileMass p s * wordPortCount s a b)
  simp only [symmetrizedMass,mul_assoc,Finset.sum_mul]
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change K⁻¹ * (K * _) = _
  rw [← mul_assoc,inv_mul_cancel₀ hK,one_mul]

def edgeMassOfStar {d q : ℕ} (S : StarWord d q → ℝ) (ab : Fin q × Fin q) : ℝ :=
  (d : ℝ)⁻¹ * ∑ s, S s * wordPortCount s ab.1 ab.2

theorem configurationEdgeMass_eq_star_marginal {N d q m : ℕ}
    (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m) (w : Fin N → StarWord d q) :
    configurationEdgeMass (m := m) w = edgeMassOfStar (d := d)
      (symmetrizedMass (histogram N w)) := by
  funext ab
  rw [edgeMassOfStar,symmetrizedMass_port_average]
  dsimp only [configurationEdgeMass,normalizedCounts]
  rw [← hNd,wordEdgeCount_eq_count_sum]
  simp only [profileMass_histogram,empiricalWordMass,Nat.cast_mul,Nat.cast_sum]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem profileExponent_le_symmetrized {N d q m : ℕ} (C : ℝ)
    (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m) (w : Fin N → StarWord d q) :
    profileExponent (m := m) C w ≤
      (N : ℝ) * entropy (symmetrizedMass (histogram N w)) -
        (m : ℝ) * entropy (edgeMassOfStar (symmetrizedMass (histogram N w))) +
          ((q : ℝ)^2/2+2)*(C+Real.log (2*m+1)) := by
  rw [profileExponent,configurationEdgeMass_eq_star_marginal hN hd hNd]
  have h := entropy_symmetrizedMass (histogram N w)
  have hpFun : profileMass (histogram N w) = empiricalWordMass w := funext (profileMass_histogram w)
  rw [hpFun] at h
  nlinarith [show (0 : ℝ) ≤ N by positivity]

end GaussianWave.BS.Reused.Graph.Configuration
