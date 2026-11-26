import GaussianWave.BS.Reused.Graph.SymmetricProfileCount
import GaussianWave.BS.Reused.Graph.SymmetricEdgeMass

/-! The actual uniform symmetric-profile entropy bound for configurations. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Graph.Configuration
open ColorProfiles Entropy Entropy.Finite

def paletteLog (N d q : ℕ) : ℝ := (q^(d+1) : ℕ) * Real.log (N+1)

def symmetricProfileExponent {N d q m : ℕ} (C : ℝ) (S : StarWord d q → ℝ) : ℝ :=
  (N : ℝ)*entropy S - (m : ℝ)*entropy (edgeMassOfStar S) +
    ((q : ℝ)^2/2+2)*(C+Real.log (2*m+1))

theorem realizedProfiles_card_le_exp (N d q : ℕ) :
    (Fintype.card (realizedProfiles N d q) : ℝ) ≤ Real.exp (paletteLog N d q) := by
  by_cases hc : Fintype.card (realizedProfiles N d q) = 0
  · rw [hc,Nat.cast_zero]; exact le_of_lt (Real.exp_pos _)
  · exact (Real.log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hc)).mp
      (log_realizedProfiles_card_le N d q)

set_option maxHeartbeats 1000000 in
theorem symmetricColoringCount_le_exp {N d q m : ℕ}
    (C t : ℝ) (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m)
    (p : Pairing (Stub N d))
    (hgood : ∀ profile : realizedProfiles N d q,
      (configurationColoringCount (profileRepresentative profile) p : ℝ) ≤
        Real.exp (profileExponent (m := m) C (profileRepresentative profile)+paletteLog N d q+t))
    (S : StarWord d q → ℝ) :
    (configurationSymmetricColoringCount p S : ℝ) ≤
      Real.exp (symmetricProfileExponent (N := N) (m := m) C S+2*paletteLog N d q+t) := by
  have hc : (configurationSymmetricColoringCount p S : ℝ) ≤
      ∑ profile : SymmetricOrderedIndex N d q S,
        (configurationColoringCount (profileRepresentative profile.val) p : ℝ) := by
    exact_mod_cast symmetricColoringCount_le_sum p S
  have hi : (Fintype.card (SymmetricOrderedIndex N d q S) : ℝ) ≤ Real.exp (paletteLog N d q) := by
    apply le_trans _ (realizedProfiles_card_le_exp N d q)
    exact_mod_cast Fintype.card_le_of_injective
      (fun profile : SymmetricOrderedIndex N d q S => profile.val) Subtype.val_injective
  have hs (profile : SymmetricOrderedIndex N d q S) :
      (configurationColoringCount (profileRepresentative profile.val) p : ℝ) ≤
        Real.exp (symmetricProfileExponent (N := N) (m := m) C S+paletteLog N d q+t) := by
    apply (hgood profile.val).trans
    apply Real.exp_le_exp.mpr
    have h := profileExponent_le_symmetrized C hN hd hNd (profileRepresentative profile.val)
    rw [profileRepresentative_histogram,profile.property] at h
    exact add_le_add_right (add_le_add_right h _) _
  calc
    _ ≤ _ := hc
    _ ≤ ∑ _profile : SymmetricOrderedIndex N d q S,
        Real.exp (symmetricProfileExponent (N := N) (m := m) C S+paletteLog N d q+t) :=
      Finset.sum_le_sum (fun profile hprofile => hs profile)
    _ = (Fintype.card (SymmetricOrderedIndex N d q S) : ℝ) *
        Real.exp (symmetricProfileExponent (N := N) (m := m) C S+paletteLog N d q+t) := by simp
    _ ≤ Real.exp (paletteLog N d q) *
        Real.exp (symmetricProfileExponent (N := N) (m := m) C S+paletteLog N d q+t) :=
      mul_le_mul_of_nonneg_right hi (le_of_lt (Real.exp_pos _))
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

set_option maxHeartbeats 1000000 in
theorem configuration_uniform_symmetric_profile_probability {N d q m : ℕ}
    (C : ℝ) (hC : ∀ k : ℕ, |Real.log k.factorial-logFactorialMain k| ≤ C+Real.log (k+1))
    (hN : 0 < N) (hd : 0 < d) (hm : 0 < m) (hNd : N*d = 2*m) (t : ℝ) :
    (pairingLaw (Stub N d)).real {p | ∃ S : StarWord d q → ℝ,
      Real.exp (symmetricProfileExponent (N := N) (m := m) C S+2*paletteLog N d q+t) <
        configurationSymmetricColoringCount p S} ≤ Real.exp (-t) := by
  letI : Nonempty (Pairing (Stub N d)) := pairing_stub_nonempty hNd
  letI : IsProbabilityMeasure (pairingLaw (Stub N d)) := pairingLaw_isProbability _
  apply le_trans (measureReal_mono (μ := pairingLaw (Stub N d)) ?_)
    (configuration_uniform_profile_probability (q := q) C hC hN hm hNd t)
  rintro p ⟨S,hS⟩
  by_contra hn
  have hgood (profile : realizedProfiles N d q) :
      (configurationColoringCount (profileRepresentative profile) p : ℝ) ≤
        Real.exp (profileExponent (m := m) C (profileRepresentative profile)+paletteLog N d q+t) := by
    apply le_of_lt
    apply lt_of_not_ge
    intro h
    exact hn ⟨profile,h⟩
  exact not_lt_of_ge (symmetricColoringCount_le_exp C t hN hd hNd p hgood S) hS

end GaussianWave.BS.Reused.Graph.Configuration
