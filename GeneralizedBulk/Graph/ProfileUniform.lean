import GeneralizedBulk.Graph.ProfileExpectation
import GeneralizedBulk.Graph.ProfileMarkov

/-! A single configuration-model event controls every realized ordered
star profile and hence every coloring of the sampled graph. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration
open Entropy Entropy.Finite ColorProfiles

def realizedProfiles (N d q : ℕ) : Finset (CountProfile N d q) :=
  Finset.univ.image (fun w : Fin N → StarWord d q => histogram N w)

def profileRepresentative {N d q : ℕ} (p : realizedProfiles N d q) : Fin N → StarWord d q :=
  Classical.choose (Finset.mem_image.mp p.property)

theorem profileRepresentative_histogram {N d q : ℕ} (p : realizedProfiles N d q) :
    histogram N (profileRepresentative p) = p.val :=
  (Classical.choose_spec (Finset.mem_image.mp p.property)).2

theorem realizedProfiles_card_le (N d q : ℕ) :
    Fintype.card (realizedProfiles N d q) ≤ (N + 1) ^ (q ^ (d + 1)) := by
  rw [Fintype.card_coe, ← countProfile_card]
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_univ)

theorem log_realizedProfiles_card_le (N d q : ℕ) :
    Real.log (Fintype.card (realizedProfiles N d q)) ≤
      (q ^ (d + 1) : ℕ) * Real.log (N + 1) := by
  by_cases hc : Fintype.card (realizedProfiles N d q) = 0
  · rw [hc, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)))
  · have hp : (0 : ℝ) < Fintype.card (realizedProfiles N d q) := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    have hle : (Fintype.card (realizedProfiles N d q) : ℝ) ≤
        (((N + 1) ^ (q ^ (d + 1)) : ℕ) : ℝ) := by exact_mod_cast realizedProfiles_card_le N d q
    have h := Real.log_le_log hp hle
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one] using h

theorem pairing_stub_nonempty {N d m : ℕ} (hNd : N * d = 2 * m) :
    Nonempty (Pairing (Stub N d)) := by
  have hc : Fintype.card (Stub N d) = 2 * m := by simpa only [Fintype.card_prod, Fintype.card_fin] using hNd
  exact ⟨conjugate (Fintype.equivFinOfCardEq hc).symm (canonicalPairing m)⟩

theorem integrable_pairingLaw_real {α : Type*} [Fintype α] [Nonempty (Pairing α)]
    (f : Pairing α → ℝ) : Integrable f (pairingLaw α) := by
  apply (integrable_finset_sum_measure.mpr (fun _ _ => integrable_dirac)).smul_measure
  exact ENNReal.inv_ne_top.mpr (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Pairing α) ≠ 0))

def profileExponent {N d q m : ℕ} (C : ℝ) (w : Fin N → StarWord d q) : ℝ :=
  (N : ℝ) * entropy (empiricalWordMass w) -
    (m : ℝ) * entropy (configurationEdgeMass (m := m) w) +
      ((q : ℝ) ^ 2 / 2 + 2) * (C + Real.log (2 * m + 1))

set_option maxHeartbeats 1000000 in
theorem configuration_uniform_profile_probability {N d q m : ℕ}
    (C : ℝ) (hC : ∀ k : ℕ, |Real.log k.factorial - logFactorialMain k| ≤ C + Real.log (k + 1))
    (hN : 0 < N) (hm : 0 < m) (hNd : N * d = 2 * m) (t : ℝ) :
    (pairingLaw (Stub N d)).real {p | ∃ profile : realizedProfiles N d q,
      Real.exp (profileExponent (m := m) C (profileRepresentative profile) +
        (q ^ (d + 1) : ℕ) * Real.log (N + 1) + t) ≤
          configurationColoringCount (profileRepresentative profile) p} ≤ Real.exp (-t) := by
  letI : Nonempty (Pairing (Stub N d)) := pairing_stub_nonempty hNd
  letI : IsProbabilityMeasure (pairingLaw (Stub N d)) := pairingLaw_isProbability _
  apply uniform_profile_markov (pairingLaw (Stub N d))
    (fun profile : realizedProfiles N d q => fun p => (configurationColoringCount (profileRepresentative profile) p : ℝ))
    (fun profile => integrable_pairingLaw_real _)
    (fun profile p => by positivity)
    (fun profile => profileExponent (m := m) C (profileRepresentative profile))
    (fun profile => configurationColoringCount_entropy_bound C hC hN hm hNd _)
    _ t (log_realizedProfiles_card_le N d q)

end GeneralizedBulk.Graph.Configuration
