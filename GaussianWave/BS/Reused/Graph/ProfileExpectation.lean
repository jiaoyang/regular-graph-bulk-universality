import GaussianWave.BS.Reused.Graph.ProfileCountingBound
import GaussianWave.BS.Reused.Entropy.ConfigurationExponent
import GaussianWave.BS.Reused.Graph.FiniteUniformIntegration

/-! Expected actual profile-coloring counts under uniform configurations. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Graph.Configuration
open Entropy Entropy.Finite ColorProfiles

def configurationColoringCount {N d q : ℕ} (w : Fin N → StarWord d q)
    (p : Pairing (Stub N d)) : ℕ :=
  Fintype.card {c : VertexColoring N q // configurationWord p c ∈ typeClass w}

theorem configurationColoringCount_sum {N d q : ℕ} (w : Fin N → StarWord d q) :
    (∑ p : Pairing (Stub N d), configurationColoringCount w p) =
      Fintype.card (profileColorings w) := by
  have h := Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun p : Pairing (Stub N d) => fun c : VertexColoring N q => configurationWord p c ∈ typeClass w))
  rw [Fintype.card_sigma] at h
  exact h.symm

theorem integral_configurationColoringCount {N d q : ℕ} (w : Fin N → StarWord d q) :
    (∫ p, (configurationColoringCount w p : ℝ) ∂pairingLaw (Stub N d)) =
      (Fintype.card (Pairing (Stub N d)) : ℝ)⁻¹ * Fintype.card (profileColorings w) := by
  rw [pairingLaw, Graph.integral_finiteUniform, ← Nat.cast_sum, configurationColoringCount_sum]

theorem pairing_stub_card {N d m : ℕ} (hNd : N * d = 2 * m) :
    Fintype.card (Pairing (Stub N d)) = pairingCount m := by
  have hc : Fintype.card (Stub N d) = 2 * m := by simpa only [Fintype.card_prod, Fintype.card_fin] using hNd
  exact (Fintype.card_congr (conjugateEquiv (Fintype.equivFinOfCardEq hc))).trans (pairing_fin_card m)

theorem configurationColoringCount_expectation_le {N d q m : ℕ}
    (hN : 0 < N) (hNd : N * d = 2 * m) (w : Fin N → StarWord d q) :
    (∫ p, (configurationColoringCount w p : ℝ) ∂pairingLaw (Stub N d)) ≤
      Real.exp ((N : ℝ) * entropy (empiricalWordMass w) + edgeFactorialLog w -
        Real.log (pairingCount m)) := by
  rw [integral_configurationColoringCount, pairing_stub_card hNd]
  have hp : (0 : ℝ) < pairingCount m := by exact_mod_cast pairingCount_pos m
  calc
    _ ≤ (pairingCount m : ℝ)⁻¹ *
        Real.exp ((N : ℝ) * entropy (empiricalWordMass w) + edgeFactorialLog w) :=
      mul_le_mul_of_nonneg_left (profileColorings_card_le_exp hN w) (by positivity)
    _ = _ := by rw [Real.exp_sub, Real.exp_log hp]; ring

def configurationEdgeMass {N d q m : ℕ} (w : Fin N → StarWord d q) : Fin q × Fin q → ℝ :=
  normalizedCounts (2 * m) (fun ab : Fin q × Fin q => wordEdgeCount w ab.1 ab.2)

set_option maxHeartbeats 1000000 in
theorem configurationColoringCount_entropy_bound {N d q m : ℕ}
    (C : ℝ) (hC : ∀ k : ℕ, |Real.log k.factorial - logFactorialMain k| ≤ C + Real.log (k + 1))
    (hN : 0 < N) (hm : 0 < m) (hNd : N * d = 2 * m) (w : Fin N → StarWord d q) :
    (∫ p, (configurationColoringCount w p : ℝ) ∂pairingLaw (Stub N d)) ≤
      Real.exp ((N : ℝ) * entropy (empiricalWordMass w) -
        (m : ℝ) * entropy (configurationEdgeMass (m := m) w) +
          ((q : ℝ) ^ 2 / 2 + 2) * (C + Real.log (2 * m + 1))) := by
  apply (configurationColoringCount_expectation_le hN hNd w).trans
  apply Real.exp_le_exp.mpr
  have hsum : (∑ ab : Fin q × Fin q, wordEdgeCount w ab.1 ab.2) = 2 * m := by
    rw [Fintype.sum_prod_type, wordEdgeCount_sum, hNd]
  have h := configuration_entropy_exponent_bound C hC m hm
    (fun ab : Fin q × Fin q => wordEdgeCount w ab.1 ab.2) hsum
  simp only [Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at h
  change (1 / 2 : ℝ) * _ - _ ≤ -(m : ℝ) * entropy (configurationEdgeMass (m := m) w) + _ at h
  dsimp only [edgeFactorialLog]
  nlinarith

end GaussianWave.BS.Reused.Graph.Configuration
