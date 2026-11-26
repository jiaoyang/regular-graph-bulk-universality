import GaussianWave.BS.Reused.Graph.SymmetricProfileUniform
import GaussianWave.BS.Reused.Graph.SymmetricGraphProfiles
import GaussianWave.BS.Reused.Graph.ConfigurationSimplicity

/-! Uniform symmetric-profile counting for the actual uniform labeled
simple regular graph, with an internally proved logarithmic simplicity cost. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Graph.Configuration
open ColorProfiles Entropy Entropy.Finite

def simplicityCost (N d M : ℕ) : ℝ := ((2*M+1 : ℕ) : ℝ)*Real.log ((N*d : ℕ)+1)

def GraphProfileGood {N d q m : ℕ} (C t : ℝ) (M : ℕ) (G : RegularGraph N d) : Prop :=
  ∀ S : StarWord d q → ℝ, (graphSymmetricColoringCount G S : ℝ) ≤
    Real.exp (symmetricProfileExponent (N := N) (m := m) C S+2*paletteLog N d q+t+simplicityCost N d M)

set_option maxHeartbeats 1000000 in
theorem regularGraph_uniform_symmetric_profile_probability {N d q m : ℕ}
    [Nonempty (RegularGraph N d)]
    (C : ℝ) (hC : ∀ k : ℕ, |Real.log k.factorial-logFactorialMain k| ≤ C+Real.log (k+1))
    (hN : 0 < N) (hd : 0 < d) (hm : 0 < m) (hNd : N*d = 2*m)
    (M : ℕ) (hL : 6 ≤ N*d) (hM : 8*d*(d+1) ≤ M) (hsize : 4*d*(d+1)+M < N*d) (t : ℝ) :
    (regularGraphLaw N d).real {G | ¬ GraphProfileGood (q := q) (m := m) C t M G} ≤ Real.exp (-t) := by
  letI : Nonempty (Pairing (Stub N d)) := pairing_stub_nonempty hNd
  letI : IsProbabilityMeasure (pairingLaw (Stub N d)) := pairingLaw_isProbability _
  let cost := simplicityCost N d M
  let F : Set (Pairing (Stub N d)) := {p | ∃ S : StarWord d q → ℝ,
    Real.exp (symmetricProfileExponent (N := N) (m := m) C S+2*paletteLog N d q+(t+cost)) <
      configurationSymmetricColoringCount p S}
  have hF : ∀ p (hp : SimpleConfiguration p),
      configurationGraph p hp ∈ {G | ¬ GraphProfileGood (q := q) (m := m) C t M G} → p ∈ F := by
    intro p hp hbad
    change ¬ (∀ S : StarWord d q → ℝ, _) at hbad
    obtain ⟨S,hS⟩ := not_forall.mp hbad
    refine ⟨S,?_⟩
    rw [← graphSymmetricColoringCount_configuration p hp S]
    apply lt_of_not_ge
    convert hS using 1 <;> congr 2 <;> dsimp [cost] <;> ring
  have hgraph := regularGraphLaw_real_event_le_pairing_event_div_simple N d _ F hF
  have hnum : (pairingLaw (Stub N d)).real F ≤ Real.exp (-(t+cost)) :=
    configuration_uniform_symmetric_profile_probability C hC hN hd hm hNd (t+cost)
  have hden : Real.exp (-cost) ≤ (pairingLaw (Stub N d)).real {p | SimpleConfiguration p} :=
    simplicity_probability_exp_lower_bound M hL hM hsize
  apply hgraph.trans
  calc
    _ ≤ Real.exp (-(t+cost)) / (pairingLaw (Stub N d)).real {p | SimpleConfiguration p} :=
      div_le_div_of_nonneg_right hnum (le_of_lt ((Real.exp_pos _).trans_le hden))
    _ ≤ Real.exp (-(t+cost)) / Real.exp (-cost) :=
      div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos _)) (Real.exp_pos _) hden
    _ = Real.exp (-t) := by rw [← Real.exp_sub]; congr 1; ring

end GaussianWave.BS.Reused.Graph.Configuration
