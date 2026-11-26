import GeneralizedBulk.Graph.OuterAveraged
import GeneralizedBulk.Graph.ComplexReciprocalRates
import GeneralizedBulk.Graph.ProposalQuadraticMean

/-!
# Exact centered near/remote/outer decomposition

The decomposition is proved for the physical independent endpoint proposal
law. Its deterministic mean and the constant eigenspace correction remain
exact; no limit identity is used in the finite algebra.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

/-- Every spectral multiplier has the literal quadratic endpoint expansion. -/
theorem spectralMultiplier_proposal_expansion (f : ℝ → ℂ) (i j : Fin 4)
    (s : ProposalSample (N n) d) :
    D.spectralMultiplier n ω f (D.proposalEndpoints n ω s i) (D.proposalEndpoints n ω s j) =
      ∑ k, ((N n : ℂ)⁻¹ * f (D.eigenvalue n ω k)) *
        (D.proposalQuadratic n ω k i j s : ℂ) := by
  have hN : (N n : ℂ)⁻¹ * (N n : ℂ) = 1 :=
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n)))
  unfold spectralMultiplier spectralCompression
  apply Finset.sum_congr rfl
  intro k hk
  simp only [proposalQuadratic, Complex.ofReal_mul, Complex.ofReal_natCast]
  symm
  calc
    _ = ((N n : ℂ)⁻¹ * (N n : ℂ)) * (f (D.eigenvalue n ω k) *
        (D.eigenvector n ω k (D.proposalEndpoints n ω s i) : ℂ) *
          (D.eigenvector n ω k (D.proposalEndpoints n ω s j) : ℂ)) := by ring
    _ = _ := by rw [hN, one_mul]

/-- Centering any genuine spectral compression is the finite sum of its
coefficients times the actual centered physical quadratic marks. -/
theorem centered_spectralMultiplier_proposal_expansion (hd : 0 < d)
    (f : ℝ → ℂ) (i j : Fin 4) (s : ProposalSample (N n) d) :
    D.spectralMultiplier n ω f (D.proposalEndpoints n ω s i) (D.proposalEndpoints n ω s j) -
      (∫ t, D.spectralMultiplier n ω f (D.proposalEndpoints n ω t i)
        (D.proposalEndpoints n ω t j) ∂uniformOrientedProposals (N n) d) =
      ∑ k, ((N n : ℂ)⁻¹ * f (D.eigenvalue n ω k)) *
        (D.centeredProposalQuadratic n ω k i j s : ℂ) := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0,D.size_pos n⟩,⟨0,hd⟩⟩⟩
  simp_rw [D.spectralMultiplier_proposal_expansion n ω f i j]
  have hi (k : Fin (N n)) : Integrable (fun t =>
      ((N n : ℂ)⁻¹ * f (D.eigenvalue n ω k)) *
        (D.proposalQuadratic n ω k i j t : ℂ)) (uniformOrientedProposals (N n) d) :=
    (integrable_finiteUniform_complex (fun t => (D.proposalQuadratic n ω k i j t : ℂ))).const_mul _
  rw [integral_finset_sum _ (fun k _ => hi k)]
  simp only [integral_const_mul, integral_complex_ofReal, centeredProposalQuadratic,
    Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib]

/-- The outer spectral compression centered by its actual finite mean is
exactly the complementary cutoff-weighted centered quadratic series. -/
theorem centered_outerProposalEntry_expansion (hd : 0 < d)
    (E gap : ℝ) (z : ℂ) (i j : Fin 4) (s : ProposalSample (N n) d) :
    D.outerProposalEntry n ω E gap z i j s -
      (∫ t, D.outerProposalEntry n ω E gap z i j t ∂uniformOrientedProposals (N n) d) =
      D.weightedCenteredPartialProposalResolvent n ω Finset.univ
        (fun k => 1 - outerCutoff E gap (D.eigenvalue n ω k)) z i j s := by
  simp_rw [outerProposalEntry]
  rw [D.centered_spectralMultiplier_proposal_expansion n ω hd]
  unfold weightedCenteredPartialProposalResolvent
  apply Finset.sum_congr rfl
  intro k hk
  simp only [outerComplexWeight, div_eq_mul_inv, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- The finite centered resolvent splits exactly into a near weighted sum,
a remote weighted sum, and the centered outer compression. -/
theorem centered_proposal_resolvent_cutoff_decomposition (hd : 0 < d)
    (near : Finset (Fin (N n))) (E gap : ℝ) (z : ℂ) (hz : z.im ≠ 0)
    (i j : Fin 4) (s : ProposalSample (N n) d) :
    D.resolvent n ω z (D.proposalEndpoints n ω s i) (D.proposalEndpoints n ω s j) -
      D.proposalMean n ω z i j =
      D.weightedCenteredPartialProposalResolvent n ω near
        (fun k => outerCutoff E gap (D.eigenvalue n ω k)) z i j s +
      D.weightedCenteredPartialProposalResolvent n ω nearᶜ
        (fun k => outerCutoff E gap (D.eigenvalue n ω k)) z i j s +
      (D.outerProposalEntry n ω E gap z i j s -
        ∫ t, D.outerProposalEntry n ω E gap z i j t ∂uniformOrientedProposals (N n) d) := by
  rw [D.centered_proposal_resolvent_expansion n ω hd z hz,
    D.centered_outerProposalEntry_expansion n ω hd E gap z i j s]
  unfold weightedCenteredPartialProposalResolvent
  rw [Finset.sum_add_sum_compl near]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Complex.ofReal_sub, Complex.ofReal_one]
  ring

end GeneralizedBulk.External.RegularSpectralData
