import GeneralizedBulk.Graph.SpectralVariance
import GeneralizedBulk.Graph.ResolventMean
import GeneralizedBulk.Graph.ExteriorSwitching

/-!
# Actual centered quadratic proposal marks and finite resolvent variance

Every L² class below is constructed from the finite uniform proposal law.
The centered resolvent expansion is proved from the genuine spectral formula
and the exact unconditioned mean. Only the explicit quadratic-mark covariance
bounds remain as input to the resulting variance estimate.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

abbrev ProposalSample (N d : ℕ) := (Fin N × Fin d) × (Fin N × Fin d)

def proposalQuadratic (k : Fin (N n)) (i j : Fin 4) (s : ProposalSample (N n) d) : ℝ :=
  (N n : ℝ) * D.eigenvector n ω k (D.proposalEndpoints n ω s i) *
    D.eigenvector n ω k (D.proposalEndpoints n ω s j)

def centeredProposalQuadratic (k : Fin (N n)) (i j : Fin 4) (s : ProposalSample (N n) d) : ℝ :=
  D.proposalQuadratic n ω k i j s -
    ∫ t, D.proposalQuadratic n ω k i j t ∂uniformOrientedProposals (N n) d

theorem centeredProposalQuadratic_memLp_two (hd : 0 < d) (k : Fin (N n)) (i j : Fin 4) :
    MemLp (D.centeredProposalQuadratic n ω k i j) 2 (uniformOrientedProposals (N n) d) := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0, D.size_pos n⟩, ⟨0, hd⟩⟩⟩
  apply (memLp_two_iff_integrable_sq (measurable_of_finite _).aestronglyMeasurable).mpr
  exact integrable_finiteUniform_real _

def centeredProposalQuadraticLp (hd : 0 < d) (k : Fin (N n)) (i j : Fin 4) :
    Lp ℂ 2 (uniformOrientedProposals (N n) d) :=
  ((D.centeredProposalQuadratic_memLp_two n ω hd k i j).ofReal (K := ℂ)).toLp
    (fun s => (D.centeredProposalQuadratic n ω k i j s : ℂ))

theorem centeredProposalQuadraticLp_ae (hd : 0 < d) (k : Fin (N n)) (i j : Fin 4) :
    (D.centeredProposalQuadraticLp n ω hd k i j : ProposalSample (N n) d → ℂ)
      =ᵐ[uniformOrientedProposals (N n) d]
        (fun s => (D.centeredProposalQuadratic n ω k i j s : ℂ)) := MemLp.coeFn_toLp _

/-- The raw quadratic spectral sum is exactly the compressed finite resolvent. -/
theorem proposal_resolvent_spectral_expansion (z : ℂ) (hz : z.im ≠ 0) (i j : Fin 4)
    (s : ProposalSample (N n) d) :
    D.resolvent n ω z (D.proposalEndpoints n ω s i) (D.proposalEndpoints n ω s j) =
      ∑ k, ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹) *
        (D.proposalQuadratic n ω k i j s : ℂ) := by
  have hN : (N n : ℂ)⁻¹ * (N n : ℂ) = 1 :=
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (D.size_pos n)))
  rw [D.resolvent_entry n ω z hz]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [proposalQuadratic, Complex.ofReal_mul, Complex.ofReal_natCast]
  symm
  calc
    _ = ((N n : ℂ)⁻¹ * (N n : ℂ)) * (((D.eigenvalue n ω k : ℂ) - z)⁻¹ *
        (D.eigenvector n ω k (D.proposalEndpoints n ω s i) : ℂ) *
          (D.eigenvector n ω k (D.proposalEndpoints n ω s j) : ℂ)) := by ring
    _ = _ := by rw [hN, one_mul]

theorem proposalMean_spectral_expansion (hd : 0 < d) (z : ℂ) (hz : z.im ≠ 0) (i j : Fin 4) :
    D.proposalMean n ω z i j =
      ∑ k, ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹) *
        ((∫ s, D.proposalQuadratic n ω k i j s ∂uniformOrientedProposals (N n) d : ℝ) : ℂ) := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0, D.size_pos n⟩, ⟨0, hd⟩⟩⟩
  have hi (k : Fin (N n)) : Integrable (fun s =>
      ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹) *
        (D.proposalQuadratic n ω k i j s : ℂ)) (uniformOrientedProposals (N n) d) :=
    (integrable_finiteUniform_real (D.proposalQuadratic n ω k i j)).ofReal.const_mul _
  rw [← D.proposalMean_integral_entry n ω hd z i j]
  simp_rw [D.proposal_resolvent_spectral_expansion n ω z hz i j]
  rw [integral_finset_sum _ (fun k _ => hi k)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul, integral_complex_ofReal]

/-- Centering by the actual proposal mean commutes with the finite spectral
expansion. This identity is not supplied as a covariance or series premise. -/
theorem centered_proposal_resolvent_expansion (hd : 0 < d) (z : ℂ) (hz : z.im ≠ 0) (i j : Fin 4)
    (s : ProposalSample (N n) d) :
    D.resolvent n ω z (D.proposalEndpoints n ω s i) (D.proposalEndpoints n ω s j) -
      D.proposalMean n ω z i j =
      ∑ k, ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹) *
        (D.centeredProposalQuadratic n ω k i j s : ℂ) := by
  rw [D.proposal_resolvent_spectral_expansion n ω z hz i j,
    D.proposalMean_spectral_expansion n ω hd z hz i j]
  simp only [centeredProposalQuadratic, Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib]

/-- The actual centered compressed-resolvent entry has the stated variance
bound, from explicit finite quadratic covariance bounds and the proved Ward
identity. Its L² functions and centered expansion are constructed internally. -/
theorem proposal_resolvent_variance_le (hd : 0 < d) (C epsilon : ℝ) (i j : Fin 4)
    (hcov : ∀ k l, |∫ s, D.centeredProposalQuadratic n ω k i j s *
        D.centeredProposalQuadratic n ω l i j s ∂uniformOrientedProposals (N n) d| ≤
      C * (if k = l then 1 else 0) + epsilon)
    (z : ℂ) (hz : z.im ≠ 0) :
    (∫ s, ‖D.resolvent n ω z (D.proposalEndpoints n ω s i) (D.proposalEndpoints n ω s j) -
      D.proposalMean n ω z i j‖ ^ 2 ∂uniformOrientedProposals (N n) d) ≤
      C * ((D.scalarResolvent n ω z).im / ((N n : ℝ) * z.im)) +
        epsilon * (∑ k, ‖(N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹‖) ^ 2 := by
  have h := D.integral_centered_spectral_variance_le n ω (uniformOrientedProposals (N n) d)
    (fun k => D.centeredProposalQuadraticLp n ω hd k i j)
    (fun k => D.centeredProposalQuadratic n ω k i j) C epsilon
    (fun k => D.centeredProposalQuadraticLp_ae n ω hd k i j) hcov z hz
  simp_rw [← D.centered_proposal_resolvent_expansion n ω hd z hz i j] at h
  exact h

end GeneralizedBulk.External.RegularSpectralData
