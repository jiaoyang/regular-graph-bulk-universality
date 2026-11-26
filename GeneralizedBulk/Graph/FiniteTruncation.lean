import GeneralizedBulk.Graph.CenteredCutoff

/-!
# Exact finite truncation and its two analytic errors

A cutoff supported in a fixed bulk window separates the covariance-controlled
remote channels from the outer compression. The retained finite marks are
centered by their actual finite Gaussian covariance parameter lambda/d.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def bulkRemoteEigenvalues (near : Finset (Fin (N n))) (E gap : ℝ) : Finset (Fin (N n)) :=
  nearᶜ ∩ D.eigenvalueWindow n ω E (2 * gap)

/-- The weighted remote sum is supported in the fixed bulk window. -/
theorem weighted_remote_eq_bulkRemote (near : Finset (Fin (N n)))
    (E gap : ℝ) (hgap : 0 < gap) (z : ℂ) (i j : Fin 4)
    (t : ProposalSample (N n) d) :
    D.weightedCenteredPartialProposalResolvent n ω nearᶜ
      (fun k => outerCutoff E gap (D.eigenvalue n ω k)) z i j t =
    D.weightedCenteredPartialProposalResolvent n ω (D.bulkRemoteEigenvalues n ω near E gap)
      (fun k => outerCutoff E gap (D.eigenvalue n ω k)) z i j t := by
  unfold weightedCenteredPartialProposalResolvent bulkRemoteEigenvalues
  symm
  apply Finset.sum_subset (Finset.inter_subset_left)
  intro k hk hnot
  have hn : k ∉ D.eigenvalueWindow n ω E (2 * gap) := by
    intro hh
    exact hnot (Finset.mem_inter.mpr ⟨hk,hh⟩)
  have habs : 2 * gap ≤ |D.eigenvalue n ω k - E| := by
    have hh : ¬ |D.eigenvalue n ω k - E| ≤ 2 * gap := by
      simpa only [eigenvalueWindow, Finset.mem_filter, Finset.mem_univ, true_and] using hn
    exact (lt_of_not_ge hh).le
  dsimp only
  rw [outerCutoff_eq_zero E gap _ hgap habs]
  simp

/-- Inside the near window the cutoff is exactly one. -/
theorem weighted_near_eq_partial (E gap eta : ℝ) (hgap : 0 < gap) (heta : eta ≤ gap)
    (z : ℂ) (i j : Fin 4) (t : ProposalSample (N n) d) :
    D.weightedCenteredPartialProposalResolvent n ω (D.eigenvalueWindow n ω E eta)
      (fun k => outerCutoff E gap (D.eigenvalue n ω k)) z i j t =
      D.centeredPartialProposalResolvent n ω (D.eigenvalueWindow n ω E eta) z i j t := by
  unfold weightedCenteredPartialProposalResolvent centeredPartialProposalResolvent
  apply Finset.sum_congr rfl
  intro k hk
  have hb : |D.eigenvalue n ω k - E| ≤ gap := (Finset.mem_filter.mp hk).2.trans heta
  dsimp only
  rw [outerCutoff_eq_one E gap _ hgap hb, Complex.ofReal_one, one_mul]

/-- The exact finite truncation error has only a centered bulk-remote sum
and the centered outer compression. -/
theorem centered_proposal_truncation_decomposition (hd : 0 < d)
    (E gap eta : ℝ) (hgap : 0 < gap) (heta : eta ≤ gap)
    (z : ℂ) (hz : z.im ≠ 0) (i j : Fin 4) (t : ProposalSample (N n) d) :
    D.resolvent n ω z (D.proposalEndpoints n ω t i) (D.proposalEndpoints n ω t j) -
      D.proposalMean n ω z i j -
      D.centeredPartialProposalResolvent n ω (D.eigenvalueWindow n ω E eta) z i j t =
      D.weightedCenteredPartialProposalResolvent n ω
        (D.bulkRemoteEigenvalues n ω (D.eigenvalueWindow n ω E eta) E gap)
        (fun k => outerCutoff E gap (D.eigenvalue n ω k)) z i j t +
      (D.outerProposalEntry n ω E gap z i j t -
        ∫ s, D.outerProposalEntry n ω E gap z i j s ∂uniformOrientedProposals (N n) d) := by
  have h := D.centered_proposal_resolvent_cutoff_decomposition n ω hd
    (D.eigenvalueWindow n ω E eta) E gap z hz i j t
  rw [D.weighted_near_eq_partial n ω E gap eta hgap heta z i j t,
    D.weighted_remote_eq_bulkRemote n ω _ E gap hgap z i j t] at h
  rw [h]
  ring

/-- Retained nonconstant physical marks have the exact finite covariance
centering used in the limiting Gaussian series. -/
theorem centeredPartialProposalResolvent_eq_covariance_series (hd : 0 < d)
    (s : Finset (Fin (N n)))
    (hs : ∀ k ∈ s, k ≠ ⟨0,D.size_pos n⟩)
    (z : ℂ) (i j : Fin 4) (t : ProposalSample (N n) d) :
    D.centeredPartialProposalResolvent n ω s z i j t =
      ∑ k ∈ s, ((N n : ℂ)⁻¹ * ((D.eigenvalue n ω k : ℂ) - z)⁻¹) *
        ((D.proposalQuadratic n ω k i j t -
          (GeneralizedBulk.covarianceMatrix (D.eigenvalue n ω k / d)) i j : ℝ) : ℂ) := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [D.centeredProposalQuadratic_eq_covariance n ω hd k (hs k hk)]

/-- The cutoff-selected remote channels are genuinely remote from the
near-window center. -/
theorem bulkRemoteEigenvalues_subset_remote (E gap eta : ℝ) :
    D.bulkRemoteEigenvalues n ω (D.eigenvalueWindow n ω E eta) E gap ⊆
      D.remoteEigenvalues n ω E eta := by
  intro k hk
  have hn := (Finset.mem_inter.mp hk).1
  have hnot : ¬ |D.eigenvalue n ω k - E| ≤ eta := by
    simpa only [Finset.mem_compl, eigenvalueWindow, Finset.mem_filter,
      Finset.mem_univ, true_and] using hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (lt_of_not_ge hnot).le⟩

/-- Squared truncation error is bounded by the two actual centered second
moments; no exceptional-set estimate is assumed in this comparison. -/
theorem proposal_truncation_variance_le (hd : 0 < d)
    (E gap eta : ℝ) (hgap : 0 < gap) (heta : eta ≤ gap)
    (z : ℂ) (hz : z.im ≠ 0) (i j : Fin 4) :
    (∫ t, ‖D.resolvent n ω z (D.proposalEndpoints n ω t i) (D.proposalEndpoints n ω t j) -
      D.proposalMean n ω z i j -
      D.centeredPartialProposalResolvent n ω (D.eigenvalueWindow n ω E eta) z i j t‖ ^ 2
      ∂uniformOrientedProposals (N n) d) ≤
      2 * (∫ t, ‖D.weightedCenteredPartialProposalResolvent n ω
        (D.bulkRemoteEigenvalues n ω (D.eigenvalueWindow n ω E eta) E gap)
        (fun k => outerCutoff E gap (D.eigenvalue n ω k)) z i j t‖ ^ 2
        ∂uniformOrientedProposals (N n) d) +
      2 * D.outerProposalVariance n ω E gap z i j := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0,D.size_pos n⟩,⟨0,hd⟩⟩⟩
  let A := fun t => D.weightedCenteredPartialProposalResolvent n ω
    (D.bulkRemoteEigenvalues n ω (D.eigenvalueWindow n ω E eta) E gap)
    (fun k => outerCutoff E gap (D.eigenvalue n ω k)) z i j t
  let B := fun t => D.outerProposalEntry n ω E gap z i j t -
    ∫ s, D.outerProposalEntry n ω E gap z i j s ∂uniformOrientedProposals (N n) d
  have hp (t : ProposalSample (N n) d) : ‖A t + B t‖ ^ 2 ≤ 2 * ‖A t‖ ^ 2 + 2 * ‖B t‖ ^ 2 := by
    have hn := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (norm_add_le (A t) (B t))
    nlinarith [sq_nonneg (‖A t‖ - ‖B t‖)]
  simp_rw [D.centered_proposal_truncation_decomposition n ω hd E gap eta hgap heta z hz i j]
  have hiA : Integrable (fun t => ‖A t‖ ^ 2) (uniformOrientedProposals (N n) d) :=
    integrable_finiteUniform_real _
  have hiB : Integrable (fun t => ‖B t‖ ^ 2) (uniformOrientedProposals (N n) d) :=
    integrable_finiteUniform_real _
  have h := integral_mono (μ := uniformOrientedProposals (N n) d)
    (integrable_finiteUniform_real (fun t => ‖A t + B t‖ ^ 2))
    ((hiA.const_mul 2).add (hiB.const_mul 2)) hp
  simp only [Pi.add_apply] at h
  rw [integral_add (hiA.const_mul 2) (hiB.const_mul 2), integral_const_mul, integral_const_mul] at h
  exact h

end GeneralizedBulk.External.RegularSpectralData
