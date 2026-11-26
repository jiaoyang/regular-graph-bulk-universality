import GeneralizedBulk.Graph.FiniteTruncation

/-! The complete finite microscopic truncation bound from HY and a literal covariance rate. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def microscopicTruncationVariance (n : ℕ) (ω : Ω)
    (E sigma : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) (R : ℝ) (i j : Fin 4) : ℝ :=
  ∫ t, ‖D.resolvent n ω (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1
      (D.proposalEndpoints n ω t i) (D.proposalEndpoints n ω t j) -
    D.proposalMean n ω (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j -
    D.centeredPartialProposalResolvent n ω
      (D.eigenvalueWindow n ω E (microscopicStep (N n) sigma * R))
      (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j t‖ ^ 2
    ∂uniformOrientedProposals (N n) d

/-- Every error in the finite microscopic truncation is displayed: the
Poisson trace at cutoff height, the covariance rate, and the centered outer
compression. In particular the remote variance itself is not a premise. -/
theorem microscopicTruncationVariance_le_of_HY_covariance_rate
    {P : Measure Ω} [IsProbabilityMeasure P] {K : Set ℝ} {alpha : ℝ}
    (H : HYMesoscopicInput D P K alpha) (hd : 0 < d) (E : ℝ) (hE : E ∈ K)
    (gap sigma : ℝ) (hgap : 0 < gap) (hsigma : 0 < sigma)
    (w : GraphNonreal) (L : ℕ) (hwindow : 2 * gap ≤ (2 : ℝ) ^ L)
    (C C0 chi : ℝ) (hC : 0 ≤ C) (hC0 : 0 ≤ C0) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop,
      ∀ ω ∈ H.events.good n, ∀ R : ℝ, 0 < R → 2 * |w.1.re| ≤ R →
      microscopicStep (N n) sigma * R ≤ gap → ∀ i j : Fin 4,
      (∀ k ∈ D.bulkRemoteEigenvalues n ω
          (D.eigenvalueWindow n ω E (microscopicStep (N n) sigma * R)) E gap,
        ∀ l ∈ D.bulkRemoteEigenvalues n ω
          (D.eigenvalueWindow n ω E (microscopicStep (N n) sigma * R)) E gap,
        |∫ t, D.centeredProposalQuadratic n ω k i j t *
          D.centeredProposalQuadratic n ω l i j t ∂uniformOrientedProposals (N n) d| ≤
        C * (if k = l then 1 else 0) + C0 * (N n : ℝ) ^ (-chi)) →
      D.microscopicTruncationVariance n ω E sigma hsigma w R i j ≤
        (16 * C * sigma / R) * (D.scalarResolvent n ω
          (spectralParameter E (microscopicStep (N n) sigma * R))).im +
        2 * C0 * B ^ 2 * (N n : ℝ) ^ (-chi + 2 * alpha) +
        2 * D.outerProposalVariance n ω E gap
          (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j := by
  obtain ⟨B,hB,hremote⟩ := D.weighted_microscopic_remote_variance_of_HY_covariance_rate
    H hd E hE sigma hsigma w L C C0 chi hC hC0
  refine ⟨B,hB,?_⟩
  filter_upwards [hremote] with n hn
  intro ω hω R hR hw hcut i j hcov
  let s := D.bulkRemoteEigenvalues n ω
    (D.eigenvalueWindow n ω E (microscopicStep (N n) sigma * R)) E gap
  have hs (k) (hk : k ∈ s) : |D.eigenvalue n ω k - E| ≤ (2 : ℝ) ^ L :=
    ((Finset.mem_filter.mp (Finset.mem_inter.mp hk).2).2).trans hwindow
  have htheta (k) (_hk : k ∈ s) : |outerCutoff E gap (D.eigenvalue n ω k)| ≤ 1 := by
    rw [abs_of_nonneg (outerCutoff_bounds E gap _).1]
    exact (outerCutoff_bounds E gap _).2
  have hb := hn ω hω s hs (fun k => outerCutoff E gap (D.eigenvalue n ω k)) htheta
    R hR hw (D.bulkRemoteEigenvalues_subset_remote n ω E gap _) i j hcov
  have he := D.proposal_truncation_variance_le n ω hd E gap
    (microscopicStep (N n) sigma * R) hgap hcut
    (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1
    (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).2 i j
  change D.microscopicTruncationVariance n ω E sigma hsigma w R i j ≤ _ at he
  dsimp only [s] at hb
  apply he.trans
  convert add_le_add_right (mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ 2 by norm_num))
    (2 * D.outerProposalVariance n ω E gap
      (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j) using 1 <;> ring

end GeneralizedBulk.External.RegularSpectralData
