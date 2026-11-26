import GeneralizedBulk.Graph.BulkProposalGoodEvent

/-! The actual finite marked-resolvent truncation bound, with the one/two
color proposal covariance supplied by proved entropy/counting estimates. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Gaussian GeneralizedBulk.KestenMcKay GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2000000 in
theorem HY_common_microscopicTruncationVariance_le {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ d) (Hc : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast hd)))
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1))
    (c0 : ℝ) (hc1 : c0 < channelNoiseExponent (channelTheta 1 d))
    (hc2 : c0 < channelNoiseExponent (channelTheta 2 d))
    (hcr : c0 < Hc.rigidity_exponent) (hcs : c0 ≤ 1/16)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d (by exact_mod_cast hd)))
    {Km : Set ℝ} {alpha : ℝ} (Hm : HYMesoscopicInput D P Km alpha)
    (E : ℝ) (hE : E ∈ Km) (gap sigma : ℝ) (hgap : 0 < gap) (hsigma : 0 < sigma)
    (hwindow : Icc (E-2*gap) (E+2*gap) ⊆ K) (w : GraphNonreal)
    (L : ℕ) (hL : 2*gap ≤ (2 : ℝ)^L) :
    ∃ B : ℝ,0 < B ∧ ∀ᶠ n in atTop,
      ∀ ω ∈ D.commonProposalGood P Hc.events H.events Hm.events n,
      ∀ R : ℝ,0 < R → 2*|w.1.re| ≤ R → microscopicStep (N n) sigma*R ≤ gap → ∀ i j : Fin 4,
      D.microscopicTruncationVariance n ω E sigma hsigma w R i j ≤
        (32*sigma/R)*(D.scalarResolvent n ω (spectralParameter E (microscopicStep (N n) sigma*R))).im+
        2*B^2*(N n : ℝ)^(-proposalCovarianceExponent d Hc.rigidity_exponent H.local_exponent c0+2*alpha)+
        2*D.outerProposalVariance n ω E gap
          (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).1 i j := by
  obtain ⟨B,hB,hvariance⟩ := D.microscopicTruncationVariance_le_of_HY_covariance_rate Hm (by omega) E hE
    gap sigma hgap hsigma w L hL 2 1 (proposalCovarianceExponent d Hc.rigidity_exponent H.local_exponent c0)
    (by norm_num) (by norm_num)
  refine ⟨B,hB,?_⟩
  filter_upwards [hvariance,D.HY_common_proposal_covariance_window hd Hc K hK hbulk c0 hc1 hc2 hcr hcs H]
    with n hvariance hcov ω hω R hR hw hcut i j
  have hh := hvariance ω hω.2 R hR hw hcut i j ?_
  · convert hh using 1 <;> ring
  · let s := D.bulkRemoteEigenvalues n ω (D.eigenvalueWindow n ω E (microscopicStep (N n) sigma*R)) E gap
    have hsK (a : Fin (N n)) (ha : a ∈ s) : D.eigenvalue n ω a ∈ K := by
      have hh := (Finset.mem_filter.mp (Finset.mem_inter.mp ha).2).2
      have hbound := abs_le.mp hh
      exact hwindow ⟨by linarith,by linarith⟩
    intro k hk l hl
    simpa only [one_mul] using hcov ω hω.1 s hsK k hk l hl i j

end GeneralizedBulk.External.RegularSpectralData
