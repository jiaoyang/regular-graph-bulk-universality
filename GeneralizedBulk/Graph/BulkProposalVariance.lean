import GeneralizedBulk.Graph.BulkFourthMoment
import GeneralizedBulk.Graph.StarProposalCovarianceRates
import GeneralizedBulk.Graph.MicroscopicTruncationVariance

/-! Actual one/two-color common entropy events prove the finite proposal
covariance and conditional physical variance required by the scalar tail.
No covariance or variance certificate is an external input. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology Classical
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Gaussian GeneralizedBulk.Entropy.ChannelRates GeneralizedBulk.KestenMcKay
open Graph GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def commonOneTwoEntropyGood (P : Measure Ω) [IsProbabilityMeasure P]
    (coarse localEvents : PolynomialGoodEvents P N) (n : ℕ) : Set Ω :=
  D.commonEntropyGood P 1 coarse localEvents n ∩ D.commonEntropyGood P 2 coarse localEvents n

def proposalCovarianceExponent (d : ℕ) (rigidity localExponent height : ℝ) : ℝ :=
  min (bulkEntropyExponent 1 d rigidity localExponent height/36)
    (bulkEntropyExponent 2 d rigidity localExponent height/36)

theorem proposalCovarianceExponent_pos (rigidity localExponent height : ℝ)
    (hl : 0 < localExponent) (hh : 0 < height) (hr : height < rigidity) (h1 : height < 1) :
    0 < proposalCovarianceExponent d rigidity localExponent height :=
  lt_min (div_pos (bulkEntropyExponent_pos 1 d _ _ _ hl hh hr h1) (by norm_num))
    (div_pos (bulkEntropyExponent_pos 2 d _ _ _ hl hh hr h1) (by norm_num))

theorem measurableSet_commonOneTwoEntropyGood (P : Measure Ω) [IsProbabilityMeasure P]
    (coarse localEvents : PolynomialGoodEvents P N) (n : ℕ) :
    MeasurableSet (D.commonOneTwoEntropyGood P coarse localEvents n) :=
  (D.measurableSet_commonEntropyGood P 1 coarse localEvents n).inter
    (D.measurableSet_commonEntropyGood P 2 coarse localEvents n)

theorem commonOneTwoEntropyGood_failure_tendsto_zero {P : Measure Ω} [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 0 < d) (coarse localEvents : PolynomialGoodEvents P N) :
    Tendsto (fun n => P.real (D.commonOneTwoEntropyGood P coarse localEvents n)ᶜ) atTop (nhds 0) :=
  intersection_failure_tendsto_zero P _ _
    (D.commonEntropyGood_failure_tendsto_zero hUniform hd 1 coarse localEvents)
    (D.commonEntropyGood_failure_tendsto_zero hUniform hd 2 coarse localEvents)

set_option maxHeartbeats 2500000 in
theorem HY_common_proposal_covariance_window {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ d) (Hc : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast hd)))
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1))
    (c0 : ℝ) (hc1 : c0 < channelNoiseExponent (channelTheta 1 d))
    (hc2 : c0 < channelNoiseExponent (channelTheta 2 d))
    (hcr : c0 < Hc.rigidity_exponent) (hcs : c0 ≤ 1/16)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d (by exact_mod_cast hd))) :
    ∀ᶠ n in atTop,∀ ω ∈ D.commonOneTwoEntropyGood P Hc.events H.events n,
      ∀ s : Finset (Fin (N n)),(∀ k ∈ s,D.eigenvalue n ω k ∈ K) →
      ∀ k ∈ s,∀ l ∈ s,∀ i j : Fin 4,
        |∫ t,D.centeredProposalQuadratic n ω k i j t*D.centeredProposalQuadratic n ω l i j t
          ∂uniformOrientedProposals (N n) d| ≤
          2*(if k=l then 1 else 0)+(N n : ℝ)^(-proposalCovarianceExponent d Hc.rigidity_exponent H.local_exponent c0) := by
  have hfirst := D.HY_common_event_fourth_moments hd Hc 1 (by norm_num) K hK hbulk c0 hc1 hcr hcs H
  have hsecond := D.HY_common_event_fourth_moments hd Hc 2 (by norm_num) K hK hbulk c0 hc2 hcr hcs H
  filter_upwards [hfirst,hsecond] with n hfirst hsecond ω hω s hs k hk l hl i j
  have hN : (1 : ℝ) ≤ N n := by exact_mod_cast (D.size_pos n)
  have hnonconstant (a : Fin (N n)) (ha : a ∈ s) : a ≠ ⟨0,D.size_pos n⟩ := by
    intro heq
    have hb := hbulk _ (hs a ha)
    rw [heq,D.constant_eigenvalue] at hb
    nlinarith [sq_nonneg ((d : ℝ)-2)]
  apply D.proposal_covariance_window_of_one_two_color_Wick n ω (by omega) s hnonconstant _
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) _ k hk l hl i j
  intro m hm selection hinj hsel j1 j2 j3 j4
  interval_cases m
  · exact Fin.elim0 j1.1
  · exact (hfirst ω hω.1 selection hinj (fun a => hs _ (hsel a)) j1 j2 j3 j4).trans
      (Real.rpow_le_rpow_of_exponent_le hN (by
        unfold proposalCovarianceExponent
        linarith [min_le_left (bulkEntropyExponent 1 d Hc.rigidity_exponent H.local_exponent c0/36)
          (bulkEntropyExponent 2 d Hc.rigidity_exponent H.local_exponent c0/36)]))
  · exact (hsecond ω hω.2 selection hinj (fun a => hs _ (hsel a)) j1 j2 j3 j4).trans
      (Real.rpow_le_rpow_of_exponent_le hN (by
        unfold proposalCovarianceExponent
        linarith [min_le_right (bulkEntropyExponent 1 d Hc.rigidity_exponent H.local_exponent c0/36)
          (bulkEntropyExponent 2 d Hc.rigidity_exponent H.local_exponent c0/36)]))

set_option maxHeartbeats 2500000 in
theorem HY_common_graphFiber_linear_variance {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ d) (Hc : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast hd)))
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1))
    (c0 : ℝ) (hc1 : c0 < channelNoiseExponent (channelTheta 1 d))
    (hc2 : c0 < channelNoiseExponent (channelTheta 2 d))
    (hcr : c0 < Hc.rigidity_exponent) (hcs : c0 ≤ 1/16)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d (by exact_mod_cast hd)))
    {Km : Set ℝ} {alpha : ℝ} (Hm : HYMesoscopicInput D P Km alpha)
    (hchi : 2*alpha ≤ proposalCovarianceExponent d Hc.rigidity_exponent H.local_exponent c0)
    (E : ℝ) (hE : E ∈ Km) (gap cstar : ℝ) (hgap : 0 < gap) (hcstar : 0 < cstar)
    (hwindow : Icc (E-2*gap) (E+2*gap) ⊆ K) (L : ℕ) (hL : 2*gap ≤ (2 : ℝ)^L) :
    ∃ V : ℝ,0 < V ∧ ∀ᶠ n in atTop,
      ∀ ω ∈ D.commonOneTwoEntropyGood P Hc.events H.events n ∩ Hm.events.good n,
      ∀ eta : ℝ,0 < eta → cstar ≤ (N n : ℝ)*eta → ∀ i j : Fin 4,
        (∫ t : {t : EdgePairState (N n) d // edgePairGraph t=D.spectralRegularGraph n ω},
          ‖graphDeviation t.val (spectralParameter E eta) i j‖^2
          ∂finiteUniform {t : EdgePairState (N n) d // edgePairGraph t=D.spectralRegularGraph n ω}) ≤
          V*(1+graphHeight (D.spectralRegularGraph n ω) (spectralParameter E eta)) := by
  obtain ⟨V,hV,hvariance⟩ := D.graphFiber_linear_variance_of_HY_covariance_rate Hm (by omega) E hE
    cstar gap hcstar hgap L 2 1 (proposalCovarianceExponent d Hc.rigidity_exponent H.local_exponent c0)
    (by norm_num) (by norm_num) hchi
  refine ⟨V,hV,?_⟩
  filter_upwards [hvariance,D.HY_common_proposal_covariance_window hd Hc K hK hbulk c0 hc1 hc2 hcr hcs H]
    with n hvariance hcov ω hω eta heta hheight i j
  let s := D.eigenvalueWindow n ω E (2*gap)
  have hs (k : Fin (N n)) (hk : k ∈ s) : |D.eigenvalue n ω k-E| ≤ 2*gap := (Finset.mem_filter.mp hk).2
  have hsK (k : Fin (N n)) (hk : k ∈ s) : D.eigenvalue n ω k ∈ K := by
    have hh := abs_le.mp (hs k hk)
    exact hwindow ⟨by linarith,by linarith⟩
  have hremote : sᶜ ⊆ D.remoteEigenvalues n ω E gap := by
    intro k hk
    have hh : ¬ |D.eigenvalue n ω k-E| ≤ 2*gap := by
      simpa only [s,eigenvalueWindow,Finset.mem_compl,Finset.mem_filter,Finset.mem_univ,true_and] using hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by linarith [lt_of_not_ge hh]⟩
  exact hvariance ω hω.2 s (fun k hk => (hs k hk).trans hL) hremote i j
    (fun k hk l hl => by simpa only [one_mul] using hcov ω hω.1 s hsK k hk l hl i j) eta heta hheight

end GeneralizedBulk.External.RegularSpectralData
