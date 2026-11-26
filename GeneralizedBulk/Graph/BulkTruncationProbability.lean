import GeneralizedBulk.Graph.BulkScalarBounds
import GeneralizedBulk.Graph.TruncationErrorMeasurable
import GeneralizedBulk.Analysis.CappedTruncationProbability

/-! Actual finite-model tails of the centered microscopic marked resolvent.
Every exceptional event and finite scalar cap is retained until after the
finite-model limit; only the permitted HY estimates are external. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Analysis GeneralizedBulk.Gaussian GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 3000000 in
theorem HY_microscopic_centered_truncation_probability {P : Measure Ω} [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 3 ≤ d) (Hc : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast hd)))
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1))
    (c0 : ℝ) (hc1 : c0 < channelNoiseExponent (channelTheta 1 d))
    (hc2 : c0 < channelNoiseExponent (channelTheta 2 d))
    (hcr : c0 < Hc.rigidity_exponent) (hcs : c0 ≤ 1/16)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d (by exact_mod_cast hd)))
    {Km : Set ℝ} {alpha : ℝ} (Hm : HYMesoscopicInput D P Km alpha)
    (hchi : 2*alpha < proposalCovarianceExponent d Hc.rigidity_exponent H.local_exponent c0)
    (E : ℝ) (hE : E ∈ Km) (gap : ℝ) (hgap : 0 < gap)
    (hwindow : Icc (E-2*gap) (E+2*gap) ⊆ K) (L : ℕ) (hL : 2*gap ≤ (2 : ℝ)^L)
    (sigma center : ℝ) (hsigma : 0 < sigma)
    (Hg : HYGeometryInput D P) (w : GraphNonreal)
    (R : ℕ → ℝ) (hR : ∀ k : ℕ,(k:ℝ)+1 ≤ R k) (i j : Fin 4) :
    ∀ ε δ : ℝ,0 < ε → 0 < δ → ∃ k0 : ℕ,∀ k : ℕ,k0 ≤ k →
      ∀ᶠ n in atTop,(P.prod (uniformOrientedProposals (N n) d)).real
        {z | ε < ‖D.microscopicCenteredTruncationError n E sigma hsigma w (R k) i j z‖} ≤ δ := by
  letI : ∀ n,IsProbabilityMeasure (uniformOrientedProposals (N n) d) :=
    fun n => uniformOrientedProposals_isProbability _ _ (D.size_pos n) (by omega)
  obtain ⟨cap,hcap0,hcap,constants,hconstants,bounds,hbounds,hmoment⟩ :=
    D.HY_bulk_scalar_capped_moment_limits hUniform hd Hc K hK hbulk c0 hc1 hc2 hcr hcs H Hm hchi.le
      E hE gap hgap hwindow L hL sigma center hsigma
  obtain ⟨B,hB,hvar⟩ := D.HY_common_microscopicTruncationVariance_le hd Hc K hK hbulk
    c0 hc1 hc2 hcr hcs H Hm E hE gap sigma hgap hsigma hwindow w L hL
  let good := D.commonProposalGood P Hc.events H.events Hm.events
  let o := fun n ω => D.outerProposalVariance n ω E gap
    (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).val i j
  let v := fun n => 2*B^2*(N n:ℝ)^(-proposalCovarianceExponent d Hc.rigidity_exponent H.local_exponent c0+2*alpha)
  have hv : Tendsto v atTop (𝓝 0) := by
    have hp := (tendsto_rpow_neg_atTop (show 0 < proposalCovarianceExponent d
      Hc.rigidity_exponent H.local_exponent c0-2*alpha by linarith)).comp
      (tendsto_natCast_atTop_atTop.comp D.size_tendsto)
    have he : -proposalCovarianceExponent d Hc.rigidity_exponent H.local_exponent c0+2*alpha =
        -(proposalCovarianceExponent d Hc.rigidity_exponent H.local_exponent c0-2*alpha) := by ring
    simpa only [v,he,Function.comp_def,mul_zero] using hp.const_mul (2*B^2)
  have ho : ∀ᶠ n in atTop,Integrable (o n) P := by
    have hz := microscopicParameter_tendsto_center N D.size_pos D.size_tendsto E sigma hsigma w
    have hnear : Tendsto (fun n => ‖(microscopicParameter (N n) (D.size_pos n)
        E sigma hsigma w).val-(E:ℂ)‖) atTop (𝓝 0) := by
      simpa only [sub_self,norm_zero] using (hz.sub_const (E:ℂ)).norm
    have hnear' : ∀ᶠ n in atTop,‖(microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).val-(E:ℂ)‖ ≤ gap/2 := by
      simpa only [sub_self,norm_zero] using
        (hnear.eventually (eventually_lt_nhds (half_pos hgap))).mono (fun _ hn => hn.le)
    filter_upwards [hnear'] with n hn
    exact D.outerProposalVariance_integrable_near P n (by omega) E gap hgap _ hn i j
  have hfirst (k : ℕ) : ∀ᶠ n in atTop,
      (∫ ω,(good n).indicator (fun ω => min (D.microscopicVerticalNorm n ω E sigma center k) (cap n)) ω ∂P) ≤ constants 1+1 := by
    have hb := ((hbounds 1).eventually (eventually_lt_nhds
      (by linarith : constants 1 < constants 1+1))).mono (fun _ hh => hh.le)
    filter_upwards [hmoment k 1,hb] with n hn hb
    have hh : (∫ ω,(good n).indicator (fun ω => min
        (D.microscopicVerticalNorm n ω E sigma center k) (cap n)) ω ∂P) ≤ bounds 1 n := by
      simpa only [pow_one,good] using hn
    exact hh.trans hb
  have hvariance : ∀ᶠ k in atTop,∀ᶠ n in atTop,∀ ω ∈ good n,
      (∫ t,‖D.microscopicCenteredTruncationError n E sigma hsigma w (R k) i j (ω,t)‖^2
        ∂uniformOrientedProposals (N n) d) ≤
      (32*sigma^2)/((k:ℝ)+1)*D.microscopicVerticalNorm n ω E sigma center k+v n+2*o n ω := by
    have hklarge : ∀ᶠ k : ℕ in atTop,2*|w.val.re| ≤ (k:ℝ)+1 := by
      exact (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (2*|w.val.re|))
    filter_upwards [hklarge] with k hk
    have hcut : ∀ᶠ n in atTop,microscopicStep (N n) sigma*R k ≤ gap := by
      have ht : Tendsto (fun n => microscopicStep (N n) sigma*R k) atTop (𝓝 0) := by
        simpa only [zero_mul] using (microscopicStep_tendsto_zero N D.size_tendsto sigma).mul_const (R k)
      exact ((tendsto_order.mp ht).2 gap hgap).mono (fun _ hh => hh.le)
    filter_upwards [hvar,hcut] with n hn hcut ω hω
    have hRpos : 0 < R k := (show (0:ℝ) < (k:ℝ)+1 by positivity).trans_le (hR k)
    have hh := hn ω hω (R k) hRpos (hk.trans (hR k)) hcut i j
    have hheight := D.cutoffPoissonTrace_le_verticalNorm n ω E sigma center (R k) hsigma k (hR k)
    exact hh.trans (add_le_add_right (add_le_add_right hheight _) _)
  apply capped_truncation_probability_two_step P (fun n => uniformOrientedProposals (N n) d)
    good (D.measurableSet_commonProposalGood P Hc.events H.events Hm.events)
    (D.commonProposalGood_failure_tendsto_zero hUniform (by omega) Hc.events H.events Hm.events)
    cap hcap (fun k n ω => D.microscopicVerticalNorm n ω E sigma center k)
    (fun k n => D.measurable_microscopicVerticalNorm n E sigma center k)
    (fun k n ω => norm_nonneg _) (constants 1+1) (32*sigma^2)
    (by linarith [hconstants 1]) (by positivity) hfirst
    (fun k n => D.microscopicCenteredTruncationError n E sigma hsigma w (R k) i j)
    (fun k n => D.measurable_microscopicCenteredTruncationError n (by omega) E sigma hsigma w (R k) i j)
    v hv o ho (fun n ω => integral_nonneg (fun t => sq_nonneg _))
    (D.integral_microscopic_outerVariance_tendsto_zero Hg (by omega) E gap sigma hgap hsigma w i j)
    hvariance

end GeneralizedBulk.External.RegularSpectralData
