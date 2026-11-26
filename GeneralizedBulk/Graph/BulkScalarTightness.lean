import GeneralizedBulk.Graph.BulkScalarBounds
import GeneralizedBulk.Analysis.CappedTightness

/-! Actual uniform anchor tails and anchored counting-state subsequences
follow from the proved finite capped entropy/switching bounds. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical ENNReal
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Analysis GeneralizedBulk.Gaussian GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2000000 in
theorem HY_bulk_anchor_tails_and_subsequence {P : Measure Ω} [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 3 ≤ d) (Hc : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast hd)))
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1))
    (c0 : ℝ) (hc1 : c0 < channelNoiseExponent (channelTheta 1 d))
    (hc2 : c0 < channelNoiseExponent (channelTheta 2 d))
    (hcr : c0 < Hc.rigidity_exponent) (hcs : c0 ≤ 1/16)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d (by exact_mod_cast hd)))
    {Km : Set ℝ} {alpha : ℝ} (Hm : HYMesoscopicInput D P Km alpha)
    (hchi : 2*alpha ≤ proposalCovarianceExponent d Hc.rigidity_exponent H.local_exponent c0)
    (E : ℝ) (hE : E ∈ Km) (gap : ℝ) (hgap : 0 < gap)
    (hwindow : Icc (E-2*gap) (E+2*gap) ⊆ K) (L : ℕ) (hL : 2*gap ≤ (2 : ℝ)^L)
    (sigma center : ℝ) (hsigma : 0 < sigma) :
    (∀ epsilon : ℝ≥0∞,0 < epsilon → ∃ B : ℝ,∀ n,
      P {ω | B < ‖(D.microscopicCountingState n ω E sigma center).val.2‖} ≤ epsilon) ∧
    ∃ (ν : ProbabilityMeasure BourgadeHuang.AnchoredCountingState) (r : ℕ → ℕ),StrictMono r ∧
      WeakLawConverges (fun n => Measure.map (fun ω => D.microscopicCountingState (r n) ω E sigma center) P) ν := by
  obtain ⟨cap,hcap0,hcap,constants,hconstants,bounds,hbounds,hmoment⟩ :=
    D.HY_bulk_scalar_capped_moment_limits hUniform hd Hc K hK hbulk c0 hc1 hc2 hcr hcs H Hm hchi
      E hE gap hgap hwindow L hL sigma center hsigma
  let good := D.commonProposalGood P Hc.events H.events Hm.events
  have hgood := D.measurableSet_commonProposalGood P Hc.events H.events Hm.events
  have hbad := D.commonProposalGood_failure_tendsto_zero hUniform (by omega) Hc.events H.events Hm.events
  have hfirst : ∀ᶠ n in atTop,
      (∫ ω,(good n).indicator (fun ω => min ‖(D.microscopicCountingState n ω E sigma center).val.2‖ (cap n)) ω ∂P) ≤
        constants 1+1 := by
    have hbound := ((hbounds 1).eventually (eventually_lt_nhds (by linarith : constants 1 < constants 1+1))).mono
      (fun _ h => h.le)
    filter_upwards [hmoment 0 1,hbound] with n hn hb
    have hh : (∫ ω,(good n).indicator (fun ω => min ‖(D.microscopicCountingState n ω E sigma center).val.2‖ (cap n)) ω ∂P) ≤ bounds 1 n := by
      simpa only [D.microscopicVerticalNorm_zero_anchor,pow_one] using hn
    exact hh.trans hb
  have hC : 0 ≤ constants 1+1 := by linarith [hconstants 1]
  constructor
  · apply uniform_real_tails_of_good_capped_moment (fun _ : ℕ => P)
      (fun n ω => ‖(D.microscopicCountingState n ω E sigma center).val.2‖)
      (fun n => (measurable_snd.comp (D.measurable_microscopicCountingState n E sigma center).subtype_val).norm)
      (fun n ω => norm_nonneg _) good hgood hbad cap hcap (constants 1+1) hC hfirst
  · exact anchored_subsequence_of_good_capped_anchor_moment (fun _ : ℕ => P)
      (fun n ω => D.microscopicCountingState n ω E sigma center)
      (fun n => D.measurable_microscopicCountingState n E sigma center)
      good hgood hbad cap hcap (constants 1+1) hC hfirst

end GeneralizedBulk.External.RegularSpectralData
