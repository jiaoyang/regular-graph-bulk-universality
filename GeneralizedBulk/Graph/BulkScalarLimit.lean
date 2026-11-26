import GeneralizedBulk.Graph.BulkScalarBounds
import GeneralizedBulk.Graph.MicroscopicLimitMoments

/-! Actual scalar/counting bulk limits have every anchor moment, uniform
vertical moments, and zero escaped affine coefficient. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Analysis GeneralizedBulk.Gaussian GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2000000 in
theorem HY_bulk_scalar_limit_moments {P : Measure Ω} [IsProbabilityMeasure P]
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
    (sigma center : ℝ) (hsigma : 0 < sigma)
    (r : ℕ → ℕ) (hr : StrictMono r) (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hweak : WeakLawConverges
      (fun n => Measure.map (fun ω => D.microscopicCountingState (r n) ω E sigma center) P) ν) :
    AllMoments ν (fun s : AnchoredCountingState => s.val.2) ∧
      (∀ᵐ s ∂ν,anchoredLinearCoefficient s=0) ∧
      ∃ constants : ℕ → ℝ,(∀ q,0 ≤ constants q) ∧ ∀ Y q : ℕ,q ≠ 0 →
        Integrable (fun s : AnchoredCountingState => ‖anchoredNevanlinna s ((((Y : ℝ)+1 : ℝ) : ℂ)*Complex.I)‖^q) ν ∧
          (∫ s : AnchoredCountingState,‖anchoredNevanlinna s ((((Y : ℝ)+1 : ℝ) : ℂ)*Complex.I)‖^q ∂ν) ≤ constants q := by
  obtain ⟨cap,hcap0,hcap,constants,hconstants,bounds,hbounds,hmoment⟩ :=
    D.HY_bulk_scalar_capped_moment_limits hUniform hd Hc K hK hbulk c0 hc1 hc2 hcr hcs H Hm hchi
      E hE gap hgap hwindow L hL sigma center hsigma
  have hh := D.microscopic_limit_moments_of_caps E sigma center
    (D.commonProposalGood P Hc.events H.events Hm.events)
    (D.measurableSet_commonProposalGood P Hc.events H.events Hm.events)
    (D.commonProposalGood_failure_tendsto_zero hUniform (by omega) Hc.events H.events Hm.events)
    cap hcap0 hcap constants hconstants bounds hbounds hmoment r hr ν hweak
  exact ⟨hh.1,hh.2.1,constants,hconstants,hh.2.2⟩

end GeneralizedBulk.External.RegularSpectralData
