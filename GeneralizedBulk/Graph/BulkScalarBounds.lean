import GeneralizedBulk.Graph.BulkProposalGoodEvent
import GeneralizedBulk.Graph.MicroscopicMomentBounds

/-! Actual common-event capped moments of the microscopic scalar. All
physical variances and exceptional-event rates are proved from the concrete
uniform graph model and the permitted HY inputs. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Analysis GeneralizedBulk.Gaussian GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2000000 in
theorem HY_bulk_scalar_capped_moment_limits {P : Measure Ω} [IsProbabilityMeasure P]
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
    ∃ cap : ℕ → ℝ,(∀ n,0 ≤ cap n) ∧ Tendsto cap atTop atTop ∧
      ∃ constants : ℕ → ℝ,(∀ q,0 ≤ constants q) ∧ ∃ bounds : ℕ → ℕ → ℝ,
      (∀ q,Tendsto (bounds q) atTop (nhds (constants q))) ∧
      ∀ Y q : ℕ,∀ᶠ n in atTop,
        (∫ ω,(D.commonProposalGood P Hc.events H.events Hm.events n).indicator
          (fun ω => min (D.microscopicVerticalNorm n ω E sigma center Y) (cap n)^q) ω ∂P) ≤ bounds q n := by
  obtain ⟨V,hV,hvariance⟩ := D.HY_common_graphFiber_linear_variance hd Hc K hK hbulk c0 hc1 hc2 hcr hcs H Hm hchi
    E hE gap (1/sigma) hgap (one_div_pos.mpr hsigma) hwindow L hL
  obtain ⟨β,C,hβ,hC,hbad⟩ := D.commonProposalGood_failure_polynomial hUniform (by omega) Hc.events H.events Hm.events
  have hEbulk : E ∈ K := hwindow ⟨by linarith,by linarith⟩
  have hEdegree : |E| < d := bulk_abs_lt_degree (by exact_mod_cast hd) E (hbulk E hEbulk)
  exact D.exists_microscopic_capped_moment_limits hUniform (by omega) E hEdegree sigma center hsigma
    (D.commonProposalGood P Hc.events H.events Hm.events)
    (D.measurableSet_commonProposalGood P Hc.events H.events Hm.events) β C hβ hC.le hbad V hV.le hvariance

end GeneralizedBulk.External.RegularSpectralData
