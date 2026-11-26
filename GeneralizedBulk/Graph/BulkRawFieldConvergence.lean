import GeneralizedBulk.Graph.BulkCenteredFieldConvergence
import GeneralizedBulk.Graph.RawFieldMeanConvergence

/-! The public actual raw finite-dimensional marked-field limit. All
finite-window, covariance, tail, and mean-calibration estimates are proved;
the only theorem inputs are the explicitly permitted BS and HY results. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Counting GeneralizedBulk.Analysis GeneralizedBulk.Gaussian
open GeneralizedBulk.KestenMcKay GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω V : Type*} [MeasurableSpace Ω] [Fintype V]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2500000 in
theorem microscopicRawState_converges_of_BS_HY_limit [Nonempty Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 3 ≤ d) (HC : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast hd)))
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1))
    (c0 : ℝ) (hc1 : c0 < channelNoiseExponent (channelTheta 1 d))
    (hc2 : c0 < channelNoiseExponent (channelTheta 2 d))
    (hcr : c0 < HC.rigidity_exponent) (hcs : c0 ≤ 1/16)
    (HL : HYLocalStarInput D P K c0 (treeGreenStar d (by exact_mod_cast hd)))
    {Km : Set ℝ} {alpha : ℝ} (HM : HYMesoscopicInput D P Km alpha) (halpha : alpha < 1)
    (hchi : 2*alpha < proposalCovarianceExponent d HC.rigidity_exponent HL.local_exponent c0)
    (KBS : Set ℝ) (BS : BSQualitativeInput D P KBS)
    (E : ℝ) (hEbulk : E^2 < 4*((d : ℝ)-1)) (hE : E ∈ Km) (hEBS : E ∈ KBS) (gap : ℝ) (hgap : 0 < gap)
    (hwindow : Icc (E-2*gap) (E+2*gap) ⊆ K) (L : ℕ) (hL : 2*gap ≤ (2 : ℝ)^L)
    (HG : HYGeometryInput D P)
    (r : ℕ → ℕ) (hr : StrictMono r)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (hscalar : WeakLawConverges
      (fun n => P.map (fun ω => D.microscopicCountingState (r n) ω E (Parameters.regular d E (by exact_mod_cast hd) hEbulk).scale (Parameters.regular d E (by exact_mod_cast hd) hEbulk).center)) ν)
    (w : V → GraphNonreal) :
    let parameters := Parameters.regular d E (by exact_mod_cast hd) hEbulk
    WeakLawConverges
      (fun n => Measure.map (D.microscopicRawState (r n) E parameters.center parameters w)
        (P.prod (uniformOrientedProposals (N (r n)) d)))
      (Measure.map (massRawState ν hm parameters w) (massMarkedLaw ν parameters)) := by
  intro parameters
  have hp : parameters.p=E/(d : ℝ) := by simp only [parameters,Parameters.regular_p]
  have hcentered := D.microscopicCenteredState_converges_of_BS_HY_limit P hUniform hd HC K hK hbulk c0 hc1 hc2
    hcr hcs HL HM halpha hchi KBS BS E hE hEBS gap hgap hwindow L hL parameters.center parameters hp HG
    r hr ν hm hscalar w
  exact D.microscopicRawState_converges_of_centered P E (by exact_mod_cast hd) hEbulk r hr w ν hm hcentered

end GeneralizedBulk.External.RegularSpectralData
