import GeneralizedBulk.Graph.BulkRawFieldConvergence
import GeneralizedBulk.Graph.ResolventJetsSubsequence

/-! Actual joint value/derivative laws along every scalar subsequence, with
all value, analytic, and tightness inputs constructed from BS/HY. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Counting GeneralizedBulk.Analysis GeneralizedBulk.Gaussian
open GeneralizedBulk.KestenMcKay GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω V : Type*} [MeasurableSpace Ω] [Fintype V]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 3000000 in
theorem rawValueJet_converges_of_BS_HY_limit [Nonempty Ω]
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
      (fun n => (P.prod (uniformOrientedProposals (N (r n)) d)).map (fun z =>
        finiteValueJet (fun i => (w i).val)
          (D.rawCoordinateExtension (r n) E parameters.scale parameters.center z)
          (D.rawCoordinateDerivative (r n) E parameters.scale z)))
      ((massMarkedLaw ν parameters).map (fun z =>
        finiteValueJet (fun i => (w i).val) (massRawCoordinate ν hm parameters z)
          (massRawCoordinateDerivative ν hm parameters z))) := by
  intro parameters
  apply D.weakLaw_rawValueJet_mass_subsequence r hr P (by omega) ν hm parameters E parameters.center w
  · intro R
    apply D.paired_raw_values_converge_of_rawState_subsequence r hr P ν hm parameters E parameters.center w R
    exact D.microscopicRawState_converges_of_BS_HY_limit P hUniform hd HC K hK hbulk c0 hc1 hc2
      hcr hcs HL HM halpha hchi KBS BS E hEbulk hE hEBS gap hgap hwindow L hL HG r hr ν hm hscalar
      (pairedSpectral w R)
  · exact D.microscopic_anchor_uniform_tails_of_scalar_weak P r E parameters.scale parameters.center ν hscalar

end GeneralizedBulk.External.RegularSpectralData
