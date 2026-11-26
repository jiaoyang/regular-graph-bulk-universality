import GeneralizedBulk.Graph.BulkCenteredFieldConvergence
import GeneralizedBulk.Graph.SpectralRawLimit
import GeneralizedBulk.Graph.NormalizationFromRawLimit
import GeneralizedBulk.Graph.BulkScalarLimit

/-! The normalization and infinite particle mass of every actual bulk scalar
limit follow from the constructed marked series and genuine finite switching. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology ENNReal
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Gaussian GeneralizedBulk.Analysis GeneralizedBulk.Counting
open GeneralizedBulk.KestenMcKay GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 4000000 in
theorem HY_bulk_scalar_limit_normalization
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
    (E : ℝ) (hEbulk : E^2 < 4*((d : ℝ)-1)) (hE : E ∈ Km) (hEBS : E ∈ KBS)
    (gap : ℝ) (hgap : 0 < gap) (hwindow : Set.Icc (E-2*gap) (E+2*gap) ⊆ K)
    (L : ℕ) (hL : 2*gap ≤ (2 : ℝ)^L) (HG : HYGeometryInput D P)
    (r : ℕ → ℕ) (hr : StrictMono r)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hscalar : let parameters := Parameters.regular d E (by exact_mod_cast hd) hEbulk
      External.WeakLawConverges
        (fun n => P.map (fun ω => D.microscopicCountingState (r n) ω E parameters.scale parameters.center)) ν) :
    Tendsto (fun Y : ℕ => ∫ s,‖anchoredNevanlinna s (normalizationHeight Y)-Complex.I‖ ∂ν) atTop (𝓝 0) ∧
      (∀ᵐ s ∂ν,s.val.1.measure Set.univ=∞) := by
  let parameters := Parameters.regular d E (by exact_mod_cast hd) hEbulk
  have hscalar' : External.WeakLawConverges
      (fun n => P.map (fun ω => D.microscopicCountingState (r n) ω E parameters.scale parameters.center)) ν := hscalar
  letI : Nonempty Ω := ProbabilityMeasure.nonempty (⟨P,inferInstance⟩ : ProbabilityMeasure Ω)
  have hmoms := D.HY_bulk_scalar_limit_moments hUniform hd HC K hK hbulk c0 hc1 hc2 hcr hcs
    HL HM hchi.le E hE gap hgap hwindow L hL parameters.scale parameters.center parameters.scale_pos r hr ν hscalar'
  have hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν := by
    simpa only [pow_one] using hmoms.1.norm_pow 1
  obtain ⟨constants,hconstants,hheight⟩ := hmoms.2.2
  have hheight1 (Y : ℕ) : (∫ s,‖anchoredNevanlinna s (normalizationHeight Y)‖ ∂ν) ≤ constants 1 := by
    simpa only [normalizationHeight,pow_one] using (hheight Y 1 (by norm_num)).2
  have hiheight2 (Y : ℕ) : Integrable (fun s => ‖anchoredNevanlinna s (normalizationHeight Y)‖^2) ν :=
    (hheight Y 2 (by norm_num)).1
  have hheight2 (Y : ℕ) : (∫ s,‖anchoredNevanlinna s (normalizationHeight Y)‖^2 ∂ν) ≤ constants 2 :=
    (hheight Y 2 (by norm_num)).2
  letI : ∀ n,Nonempty (RegularGraph (N (r n)) d) :=
    fun n => ⟨D.spectralRegularGraph (r n) (Classical.arbitrary Ω)⟩
  apply normalization_of_actual_raw_height_limits (fun n => N (r n)) (fun n => D.size_pos (r n))
    (D.size_tendsto.comp hr.tendsto_atTop) d (by omega) E parameters.center parameters ν hm
    (constants 1) (constants 2) (hconstants 1) (hconstants 2) hheight1 hiheight2 hheight2
  intro Y
  let wY : GraphNonreal := ⟨normalizationHeight Y,ne_of_gt (normalizationHeight_im_pos Y)⟩
  have hcentered := D.microscopicCenteredState_converges_of_BS_HY_limit P hUniform hd HC K hK hbulk
    c0 hc1 hc2 hcr hcs HL HM halpha hchi KBS BS E hE hEBS gap hgap hwindow L hL parameters.center parameters
    rfl HG r hr ν hm hscalar' (fun _ : Unit => wY)
  have hraw := D.microscopicRawState_converges_of_centered P E (by exact_mod_cast hd) hEbulk
    r hr (fun _ : Unit => wY) ν hm hcentered
  exact D.microscopicRawLaw_converges_of_rawState P hUniform (by omega) E parameters.center parameters r ν hm wY hraw

end GeneralizedBulk.External.RegularSpectralData
