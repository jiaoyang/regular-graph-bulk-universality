import GeneralizedBulk.Graph.BulkNormalization
import GeneralizedBulk.Graph.BulkResolventJetConvergence
import GeneralizedBulk.Graph.ExteriorJetConvergence
import GeneralizedBulk.Graph.BulkFullSequence
import GeneralizedBulk.Graph.BulkProofParameters
import GeneralizedBulk.Spectral.RegularParameterBoundary
import GeneralizedBulk.Graph.ProvedBSInput
import GeneralizedBulk.LocalLaw.ProvedMesoscopicInput

/-! The generic regular-graph bulk point-process proof with estimate inputs.

BS Gaussian-wave convergence is supplied by the merged, proved qualitative
classification. The imported local law constructs the mesoscopic trace input.
Coarse rigidity/delocalization, local-star comparison, and geometry are
parameters here; `ProvedRegularGraphUniversality` constructs all of them.
All entropy, moments, compactness, Gaussian marking, analytic flow,
normalization, exterior switching, and subsequence/full-sequence arguments
are proved. The beta-one loop characterization is reused from the vendored
repository, without an additional characterization assumption.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology ENNReal
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Counting GeneralizedBulk.Analysis GeneralizedBulk.Gaussian
open GeneralizedBulk.Exterior GeneralizedBulk.KestenMcKay GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 5000000 in
theorem identify_bulk_scalar_limit_of_HY
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
    (E : ℝ) (hEbulk : E^2 < 4*((d : ℝ)-1)) (hE : E ∈ Km)
    (gap : ℝ) (hgap : 0 < gap) (hwindow : Set.Icc (E-2*gap) (E+2*gap) ⊆ K)
    (L : ℕ) (hL : 2*gap ≤ (2 : ℝ)^L) (HG : HYGeometryInput D P)
    (r : ℕ → ℕ) (hr : StrictMono r)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hscalar : let parameters := Parameters.regular d E (by exact_mod_cast hd) hEbulk
      External.WeakLawConverges
        (fun n => P.map (fun ω => D.microscopicCountingState (r n) ω E parameters.scale parameters.center)) ν) :
    Measure.map (fun s : AnchoredCountingState => s.val.1) ν=sineOneLaw := by
  let parameters := Parameters.regular d E (by exact_mod_cast hd) hEbulk
  letI : Nonempty Ω := ProbabilityMeasure.nonempty (⟨P,inferInstance⟩ : ProbabilityMeasure Ω)
  have hEabs : |E| < 2*Real.sqrt (d-1 : ℝ) := by
    have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hnonneg : (0 : ℝ) ≤ (d : ℝ)-1 := by linarith
    apply (sq_lt_sq₀ (abs_nonneg E) (by positivity : (0 : ℝ) ≤ 2*Real.sqrt (d-1 : ℝ))).mp
    rw [sq_abs,mul_pow,Real.sq_sqrt hnonneg]
    norm_num
    exact hEbulk
  let KBS : Set ℝ := {E}
  have hEBS : E ∈ KBS := Set.mem_singleton E
  let BS := D.provedBSQualitativeInput P hUniform hd KBS isCompact_singleton (by
    intro x hx
    have hx' : x=E := Set.mem_singleton_iff.mp hx
    simpa only [hx'] using hEabs)
  have hscalar' : WeakLawConverges
      (fun n => P.map (fun ω => D.microscopicCountingState (r n) ω E parameters.scale parameters.center)) ν := hscalar
  have hmoms := D.HY_bulk_scalar_limit_moments hUniform hd HC K hK hbulk c0 hc1 hc2 hcr hcs
    HL HM hchi.le E hE gap hgap hwindow L hL parameters.scale parameters.center parameters.scale_pos r hr ν hscalar'
  have hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν := by
    simpa only [pow_one] using hmoms.1.norm_pow 1
  have hmass := (D.HY_bulk_scalar_limit_normalization P hUniform hd HC K hK hbulk c0 hc1 hc2 hcr hcs
    HL HM halpha hchi KBS BS E hEbulk hE hEBS gap hgap hwindow L hL HG r hr ν hscalar').2
  have hswitch : Measure.map (action GeneralizedSwitching.endpointPermutation)
      (Measure.map (massExterior ν hm parameters) (massMarkedLaw ν parameters)) =
      Measure.map (massExterior ν hm parameters) (massMarkedLaw ν parameters) := by
    apply D.massExterior_switching_of_rawJet_limits P hUniform (by omega) r hr ν hm parameters
      E parameters.center hmoms.2.1 hmass
    intro S
    exact D.rawValueJet_converges_of_BS_HY_limit P hUniform hd HC K hK hbulk c0 hc1 hc2 hcr hcs
      HL HM halpha hchi KBS BS E hEbulk hE hEBS gap hgap hwindow L hL HG r hr ν hm hscalar'
      (fun i : S => i.val)
  exact identify_of_mass_exterior_switching ν hm parameters
    (fun q => hmoms.1.norm_pow q) hmoms.2.1 hmass hswitch

/- The full sequence of the actual microscopic point-process laws converges
in the topology of locally finite counting measures, retaining multiplicities. -/
set_option maxHeartbeats 5000000 in
theorem bulk_universality_of_HY_inputs
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
    (E : ℝ) (hEbulk : E^2 < 4*((d : ℝ)-1)) (hE : E ∈ Km)
    (gap : ℝ) (hgap : 0 < gap) (hwindow : Set.Icc (E-2*gap) (E+2*gap) ⊆ K)
    (L : ℕ) (hL : 2*gap ≤ (2 : ℝ)^L) (HG : HYGeometryInput D P) :
    let parameters := Parameters.regular d E (by exact_mod_cast hd) hEbulk
    WeakLawConverges (fun n => P.map
      (fun ω => (D.microscopicCountingState n ω E parameters.scale parameters.center).val.1)) sineOneLaw := by
  intro parameters
  apply D.HY_full_sequence_of_subsequence_counting_identification hUniform hd HC K hK hbulk
    c0 hc1 hc2 hcr hcs HL HM hchi.le E hE gap hgap hwindow L hL
    parameters.scale parameters.center parameters.scale_pos
  intro r hr ν hscalar
  exact D.identify_bulk_scalar_limit_of_HY P hUniform hd HC K hK hbulk c0 hc1 hc2 hcr hcs
    HL HM halpha hchi E hEbulk hE gap hgap hwindow L hL HG r hr ν hscalar

/-- The final endpoint uses the imported, proved local law for its mesoscopic
trace estimate. Only the coarse, local-star and geometric HY records remain
as mathematical inputs. The mesoscopic exponent is chosen internally. -/
theorem bulk_universality_of_HY
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 3 ≤ d) (HC : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast hd)))
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1))
    (c0 : ℝ) (hc1 : c0 < channelNoiseExponent (channelTheta 1 d))
    (hc2 : c0 < channelNoiseExponent (channelTheta 2 d))
    (hcr : c0 < HC.rigidity_exponent) (hcs : c0 ≤ 1/16)
    (HL : HYLocalStarInput D P K c0 (treeGreenStar d (by exact_mod_cast hd)))
    (E : ℝ) (hEbulk : E^2 < 4*((d : ℝ)-1))
    (gap : ℝ) (hgap : 0 < gap) (hwindow : Set.Icc (E-2*gap) (E+2*gap) ⊆ K)
    (L : ℕ) (hL : 2*gap ≤ (2 : ℝ)^L) (HG : HYGeometryInput D P) :
    let parameters := Parameters.regular d E (by exact_mod_cast hd) hEbulk
    WeakLawConverges (fun n => P.map
      (fun ω => (D.microscopicCountingState n ω E parameters.scale parameters.center).val.1)) sineOneLaw := by
  obtain ⟨alpha, halpha0, halpha1, hchi⟩ :=
    exists_strict_mesoscopic_exponent d HC.rigidity_exponent HL.local_exponent c0
      HL.local_exponent_pos HL.height_range.1 hcr (by linarith [HL.height_range.2])
  let HM := D.provedHYMesoscopicInput P hUniform hd Set.univ alpha halpha0
  exact D.bulk_universality_of_HY_inputs P hUniform hd HC K hK hbulk c0 hc1 hc2 hcr hcs
    HL HM halpha1 hchi E hEbulk (Set.mem_univ E) gap hgap hwindow L hL HG

/-- Historical endpoint names remain aliases of the proved BS-free versions. -/
alias identify_bulk_scalar_limit_of_BS_HY := identify_bulk_scalar_limit_of_HY
alias bulk_universality_of_BS_HY := bulk_universality_of_HY

end GeneralizedBulk.External.RegularSpectralData
