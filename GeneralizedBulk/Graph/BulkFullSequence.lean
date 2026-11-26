import GeneralizedBulk.Graph.BulkScalarTightness
import GeneralizedBulk.Counting.FullSequence
import GeneralizedBulk.Main

/-! The actual graph counting laws converge along the full sequence once
all actual anchored weak subsequences have been identified. Tightness and
subsequence extraction are supplied by the proved HY/entropy/switching bounds. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology Classical ENNReal
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Analysis GeneralizedBulk.Gaussian GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Counting GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2000000 in
theorem HY_full_sequence_of_subsequence_counting_identification {P : Measure Ω} [IsProbabilityMeasure P]
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
    (hidentify : ∀ (r : ℕ → ℕ),StrictMono r →
      ∀ ν : ProbabilityMeasure AnchoredCountingState,
      WeakLawConverges (fun n => Measure.map
        (fun ω => D.microscopicCountingState (r n) ω E sigma center) P) ν →
      Measure.map (fun s : AnchoredCountingState => s.val.1) ν=sineOneLaw) :
    WeakLawConverges (fun n => Measure.map
      (fun ω => (D.microscopicCountingState n ω E sigma center).val.1) P) sineOneLaw := by
  have ht := (D.HY_bulk_anchor_tails_and_subsequence hUniform hd Hc K hK hbulk
    c0 hc1 hc2 hcr hcs H Hm hchi E hE gap hgap hwindow L hL sigma center hsigma).1
  let laws : ℕ → ProbabilityMeasure AnchoredCountingState := fun n =>
    ⟨Measure.map (fun ω => D.microscopicCountingState n ω E sigma center) P,
      isProbabilityMeasure_map (D.measurable_microscopicCountingState n E sigma center).aemeasurable⟩
  have htail : ∀ ε : ℝ≥0∞,0 < ε → ∃ B : ℝ,∀ n,
      (laws n : Measure AnchoredCountingState) {s | B < ‖s.val.2‖} ≤ ε := by
    intro ε hε
    obtain ⟨B,hB⟩ := ht ε hε
    refine ⟨B,fun n => ?_⟩
    change (Measure.map (fun ω => D.microscopicCountingState n ω E sigma center) P)
      {s | B < ‖s.val.2‖} ≤ ε
    have hs : MeasurableSet {s : AnchoredCountingState | B < ‖s.val.2‖} :=
      (isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val).norm).measurableSet
    rw [Measure.map_apply (D.measurable_microscopicCountingState n E sigma center) hs]
    exact hB n
  have hw := countingLaw_converges_of_anchor_tails_and_limit_identification laws sineOneLaw htail hidentify
  convert hw using 1
  funext n
  change Measure.map (fun ω => (D.microscopicCountingState n ω E sigma center).val.1) P =
    Measure.map (fun s : AnchoredCountingState => s.val.1)
      (Measure.map (fun ω => D.microscopicCountingState n ω E sigma center) P)
  rw [Measure.map_map (show Measurable (fun s : AnchoredCountingState => s.val.1) from
      measurable_fst.comp measurable_subtype_coe)
    (D.measurable_microscopicCountingState n E sigma center)]
  rfl

end GeneralizedBulk.External.RegularSpectralData
