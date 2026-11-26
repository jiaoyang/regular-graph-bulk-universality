import GeneralizedBulk.Graph.WindowBulkWeakConvergence
import GeneralizedBulk.Analysis.AnchoredWeakTightness

/-! Actual finite marked-window convergence from BS/HY, ordinary model
sampling, scalar weak convergence, and atom-free boundaries. No joint-law,
independence, mark moment, or tightness hypothesis remains. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Counting GeneralizedBulk.Analysis GeneralizedBulk.Gaussian
open GeneralizedBulk.KestenMcKay GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2500000 in
theorem windowMarkLaw_restrict_converges_of_BS_HY {m : ℕ} (hm : 0 < m) [Nonempty Ω]
    (r : ℕ → ℕ) (hr : StrictMono r)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (K : Set ℝ) (BS : BSQualitativeInput D P K)
    (HC : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast BS.degree_ge_three)))
    (J : Set ℝ) (hJ : IsCompact J) (hJbulk : ∀ E ∈ J,E^2 < 4*((d : ℝ)-1))
    (c0 : ℝ) (hcchannel : c0 < channelNoiseExponent (channelTheta 1 d))
    (hcrigidity : c0 < HC.rigidity_exponent) (hcsmall : c0 ≤ 1/16)
    (HL : HYLocalStarInput D P J c0 (treeGreenStar d (by exact_mod_cast BS.degree_ge_three)))
    (E sigma center R gap : ℝ) (hsigma : 0 < sigma) (hE : E ∈ K) (hgap : 0 < gap)
    (hwindow : Icc (E-gap) (E+gap) ⊆ J) (leaf : Fin d)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hscalar : WeakLawConverges
      (fun n => Measure.map (fun ω => D.microscopicCountingState (r n) ω E sigma center) P) ν)
    (hboundary : ∀ᵐ s ∂ν,s.val.1.measure {-R}=0 ∧ s.val.1.measure {R}=0)
    :
    WeakLawConverges
      (fun n => (D.windowMarkLaw P (r n) E sigma center R
        (D.paddedWindowSelection (r n) · E sigma (-R) R (fun _ => D.bulkPaddingIndex E m (r n)))).restrict
          (Prod.fst ⁻¹' {x : WindowData m | x.2.1=m}))
      (((Measure.map (windowData m (-R) R) ν).restrict {x : WindowData m | x.2.1=m}).prod
        (finiteMarkLaw (E/d) m)) := by
  letI : ∀ n,IsProbabilityMeasure (P.map (fun ω => D.microscopicCountingState (r n) ω E sigma center)) :=
    fun n => isProbabilityMeasure_map (D.measurable_microscopicCountingState (r n) E sigma center).aemeasurable
  have ht := isTightMeasureSet_anchored_of_weakLawConverges _ ν hscalar
  exact D.windowMarkLaw_restrict_weak_of_BS_HY hm r hr P hUniform K BS HC J hJ hJbulk c0 hcchannel hcrigidity hcsmall HL
    E sigma center R gap hsigma hE hgap hwindow leaf ν hscalar hboundary ht

end GeneralizedBulk.External.RegularSpectralData
