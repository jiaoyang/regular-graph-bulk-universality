import GeneralizedBulk.Graph.RawPairCompactness
import GeneralizedBulk.Gaussian.HeightCouplings

/-! The actual finite switched couplings construct normalization, rather than
assuming infinite mass or a pre-existing limiting switched process. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology ENNReal
namespace GeneralizedBulk.Graph
open GeneralizedBulk.Gaussian GeneralizedBulk.Counting GeneralizedSwitching Exterior

set_option maxHeartbeats 1800000 in
theorem normalization_of_actual_raw_height_limits
    (N : ℕ → ℕ) (hN : ∀ n,0 < N n) (hNlimit : Tendsto N atTop atTop)
    (d : ℕ) (hd : 0 < d) [∀ n,Nonempty (RegularGraph (N n) d)]
    (E center : ℝ) (parameters : Parameters)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (C1 C2 : ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hheight1 : ∀ Y : ℕ,(∫ s,‖anchoredNevanlinna s (normalizationHeight Y)‖ ∂ν) ≤ C1)
    (hiheight2 : ∀ Y : ℕ,Integrable (fun s => ‖anchoredNevanlinna s (normalizationHeight Y)‖^2) ν)
    (hheight2 : ∀ Y : ℕ,(∫ s,‖anchoredNevanlinna s (normalizationHeight Y)‖^2 ∂ν) ≤ C2)
    (hraw : ∀ Y : ℕ,External.WeakLawConverges
      (fun n => microscopicRawLaw (d := d) (hN n) E parameters.scale center parameters.scale_pos
        ⟨normalizationHeight Y,ne_of_gt (normalizationHeight_im_pos Y)⟩)
      (Measure.map (massRawHeight ν hm parameters Y) (massMarkedLaw ν parameters))) :
    Tendsto (fun Y : ℕ => ∫ s,‖anchoredNevanlinna s (normalizationHeight Y)-Complex.I‖ ∂ν) atTop (𝓝 0) ∧
      (∀ᵐ s ∂ν,s.val.1.measure Set.univ=∞) := by
  let height := fun Y => (⟨normalizationHeight Y,ne_of_gt (normalizationHeight_im_pos Y)⟩ : GraphNonreal)
  have hex (Y : ℕ) : ∃ (Q : ProbabilityMeasure RawPair) (r : ℕ → ℕ),StrictMono r ∧
      External.WeakLawConverges
        (fun n => microscopicRawPairLaw (d := d) (hN (r n)) E parameters.scale center parameters.scale_pos (height Y))
        (Q : Measure RawPair) ∧
      (Q : Measure RawPair).map Prod.fst=Measure.map (massRawHeight ν hm parameters Y) (massMarkedLaw ν parameters) ∧
      (Q : Measure RawPair).map Prod.snd=Measure.map (massRawHeight ν hm parameters Y) (massMarkedLaw ν parameters) := by
    letI : IsProbabilityMeasure (Measure.map (massRawHeight ν hm parameters Y) (massMarkedLaw ν parameters)) :=
      isProbabilityMeasure_map (measurable_massRawHeight ν hm parameters Y).aemeasurable
    exact microscopicRawPairLaw_subsequence_of_marginal_weak N hN d hd E parameters.scale center parameters.scale_pos
      (height Y) _ (hraw Y)
  choose Q r hr hweak hfst hsnd using hex
  have hinverse (Y : ℕ) : ∀ᵐ x ∂(Q Y : Measure RawPair),
      (1+x.1.2*switchIncrement)*(endpointPermutation*x.2.2*endpointPermutation)=x.1.2 := by
    exact microscopicRawPairLimit_inverse_free (fun n => N (r Y n)) (fun n => hN (r Y n))
      (hNlimit.comp (hr Y).tendsto_atTop) d hd E parameters.scale center parameters.scale_pos
      (height Y) (Q Y : Measure RawPair) (hweak Y)
  have hrank (Y : ℕ) : ∀ᵐ x ∂(Q Y : Measure RawPair),‖x.2.1-x.1.1‖ ≤ 4/((Y : ℝ)+1) := by
    letI : ∀ n,Nonempty (EdgePairState (N (r Y n)) d) := fun n => edgePairState_nonempty (hN (r Y n)) hd
    have h := microscopicRawPairLimit_rank_bound (fun n => N (r Y n)) (fun n => hN (r Y n)) d
      E parameters.scale center parameters.scale_pos (height Y) (Q Y : Measure RawPair) (hweak Y)
    have him : |(height Y).val.im|=(Y : ℝ)+1 := by
      simp only [height,normalizationHeight,Complex.mul_im,Complex.ofReal_re,Complex.I_im,
        mul_one,Complex.ofReal_im,Complex.I_re,mul_zero,add_zero]
      exact abs_of_pos (by positivity)
    simpa only [him] using h
  exact normalization_of_height_couplings ν hm parameters C1 C2 hC1 hC2 hheight1 hiheight2 hheight2
    (fun Y => (Q Y : Measure RawPair)) hfst hsnd hrank hinverse

end GeneralizedBulk.Graph
