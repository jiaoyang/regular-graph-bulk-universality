import GeneralizedBulk.Graph.WindowMarkCompactness
import GeneralizedBulk.Graph.WindowBulkMarkLimitSubsequence
import GeneralizedBulk.Analysis.SubsequenceIdentification

/-! Actual retained-count marked-window laws converge to the constructed
Gaussian product law. Joint subsequences and their identification are proved,
rather than assumed as an independent marked-limit theorem. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Counting GeneralizedBulk.Analysis GeneralizedBulk.Gaussian
open GeneralizedBulk.KestenMcKay GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2500000 in
theorem windowMarkLaw_restrict_weak_of_BS_HY {m : ℕ} (hm : 0 < m) [Nonempty Ω]
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
    (hTight : IsTightMeasureSet (range (fun n => P.map (fun ω => D.microscopicCountingState (r n) ω E sigma center)))) :
    WeakLawConverges
      (fun n => (D.windowMarkLaw P (r n) E sigma center R
        (D.paddedWindowSelection (r n) · E sigma (-R) R (fun _ => D.bulkPaddingIndex E m (r n)))).restrict
          (Prod.fst ⁻¹' {x : WindowData m | x.2.1=m}))
      (((Measure.map (windowData m (-R) R) ν).restrict {x : WindowData m | x.2.1=m}).prod
        (finiteMarkLaw (E/d) m)) := by
  let selection := fun n ω => D.paddedWindowSelection n ω E sigma (-R) R (fun _ => D.bulkPaddingIndex E m n)
  have hselection (n i) : Measurable (fun ω => selection n ω i) :=
    D.measurable_paddedWindowSelection n E sigma (-R) R (fun _ => D.bulkPaddingIndex E m n)
      (fun i => D.measurable_bulkPaddingIndex E m n i) i
  let A : Set (WindowData m × ((Fin m × Fin 4) → ℝ)) := Prod.fst ⁻¹' {x | x.2.1=m}
  have hA : MeasurableSet A :=
    (measurable_fst.comp (measurable_snd.comp measurable_fst)) (measurableSet_singleton m)
  apply weakLaw_of_subsequence_identification
  intro q hq
  have hTight' : IsTightMeasureSet (range (fun n => P.map (fun ω => D.microscopicCountingState (r (q n)) ω E sigma center))) := by
    apply hTight.subset
    rintro _ ⟨n,rfl⟩
    exact ⟨q n,rfl⟩
  have hscalar' : WeakLawConverges
      (fun n => P.map (fun ω => D.microscopicCountingState (r (q n)) ω E sigma center)) ν := by
    intro G
    exact (hscalar G).comp hq.tendsto_atTop
  obtain ⟨t,ht,ρ,hjoint⟩ := D.windowMark_subsequence_of_tight_scalar hm P (by have hh := BS.degree_ge_three; omega)
    E sigma center R selection hselection (r ∘ q) hTight' ν hscalar' hboundary
  have hscalar'' : WeakLawConverges
      (fun n => P.map (fun ω => D.microscopicCountingState (r (q (t n))) ω E sigma center)) ν := by
    intro G
    exact (hscalar G).comp (hq.comp ht).tendsto_atTop
  have hidentified := D.windowMarkLimit_restrict_of_BS_HY_subsequence hm (r ∘ q ∘ t) (hr.comp (hq.comp ht))
    P hUniform K BS HC J hJ hJbulk c0 hcchannel hcrigidity hcsmall HL E sigma center R gap hsigma hE hgap hwindow leaf
    ν hscalar'' hboundary (ρ : Measure (WindowData m × ((Fin m × Fin 4) → ℝ)))
    (by simpa only [selection,Function.comp_def] using hjoint)
  refine ⟨t,ht,?_⟩
  intro Ψ
  let T : BoundedContinuousFunction (WindowData m × ((Fin m × Fin 4) → ℝ)) ℝ :=
    (countStratumIndicator m).compContinuous ⟨Prod.fst,continuous_fst⟩*Ψ
  have hweight (μ : Measure (WindowData m × ((Fin m × Fin 4) → ℝ))) :
      (∫ z,T z ∂μ) = ∫ z,Ψ z ∂μ.restrict A := by
    rw [← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards [] with z
    change countStratumIndicator m z.1*Ψ z=A.indicator (fun z => Ψ z) z
    have hI : countStratumIndicator m z.1=(if z.1.2.1=m then (1 : ℝ) else 0) := rfl
    rw [hI]
    by_cases hz : z.1.2.1=m <;> simp [A,Set.indicator,hz]
  have hlimit := hjoint T
  rw [hweight,hidentified] at hlimit
  simpa only [hweight,Function.comp_def] using hlimit

end GeneralizedBulk.External.RegularSpectralData
