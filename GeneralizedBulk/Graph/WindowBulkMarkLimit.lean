import GeneralizedBulk.Graph.WindowMarkLimit

/-! The actual BS/HY finite graph kernel identifies a joint marked-window
limit with the iid Gaussian product law on every retained-count stratum. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Counting GeneralizedBulk.Analysis GeneralizedBulk.Gaussian
open GeneralizedBulk.KestenMcKay GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2500000 in
theorem windowMarkLimit_restrict_of_BS_HY {m : ℕ} (hm : 0 < m) [Nonempty Ω]
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
      (fun n => Measure.map (fun ω => D.microscopicCountingState n ω E sigma center) P) ν)
    (hboundary : ∀ᵐ s ∂ν,s.val.1.measure {-R}=0 ∧ s.val.1.measure {R}=0)
    (ρ : Measure (WindowData m × ((Fin m × Fin 4) → ℝ))) [IsFiniteMeasure ρ]
    (hjoint : WeakLawConverges
      (fun n => D.windowMarkLaw P n E sigma center R
        (D.paddedWindowSelection n · E sigma (-R) R (fun _ => D.bulkPaddingIndex E m n))) ρ) :
    ρ.restrict (Prod.fst ⁻¹' {x : WindowData m | x.2.1=m}) =
      ((Measure.map (windowData m (-R) R) ν).restrict {x : WindowData m | x.2.1=m}).prod
        (finiteMarkLaw (E/d) m) := by
  let selection := fun n ω => D.paddedWindowSelection n ω E sigma (-R) R (fun _ => D.bulkPaddingIndex E m n)
  have hselection (n i) : Measurable (fun ω => selection n ω i) :=
    D.measurable_paddedWindowSelection n E sigma (-R) R (fun _ => D.bulkPaddingIndex E m n)
      (fun i => D.measurable_bulkPaddingIndex E m n i) i
  apply D.windowMarkLimit_restrict_of_kernel_factorization P (by have hh := BS.degree_ge_three; omega)
    E sigma center R selection hselection leaf ν hscalar hboundary ρ hjoint
  intro G F
  apply D.BS_window_count_factorization_of_bulk_entropy hm P hUniform K BS HC J hJ hJbulk c0 hcchannel hcrigidity hcsmall HL
    E sigma R gap hsigma hE hgap hwindow leaf F
    (fun n ω => (G (windowData m (-R) R (D.microscopicCountingState n ω E sigma center)) : ℂ)) _ ‖G‖ _
  · intro n
    exact (G.continuous.measurable.comp ((measurable_windowData m (-R) R).comp
      (D.measurable_microscopicCountingState n E sigma center))).complex_ofReal
  · intro n ω
    simpa only [Complex.norm_real] using G.norm_coe_le_norm (windowData m (-R) R (D.microscopicCountingState n ω E sigma center))

end GeneralizedBulk.External.RegularSpectralData
