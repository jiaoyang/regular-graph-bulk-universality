import GeneralizedBulk.Analysis.GoodFiberMoments

/-! Variable conditional bounds integrate on a genuine scalar good event. -/
noncomputable section
open MeasureTheory Filter Set
namespace GeneralizedBulk.Analysis
variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

theorem integrableOn_prod_good_of_fiber_integral_bound
    (P : Measure S) [IsProbabilityMeasure P] (Q : Measure T) [IsProbabilityMeasure Q]
    (good : Set S) (hgood : MeasurableSet good) (f : S × T → ℝ) (hf : Measurable f)
    (hpos : ∀ z,0 ≤ f z) (g : S → ℝ) (hg : Integrable g P)
    (hsection : ∀ s ∈ good,Integrable (fun t => f (s,t)) Q)
    (hbound : ∀ s ∈ good,(∫ t,f (s,t) ∂Q) ≤ g s) :
    IntegrableOn f (good ×ˢ univ) (P.prod Q) ∧
      (∫ z in good ×ˢ univ,f z ∂P.prod Q) ≤ ∫ s in good,g s ∂P := by
  let Pg := P.restrict good
  have hmeas : AEStronglyMeasurable f (Pg.prod Q) := hf.aestronglyMeasurable
  have hs : ∀ᵐ s ∂Pg,Integrable (fun t => f (s,t)) Q := by
    filter_upwards [ae_restrict_mem hgood] with s hs
    exact hsection s hs
  have hiinner : Integrable (fun s => ∫ t,‖f (s,t)‖ ∂Q) Pg := by
    apply hg.integrableOn.mono' hmeas.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem hgood] with s hs
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun t => norm_nonneg _))]
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hpos _)] using hbound s hs
  have hi : Integrable f (Pg.prod Q) := (integrable_prod_iff hmeas).mpr ⟨hs,hiinner⟩
  have hjoint : (∫ z,f z ∂Pg.prod Q) ≤ ∫ s,g s ∂Pg := by
    rw [integral_prod f hi]
    apply integral_mono_ae hi.integral_prod_left hg.integrableOn
    filter_upwards [ae_restrict_mem hgood] with s hs
    exact hbound s hs
  simpa only [Pg,Measure.restrict_prod_eq_prod_univ] using And.intro hi hjoint

end GeneralizedBulk.Analysis
