import Mathlib

/-! Actual conditional nonnegative moment bounds on a good event imply
integrability and the same joint moment bound, without assumptions on the
bad-event values. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace GeneralizedBulk.Analysis
variable {S T V : Type*} [MeasurableSpace S] [MeasurableSpace T]

theorem integrableOn_prod_good_of_fiber_bound
    (P : Measure S) [IsProbabilityMeasure P] (Q : Measure T) [IsProbabilityMeasure Q]
    (good : Set S) (hgood : MeasurableSet good) (f : S × T → ℝ) (hf : Measurable f)
    (hpos : ∀ z,0 ≤ f z) (M : ℝ) (hM : 0 ≤ M)
    (hsection : ∀ s ∈ good,Integrable (fun t => f (s,t)) Q)
    (hbound : ∀ s ∈ good,(∫ t,f (s,t) ∂Q) ≤ M) :
    IntegrableOn f (good ×ˢ univ) (P.prod Q) ∧
      (∫ z in good ×ˢ univ,f z ∂P.prod Q) ≤ M := by
  let Pg := P.restrict good
  have hmeas : AEStronglyMeasurable f (Pg.prod Q) := hf.aestronglyMeasurable
  have hs : ∀ᵐ s ∂Pg,Integrable (fun t => f (s,t)) Q := by
    filter_upwards [ae_restrict_mem hgood] with s hs
    exact hsection s hs
  have hiinner : Integrable (fun s => ∫ t,‖f (s,t)‖ ∂Q) Pg := by
    apply (integrable_const M).mono' hmeas.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem hgood] with s hs
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun t => norm_nonneg _))]
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hpos _)] using hbound s hs
  have hi : Integrable f (Pg.prod Q) := (integrable_prod_iff hmeas).mpr ⟨hs,hiinner⟩
  have hjoint : (∫ z,f z ∂Pg.prod Q) ≤ M := by
    rw [integral_prod f hi]
    have hii := hi.integral_norm_prod_left
    have he (s : S) : (∫ t,‖f (s,t)‖ ∂Q) = ∫ t,f (s,t) ∂Q := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact Real.norm_of_nonneg (hpos (s,t))
    simp_rw [he] at hii
    have hinner := integral_mono_ae hii (integrable_const M)
      (show ∀ᵐ s ∂Pg,(∫ t,f (s,t) ∂Q) ≤ M from by
        filter_upwards [ae_restrict_mem hgood] with s hs
        exact hbound s hs)
    simp only [integral_const,smul_eq_mul] at hinner
    have hpe : Pg univ ≤ 1 := by
      dsimp [Pg]
      rw [Measure.restrict_apply MeasurableSet.univ,univ_inter]
      simpa only [measure_univ] using (measure_mono (subset_univ good) : P good ≤ P univ)
    have hp : Pg.real univ ≤ 1 := by
      simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hpe
    exact hinner.trans (by nlinarith)
  simpa only [Pg,Measure.restrict_prod_eq_prod_univ] using And.intro hi hjoint

theorem product_good_failure_mass
    (P : Measure S) [IsProbabilityMeasure P] (Q : Measure T) [IsProbabilityMeasure Q]
    (good : Set S) :
    (P.prod Q).real (good ×ˢ univ)ᶜ = P.real goodᶜ := by
  have he : (good ×ˢ (univ : Set T))ᶜ = goodᶜ ×ˢ univ := by ext z; simp
  rw [he,measureReal_def,Measure.prod_prod]
  simp only [measure_univ,mul_one,measureReal_def]

theorem product_scalar_map {V : Type*} [MeasurableSpace V]
    (P : Measure S) (Q : Measure T) [IsProbabilityMeasure Q] (X : S → V) (hX : Measurable X) :
    (P.prod Q).map (fun z => X z.1) = P.map X := by
  change (P.prod Q).map (X ∘ Prod.fst) = _
  rw [← Measure.map_map hX measurable_fst,Measure.map_fst_prod,measure_univ,one_smul]

end GeneralizedBulk.Analysis
