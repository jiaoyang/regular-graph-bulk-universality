import GeneralizedBulk.Analysis.WeakRelations

/-! The almost-everywhere continuous mapping theorem, needed for literal
sorted window coordinates at atom-free deterministic cutoffs. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace GeneralizedBulk.Analysis

theorem weakLaw_map_of_ae_continuous
    {E F : Type*} [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F]
    (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges μ ν) (f : E → F) (hf : Measurable f)
    (hcont : ∀ᵐ x ∂ν, ContinuousAt f x) :
    External.WeakLawConverges (fun n => Measure.map f (μ n)) (Measure.map f ν) := by
  let laws : ℕ → ProbabilityMeasure E := fun n => ⟨μ n,inferInstance⟩
  let limit : ProbabilityMeasure E := ⟨ν,inferInstance⟩
  have hsource : Tendsto laws atTop (𝓝 limit) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hweak
  let mapped : ℕ → ProbabilityMeasure F := fun n => (laws n).map hf.aemeasurable
  let target : ProbabilityMeasure F := limit.map hf.aemeasurable
  have hmapped : Tendsto mapped atTop (𝓝 target) := by
    apply tendsto_of_forall_isOpen_le_liminf
    intro G hG
    let A := f ⁻¹' G
    have hAe : A =ᵐ[ν] interior A := by
      filter_upwards [hcont] with x hx
      apply propext
      constructor
      · intro h
        exact mem_interior_iff_mem_nhds.mpr (hx.preimage_mem_nhds (hG.mem_nhds h))
      · exact fun h => (interior_subset : interior A ⊆ A) h
    have hENN : (target : Measure F) G ≤
        atTop.liminf (fun n => (mapped n : Measure F) G) := by
      change (Measure.map f ν) G ≤ atTop.liminf (fun n => (Measure.map f (μ n)) G)
      simp_rw [Measure.map_apply hf hG.measurableSet]
      rw [measure_congr hAe]
      have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hsource (isOpen_interior : IsOpen (interior A))
      exact hlim.trans (liminf_le_liminf (Eventually.of_forall (fun n => measure_mono interior_subset)))
    have hb : atTop.IsBoundedUnder (· ≤ ·) (fun n : ℕ => mapped n G) := ⟨1,by simp⟩
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.ofNNReal_liminf hb.isCoboundedUnder_ge]
    simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hENN
  intro G
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmapped G

end GeneralizedBulk.Analysis
