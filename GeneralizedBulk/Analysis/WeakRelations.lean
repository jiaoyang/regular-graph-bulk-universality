import GeneralizedBulk.Analysis.CappedMomentTransfer

/-! Continuous algebraic relations pass through weak limits even if they
hold only outside events whose probabilities vanish. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Analysis

/-- Capping the norm proves the relation in the limit without any
integrability assumption on the uncapped polynomial residual. -/
theorem weak_limit_continuous_zero_of_failure_probability
    {E V : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges μ ν) (r : E → V) (hr : Continuous r)
    (hfailure : Tendsto (fun n => (μ n).real {x | r x ≠ 0}) atTop (𝓝 0)) :
    ∀ᵐ x ∂ν, r x = 0 := by
  let F := nonnegativeCap (fun x => ‖r x‖) hr.norm (fun x => norm_nonneg _) 1 (by norm_num)
  have hA : MeasurableSet {x | r x ≠ 0} :=
    (isClosed_eq hr continuous_const).measurableSet.compl
  have hF0 (x : E) : 0 ≤ F x := le_min (norm_nonneg _) (by norm_num)
  have hbound (n : ℕ) : (∫ x, F x ∂μ n) ≤ (μ n).real {x | r x ≠ 0} := by
    have hp (x : E) : F x ≤ ({x | r x ≠ 0} : Set E).indicator (fun _ => (1 : ℝ)) x := by
      by_cases hx : r x = 0
      · simp [F,nonnegativeCap,hx]
      · rw [Set.indicator_of_mem hx]
        exact min_le_right _ _
    have hb := integral_mono (F.integrable (μ n)) ((integrable_const 1).indicator hA) hp
    simpa only [integral_indicator_const _ hA,smul_eq_mul,mul_one] using hb
  have hzero : Tendsto (fun n => ∫ x, F x ∂μ n) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg hF0) hbound hfailure
  have hInt : (∫ x, F x ∂ν) = 0 := tendsto_nhds_unique (hweak F) hzero
  have hAE : ∀ᵐ x ∂ν, F x = 0 :=
    (integral_eq_zero_iff_of_nonneg hF0 (F.integrable ν)).mp hInt
  filter_upwards [hAE] with x hx
  by_cases hne : r x = 0
  · exact hne
  · have hpos : 0 < F x := lt_min (norm_pos_iff.mpr hne) (by norm_num)
    linarith

theorem weak_limit_continuous_le_of_failure_probability
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges μ ν) (f : E → ℝ) (hf : Continuous f) (c : ℝ)
    (hfailure : Tendsto (fun n => (μ n).real {x | c < f x}) atTop (𝓝 0)) :
    ∀ᵐ x ∂ν, f x ≤ c := by
  have heq : {x : E | max (f x - c) 0 ≠ 0} = {x | c < f x} := by
    ext x
    simp only [Set.mem_setOf_eq,ne_eq,max_eq_right_iff,sub_nonpos,not_le]
  have hz := weak_limit_continuous_zero_of_failure_probability μ ν hweak
    (fun x => max (f x - c) 0) ((hf.sub continuous_const).max continuous_const)
    (by simpa only [heq] using hfailure)
  filter_upwards [hz] with x hx
  exact sub_nonpos.mp (max_eq_right_iff.mp hx)

theorem weakLaw_map
    {E F : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    (μ : ℕ → Measure E) (ν : Measure E) (hweak : External.WeakLawConverges μ ν)
    (f : E → F) (hf : Continuous f) :
    External.WeakLawConverges (fun n => Measure.map f (μ n)) (Measure.map f ν) := by
  intro G
  simp_rw [integral_map hf.measurable.aemeasurable G.continuous.measurable.aestronglyMeasurable]
  exact hweak (G.compContinuous ⟨f,hf⟩)

/-- A known limiting marginal identifies the marginal of any actual joint
weak subsequence. -/
theorem weak_limit_marginal_eq
    {E F : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] [HasOuterApproxClosed F]
    (μ : ℕ → Measure E) (ν : Measure E) [IsFiniteMeasure ν]
    (hweak : External.WeakLawConverges μ ν) (f : E → F) (hf : Continuous f)
    (ρ : Measure F) [IsFiniteMeasure ρ]
    (hmarginal : External.WeakLawConverges (fun n => Measure.map f (μ n)) ρ) :
    Measure.map f ν = ρ := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro G
  exact tendsto_nhds_unique (weakLaw_map μ ν hweak f hf G) (hmarginal G)

end GeneralizedBulk.Analysis
