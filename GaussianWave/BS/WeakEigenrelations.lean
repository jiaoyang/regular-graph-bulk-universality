import GaussianWave.BS.SecondMomentTightness

/-! Almost eigenrelations pass to actual weak limits using bounded
continuous residual caps. No Gaussianity or moment preservation premise
is needed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace GaussianWave.BS

theorem weak_limit_zero_of_residual_second
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → Measure E) (ν : Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (hweak : WeakLawConverges μ ν) (r : E → ℝ) (hr : Continuous r)
    (hi : ∀ n, Integrable (fun x => r x ^ 2) (μ n))
    (hres : Tendsto (fun n => ∫ x, r x ^ 2 ∂μ n) atTop (𝓝 0)) :
    ∀ᵐ x ∂ν, r x = 0 := by
  let F : E →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min (r x ^ 2) 1) ((hr.pow 2).min continuous_const) 1 (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) (by norm_num))]
      exact min_le_right _ _)
  have hF0 (x) : 0 ≤ F x := le_min (sq_nonneg _) (by norm_num)
  have hle (n) : (∫ x, F x ∂μ n) ≤ ∫ x, r x ^ 2 ∂μ n :=
    integral_mono (F.integrable _) (hi n) (fun x => min_le_left _ _)
  have hzero := squeeze_zero (fun n => integral_nonneg hF0) hle hres
  have hInt : (∫ x, F x ∂ν) = 0 := tendsto_nhds_unique (hweak F) hzero
  have hAE := (integral_eq_zero_iff_of_nonneg hF0 (F.integrable ν)).mp hInt
  filter_upwards [hAE] with x hx
  change F x = 0 at hx
  have he : r x ^ 2 = 0 := by
    by_contra he
    have hpos : 0 < F x := lt_min (lt_of_le_of_ne (sq_nonneg _) (Ne.symm he)) (by norm_num)
    linarith
  exact sq_eq_zero_iff.mp he

theorem weak_limit_zero_of_continuous_failure_probability
    {E V : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup V]
    (μ : ℕ → Measure E) (ν : Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (hweak : WeakLawConverges μ ν) (r : E → V) (hr : Continuous r)
    (hfailure : Tendsto (fun n => (μ n).real {x | r x ≠ 0}) atTop (𝓝 0)) :
    ∀ᵐ x ∂ν, r x = 0 := by
  let F : E →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min ‖r x‖ 1) (hr.norm.min continuous_const) 1 (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (norm_nonneg _) (by norm_num))]
      exact min_le_right _ _)
  have hA : MeasurableSet {x | r x ≠ 0} := (isClosed_eq hr continuous_const).measurableSet.compl
  have hF0 (x) : 0 ≤ F x := le_min (norm_nonneg _) (by norm_num)
  have hle (n) : (∫ x, F x ∂μ n) ≤ (μ n).real {x | r x ≠ 0} := by
    have hpoint (x) : F x ≤ ({x | r x ≠ 0} : Set E).indicator (fun _ => (1 : ℝ)) x := by
      by_cases hx : r x = 0
      · simp [F, hx]
      · rw [Set.indicator_of_mem hx]
        exact min_le_right _ _
    have hh := integral_mono (F.integrable _) ((integrable_const 1 (μ := μ n)).indicator hA) hpoint
    simpa only [integral_indicator_const _ hA, smul_eq_mul, mul_one] using hh
  have hzero := squeeze_zero (fun n => integral_nonneg hF0) hle hfailure
  have hInt : (∫ x, F x ∂ν) = 0 := tendsto_nhds_unique (hweak F) hzero
  have hAE := (integral_eq_zero_iff_of_nonneg hF0 (F.integrable ν)).mp hInt
  filter_upwards [hAE] with x hx
  change F x = 0 at hx
  by_contra he
  have hpos : 0 < F x := lt_min (norm_pos_iff.mpr he) (by norm_num)
  linarith

end GaussianWave.BS
