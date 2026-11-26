import GaussianWave.Foundation

/-! The bounded-continuous-test convention itself forces a weak limit of
probability laws to have total mass one. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GaussianWave.BS

theorem weakLawConverges_isProbabilityMeasure {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : ℕ → Measure X) [∀ n,IsProbabilityMeasure (μ n)] (ν : Measure X)
    (h : WeakLawConverges μ ν) : IsProbabilityMeasure ν := by
  have hc := h (BoundedContinuousFunction.const X (1 : ℝ))
  change Tendsto (fun n => ∫ _ : X,(1 : ℝ) ∂μ n) atTop (𝓝 (∫ _ : X,(1 : ℝ) ∂ν)) at hc
  have htest : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (∫ _ : X,(1 : ℝ) ∂ν)) := by
    simpa only [integral_const,measureReal_univ_eq_one,
      smul_eq_mul,one_mul] using hc
  have hm : (∫ _ : X,(1 : ℝ) ∂ν)=1 := tendsto_nhds_unique htest tendsto_const_nhds
  constructor
  apply (ENNReal.toReal_eq_one_iff _).mp
  simpa only [integral_const,smul_eq_mul,mul_one,measureReal_def] using hm

end GaussianWave.BS
