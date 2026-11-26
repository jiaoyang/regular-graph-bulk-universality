import Mathlib

/-! Finite real vector laws are determined by all linear characteristic integrals. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.Gaussian

theorem measure_eq_of_linear_characteristic
    {ι : Type*} [Fintype ι]
    (μ ν : Measure (ι → ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ι → ℝ,
      (∫ x, Complex.exp ((↑(∑ i, t i * x i) : ℂ) * Complex.I) ∂μ) =
      (∫ x, Complex.exp ((↑(∑ i, t i * x i) : ℂ) * Complex.I) ∂ν)) :
    μ = ν := by
  let e := EuclideanSpace.measurableEquiv ι
  apply MeasurableEquiv.map_measurableEquiv_injective e.symm
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply, charFun_apply]
  have hc : Continuous (fun x : EuclideanSpace ℝ ι =>
      Complex.exp ((↑(@inner ℝ _ _ x t) : ℂ) * Complex.I)) := by fun_prop
  rw [integral_map e.symm.measurable.aemeasurable hc.stronglyMeasurable.aestronglyMeasurable,
    integral_map e.symm.measurable.aemeasurable hc.stronglyMeasurable.aestronglyMeasurable]
  simpa [PiLp.inner_apply, mul_comm] using h (fun i => t i)

end GeneralizedBulk.Gaussian
