import Mathlib

/-! Coordinatewise pushforwards of actual finite product measures. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace GeneralizedBulk.Analysis
variable {I : Type*} [Fintype I]

theorem map_pi_coordinatewise (μ : I → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (f : I → ℝ → ℝ) (hf : ∀ i, Measurable (f i)) :
    (Measure.pi μ).map (fun x i => f i (x i)) =
      Measure.pi (fun i => (μ i).map (f i)) := by
  symm
  apply Measure.pi_eq
  intro s hs
  have hmeas : Measurable (fun x : I → ℝ => fun i => f i (x i)) :=
    measurable_pi_lambda _ (fun i => (hf i).comp (measurable_pi_apply i))
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have he : (fun x : I → ℝ => fun i => f i (x i)) ⁻¹' univ.pi s =
      univ.pi (fun i => f i ⁻¹' s i) := by
    ext x
    simp
  rw [he, Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro i hi
  exact (Measure.map_apply (hf i) (hs i)).symm

end GeneralizedBulk.Analysis
