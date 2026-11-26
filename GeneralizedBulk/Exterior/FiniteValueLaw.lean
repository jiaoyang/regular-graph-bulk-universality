import GeneralizedBulk.Analysis.FiniteMarginalUniqueness
import GeneralizedBulk.Exterior.JetLift

/-! Literal function-space exterior symmetry follows from joint finite
spectral laws of both exterior coordinates. -/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.Exterior

def finiteValueEvaluation {I : Type*} (w : I → NonrealSpectral) (z : ValueState) :
    I → (ℂ × Mat) := fun i => (z.1 (w i),z.2 (w i))

theorem measurable_finiteValueEvaluation {I : Type*} (w : I → NonrealSpectral) :
    Measurable (finiteValueEvaluation w) :=
  measurable_pi_lambda _ (fun i =>
    ((measurable_pi_apply (w i)).comp measurable_fst).prodMk
      ((measurable_pi_apply (w i)).comp measurable_snd))

theorem value_switching_of_finite_joint_laws (μ : Measure ValueState) [IsFiniteMeasure μ]
    (h : ∀ S : Finset NonrealSpectral,
      Measure.map (fun z => finiteValueEvaluation (fun i : S => i.val)
        (action GeneralizedSwitching.endpointPermutation z)) μ =
      Measure.map (finiteValueEvaluation (fun i : S => i.val)) μ) :
    Measure.map (action GeneralizedSwitching.endpointPermutation) μ=μ := by
  apply Analysis.measure_prod_pi_eq_of_finite_joint_marginals
  intro S
  change Measure.map (finiteValueEvaluation (fun i : S => i.val))
    (Measure.map (action GeneralizedSwitching.endpointPermutation) μ) =
      Measure.map (finiteValueEvaluation (fun i : S => i.val)) μ
  rw [Measure.map_map (measurable_finiteValueEvaluation (fun i : S => i.val))
    (measurable_action GeneralizedSwitching.endpointPermutation)]
  exact h S

end GeneralizedBulk.Exterior
