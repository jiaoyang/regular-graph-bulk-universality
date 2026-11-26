import GeneralizedBulk.Gaussian.StratifiedConstruction
import GeneralizedBulk.Gaussian.JointWindowTruncation
import GeneralizedBulk.Analysis.StratumConvergence

/-! Actual finite-window approximation of the pre-normalization marked mixture. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.Gaussian
open Counting Analysis
variable (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
variable (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)

def massWindowField (parameters : Parameters) (R : ℝ) (v : ℂ × Bool) (z : MassMarkedSample ν) : EndpointMatrix :=
  globalWindowField (stratumPresentation z.1.val) parameters R v z.2

theorem measurable_massWindowField (parameters : Parameters) (R : ℝ) (v : ℂ × Bool) :
    Measurable (massWindowField ν parameters R v) := by
  apply measurable_sigma_of_sections
  intro i
  exact measurable_globalWindowField (stratumPresentation i.val) (measurable_stratumPresentation i.val) parameters R v

/-- Finite and infinite counting-mass strata both converge under their actual
mixed probability law, before normalization rules out the finite strata. -/
theorem massWindow_joint_second_moment_tendsto_zero (parameters : Parameters)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (v : ℂ × Bool) (i j : Fin 4) :
    Tendsto (fun n => ∫ z, ‖massCenteredField ν hm parameters v z i j -
      massWindowField ν parameters (R n) v z i j‖ ^ 2 ∂massMarkedLaw ν parameters)
      atTop (𝓝 0) := by
  let K : ℝ := 8 * (‖(parameters.scale : ℂ)‖ ^ 2 * coefficientSquareEnvelope v)
  let u : AnchoredCountingState → ℝ := fun s => K * ‖s.val.2‖
  let U := fun z : MassMarkedSample ν => u (massScalarState ν z)
  let F := fun n (z : MassMarkedSample ν) => ‖massCenteredField ν hm parameters v z i j -
    massWindowField ν parameters (R n) v z i j‖ ^ 2
  have hK : 0 ≤ K := by dsimp [K]; exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (coefficientSquareEnvelope_nonneg v))
  have hu : Measurable u := measurable_const.mul (measurable_snd.comp measurable_subtype_coe).norm
  have hiu : Integrable u ν := hm.const_mul K
  have hiU : Integrable U (massMarkedLaw ν parameters) := by
    have hi : Integrable u (Measure.map (massScalarState ν) (massMarkedLaw ν parameters)) := by
      rw [massMarkedLaw_scalar_marginal]
      exact hiu
    exact hi.comp_measurable (measurable_massScalarState ν)
  have hEval : Measurable (fun A : EndpointMatrix => A i j) :=
    (show Continuous (fun A : EndpointMatrix => A i j) from
      (continuous_apply j).comp (continuous_apply i)).measurable
  have hF (n) : Measurable (F n) :=
    ((hEval.comp (measurable_massCenteredField ν hm parameters v)).sub
      (hEval.comp (measurable_massWindowField ν parameters (R n) v))).norm.pow_const 2
  have hiUf (a : MassActive ν) : Integrable
      (fun z : MassState a.val × MassMarkSpace ν a => U ⟨a,z⟩)
      ((massStratumLaw ν a : Measure (MassState a.val)).prod (iidLaw (markLaw parameters.p) (MassLabels a.val))) := by
    have hi := integrable_conditionalSubtypeLaw ν (stratumSet massClass a.val)
      (measurable_massClass (measurableSet_singleton a.val)) a.property u hiu
    simpa only [mul_one] using hi.mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : MassMarkSpace ν a => (1 : ℝ))
        (iidLaw (markLaw parameters.p) (MassLabels a.val)))
  have hbound (n : ℕ) (a : MassActive ν) :
      (∫ z : MassState a.val × MassMarkSpace ν a, F n ⟨a,z⟩
        ∂(massStratumLaw ν a : Measure (MassState a.val)).prod (iidLaw (markLaw parameters.p) (MassLabels a.val))) ≤
      ∫ z : MassState a.val × MassMarkSpace ν a, U ⟨a,z⟩
        ∂(massStratumLaw ν a : Measure (MassState a.val)).prod (iidLaw (markLaw parameters.p) (MassLabels a.val)) := by
    have heq : (∫ z : MassState a.val × MassMarkSpace ν a, U ⟨a,z⟩
        ∂(massStratumLaw ν a : Measure (MassState a.val)).prod (iidLaw (markLaw parameters.p) (MassLabels a.val))) =
        K * (∫ s : MassState a.val, ‖s.val.val.2‖ ∂(massStratumLaw ν a : Measure (MassState a.val))) := by
      calc
        _ = ∫ s : MassState a.val, u s.val ∂(massStratumLaw ν a : Measure (MassState a.val)) := by
          simpa only [measureReal_univ_eq_one,one_smul] using
            integral_fun_fst (μ := (massStratumLaw ν a : Measure (MassState a.val)))
              (ν := iidLaw (markLaw parameters.p) (MassLabels a.val)) (fun s : MassState a.val => u s.val)
        _ = _ := integral_const_mul _ _
    rw [heq]
    simpa only [stratumPresentation_scalar] using
      constructedWindow_joint_second_moment_bound (massStratumLaw ν a : Measure (MassState a.val))
        (stratumPresentation a.val) (measurable_stratumPresentation a.val)
        (massStratum_anchor_integrable ν hm a) parameters (R n) v i j
  have hifibre (n : ℕ) (a : MassActive ν) : Integrable
      (fun z : MassState a.val × MassMarkSpace ν a => F n ⟨a,z⟩)
      ((massStratumLaw ν a : Measure (MassState a.val)).prod (iidLaw (markLaw parameters.p) (MassLabels a.val))) :=
    constructedWindow_error_integrable (massStratumLaw ν a : Measure (MassState a.val))
      (stratumPresentation a.val) (measurable_stratumPresentation a.val)
      (massStratum_anchor_integrable ν hm a) parameters (R n) v i j
  have hzero (a : MassActive ν) : Tendsto
      (fun n => ∫ z : MassState a.val × MassMarkSpace ν a, F n ⟨a,z⟩
        ∂(massStratumLaw ν a : Measure (MassState a.val)).prod (iidLaw (markLaw parameters.p) (MassLabels a.val)))
      atTop (𝓝 0) :=
    constructedWindow_joint_second_moment_tendsto_zero (massStratumLaw ν a : Measure (MassState a.val))
      (stratumPresentation a.val) (measurable_stratumPresentation a.val)
      (massStratum_anchor_integrable ν hm a) parameters R hR v i j
  exact integral_stratumMarkedLaw_tendsto_zero ν massClass measurable_massClass
    (MassMarkSpace ν) (fun a => iidLaw (markLaw parameters.p) (MassLabels a.val)) F U hF
    (hu.comp (measurable_massScalarState ν)) (fun n z => sq_nonneg _)
    (fun z => mul_nonneg hK (norm_nonneg _)) hiU hifibre hiUf hbound hzero

/-- Every actual mixed finite-window squared error is integrable; this is
proved from the conditional second moments and the scalar anchor moment. -/
theorem massWindow_errors_integrable (parameters : Parameters) (R : ℕ → ℝ)
    (v : ℂ × Bool) (i j : Fin 4) (n : ℕ) :
    Integrable (fun z => ‖massCenteredField ν hm parameters v z i j -
      massWindowField ν parameters (R n) v z i j‖ ^ 2) (massMarkedLaw ν parameters) := by
  let K : ℝ := 8 * (‖(parameters.scale : ℂ)‖ ^ 2 * coefficientSquareEnvelope v)
  let u : AnchoredCountingState → ℝ := fun s => K * ‖s.val.2‖
  let U := fun z : MassMarkedSample ν => u (massScalarState ν z)
  let F := fun n (z : MassMarkedSample ν) => ‖massCenteredField ν hm parameters v z i j -
    massWindowField ν parameters (R n) v z i j‖ ^ 2
  have hK : 0 ≤ K := by dsimp [K]; exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (coefficientSquareEnvelope_nonneg v))
  have hu : Measurable u := measurable_const.mul (measurable_snd.comp measurable_subtype_coe).norm
  have hiu : Integrable u ν := hm.const_mul K
  have hiU : Integrable U (massMarkedLaw ν parameters) := by
    have hi : Integrable u (Measure.map (massScalarState ν) (massMarkedLaw ν parameters)) := by
      rw [massMarkedLaw_scalar_marginal]
      exact hiu
    exact hi.comp_measurable (measurable_massScalarState ν)
  have hEval : Measurable (fun A : EndpointMatrix => A i j) :=
    (show Continuous (fun A : EndpointMatrix => A i j) from
      (continuous_apply j).comp (continuous_apply i)).measurable
  have hF (n) : Measurable (F n) :=
    ((hEval.comp (measurable_massCenteredField ν hm parameters v)).sub
      (hEval.comp (measurable_massWindowField ν parameters (R n) v))).norm.pow_const 2
  have hiUf (a : MassActive ν) : Integrable
      (fun z : MassState a.val × MassMarkSpace ν a => U ⟨a,z⟩)
      ((massStratumLaw ν a : Measure (MassState a.val)).prod (iidLaw (markLaw parameters.p) (MassLabels a.val))) := by
    have hi := integrable_conditionalSubtypeLaw ν (stratumSet massClass a.val)
      (measurable_massClass (measurableSet_singleton a.val)) a.property u hiu
    simpa only [mul_one] using hi.mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : MassMarkSpace ν a => (1 : ℝ))
        (iidLaw (markLaw parameters.p) (MassLabels a.val)))
  have hbound (n : ℕ) (a : MassActive ν) :
      (∫ z : MassState a.val × MassMarkSpace ν a, F n ⟨a,z⟩
        ∂(massStratumLaw ν a : Measure (MassState a.val)).prod (iidLaw (markLaw parameters.p) (MassLabels a.val))) ≤
      ∫ z : MassState a.val × MassMarkSpace ν a, U ⟨a,z⟩
        ∂(massStratumLaw ν a : Measure (MassState a.val)).prod (iidLaw (markLaw parameters.p) (MassLabels a.val)) := by
    have heq : (∫ z : MassState a.val × MassMarkSpace ν a, U ⟨a,z⟩
        ∂(massStratumLaw ν a : Measure (MassState a.val)).prod (iidLaw (markLaw parameters.p) (MassLabels a.val))) =
        K * (∫ s : MassState a.val, ‖s.val.val.2‖ ∂(massStratumLaw ν a : Measure (MassState a.val))) := by
      calc
        _ = ∫ s : MassState a.val, u s.val ∂(massStratumLaw ν a : Measure (MassState a.val)) := by
          simpa only [measureReal_univ_eq_one,one_smul] using
            integral_fun_fst (μ := (massStratumLaw ν a : Measure (MassState a.val)))
              (ν := iidLaw (markLaw parameters.p) (MassLabels a.val)) (fun s : MassState a.val => u s.val)
        _ = _ := integral_const_mul _ _
    rw [heq]
    simpa only [stratumPresentation_scalar] using
      constructedWindow_joint_second_moment_bound (massStratumLaw ν a : Measure (MassState a.val))
        (stratumPresentation a.val) (measurable_stratumPresentation a.val)
        (massStratum_anchor_integrable ν hm a) parameters (R n) v i j
  have hifibre (n : ℕ) (a : MassActive ν) : Integrable
      (fun z : MassState a.val × MassMarkSpace ν a => F n ⟨a,z⟩)
      ((massStratumLaw ν a : Measure (MassState a.val)).prod (iidLaw (markLaw parameters.p) (MassLabels a.val))) :=
    constructedWindow_error_integrable (massStratumLaw ν a : Measure (MassState a.val))
      (stratumPresentation a.val) (measurable_stratumPresentation a.val)
      (massStratum_anchor_integrable ν hm a) parameters (R n) v i j
  exact (integrable_stratumMarkedLaw_of_fiber_bound ν massClass measurable_massClass
    (MassMarkSpace ν) (fun a => iidLaw (markLaw parameters.p) (MassLabels a.val))
    (F n) U (hF n) (hu.comp (measurable_massScalarState ν)) (fun z => sq_nonneg _)
    (fun z => mul_nonneg hK (norm_nonneg _)) hiU (hifibre n) hiUf (hbound n)).1

end GeneralizedBulk.Gaussian
