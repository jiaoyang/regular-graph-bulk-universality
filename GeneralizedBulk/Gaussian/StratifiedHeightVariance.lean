import GeneralizedBulk.Gaussian.StratifiedConstruction
import GeneralizedBulk.Analysis.StratumMoments

/-! Sharp Gaussian height variance before infinite-particle normalization. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped BigOperators Topology
namespace GeneralizedBulk.Gaussian
open Counting Analysis
variable (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
variable (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)

/-- Sharp joint second moments of the actual mixed Gaussian field. Finite
and infinite particle strata obey one identical Poisson-height bound. -/
theorem massCenteredField_second_moment_poisson (parameters : Parameters)
    {w : ℂ} (hw : 0 < w.im) (i j : Fin 4) :
    Integrable (fun z => ‖massCenteredField ν hm parameters (w,false) z i j‖ ^ 2)
      (massMarkedLaw ν parameters) ∧
      (∫ z, ‖massCenteredField ν hm parameters (w,false) z i j‖ ^ 2
        ∂massMarkedLaw ν parameters) ≤
        (2 * ‖(parameters.scale : ℂ)‖ ^ 2 / w.im) *
          (∫ s, (anchoredNevanlinna s w).im ∂ν) := by
  let k : ℝ := 2 * ‖(parameters.scale : ℂ)‖ ^ 2 / w.im
  let u : AnchoredCountingState → ℝ := fun s => k * (anchoredNevanlinna s w).im
  have hscalar : Measurable (fun s : AnchoredCountingState => anchoredNevanlinna s w) :=
    (continuous_anchoredNevanlinna (ne_of_gt hw)).measurable
  have hiNorm := integrable_scalar_norm_of_anchor ν id measurable_id hm (ne_of_gt hw)
  have hiIm : Integrable (fun s : AnchoredCountingState => (anchoredNevanlinna s w).im) ν := by
    apply hiNorm.mono' (Complex.measurable_im.comp hscalar).aestronglyMeasurable
    exact Eventually.of_forall (fun s => Complex.abs_im_le_norm _)
  have hiu : Integrable u ν := hiIm.const_mul k
  have hu : Measurable u := measurable_const.mul (Complex.measurable_im.comp hscalar)
  have hu0 (s : AnchoredCountingState) : 0 ≤ u s := by
    exact mul_nonneg (by dsimp [k]; positivity) (anchoredNevanlinna_im_nonneg s hw)
  have hEval : Measurable (fun A : EndpointMatrix => A i j) :=
    (show Continuous (fun A : EndpointMatrix => A i j) from
      (continuous_apply j).comp (continuous_apply i)).measurable
  have hf : Measurable (fun z => ‖massCenteredField ν hm parameters (w,false) z i j‖ ^ 2) :=
    (hEval.comp (measurable_massCenteredField ν hm parameters (w,false))).norm.pow_const 2
  have hiuMixed : Integrable (fun z => u (massScalarState ν z)) (massMarkedLaw ν parameters) := by
    have hi : Integrable u (Measure.map (massScalarState ν) (massMarkedLaw ν parameters)) := by
      rw [massMarkedLaw_scalar_marginal]
      exact hiu
    exact hi.comp_measurable (measurable_massScalarState ν)
  have hiuf (a : MassActive ν) : Integrable (fun z : MassState a.val × MassMarkSpace ν a => u z.1.val)
      ((massStratumLaw ν a : Measure (MassState a.val)).prod
        (iidLaw (markLaw parameters.p) (MassLabels a.val))) := by
    have hi := integrable_conditionalSubtypeLaw ν (stratumSet massClass a.val)
      (measurable_massClass (measurableSet_singleton a.val)) a.property u hiu
    simpa only [mul_one] using hi.mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : MassMarkSpace ν a => (1 : ℝ))
        (iidLaw (markLaw parameters.p) (MassLabels a.val)))
  have hbound (a : MassActive ν) :
      (∫ z : MassState a.val × MassMarkSpace ν a,
        ‖massCenteredField ν hm parameters (w,false) ⟨a,z⟩ i j‖ ^ 2
        ∂(massStratumLaw ν a : Measure (MassState a.val)).prod
          (iidLaw (markLaw parameters.p) (MassLabels a.val))) ≤
      ∫ z : MassState a.val × MassMarkSpace ν a, u z.1.val
        ∂(massStratumLaw ν a : Measure (MassState a.val)).prod
          (iidLaw (markLaw parameters.p) (MassLabels a.val)) := by
    have heq : (∫ z : MassState a.val × MassMarkSpace ν a, u z.1.val
        ∂(massStratumLaw ν a : Measure (MassState a.val)).prod
          (iidLaw (markLaw parameters.p) (MassLabels a.val))) =
        k * (∫ s : MassState a.val, (anchoredNevanlinna s.val w).im
          ∂(massStratumLaw ν a : Measure (MassState a.val))) := by
      calc
        _ = ∫ s : MassState a.val, u s.val
            ∂(massStratumLaw ν a : Measure (MassState a.val)) := by
          simpa only [measureReal_univ_eq_one,one_smul] using
            (integral_fun_fst (μ := (massStratumLaw ν a : Measure (MassState a.val)))
              (ν := iidLaw (markLaw parameters.p) (MassLabels a.val))
              (fun s : MassState a.val => u s.val))
        _ = _ := integral_const_mul _ _
    rw [heq]
    have hb := constructedField_second_moment_poisson
      (massStratumLaw ν a : Measure (MassState a.val)) (stratumPresentation a.val)
      (measurable_stratumPresentation a.val) (massStratum_anchor_integrable ν hm a)
      parameters hw i j
    simpa only [massCenteredField,stratumPresentation_scalar,integral_const_mul] using hb
  have hb := integrable_stratumMarkedLaw_of_fiber_bound ν massClass measurable_massClass
    (MassMarkSpace ν) (fun a => iidLaw (markLaw parameters.p) (MassLabels a.val))
    (fun z => ‖massCenteredField ν hm parameters (w,false) z i j‖ ^ 2)
    (fun z => u (massScalarState ν z)) hf (hu.comp (measurable_massScalarState ν))
    (fun z => sq_nonneg _) (fun z => hu0 _) hiuMixed
    (fun a => constructedField_norm_sq_integrable_upper
      (massStratumLaw ν a : Measure (MassState a.val)) (stratumPresentation a.val)
      (measurable_stratumPresentation a.val) (massStratum_anchor_integrable ν hm a)
      parameters hw i j) hiuf hbound
  have hmap : (∫ z, u (massScalarState ν z) ∂massMarkedLaw ν parameters) = ∫ s, u s ∂ν := by
    rw [← integral_map (measurable_massScalarState ν).aemeasurable hu.aestronglyMeasurable,
      massMarkedLaw_scalar_marginal]
  refine ⟨hb.1,hb.2.trans_eq ?_⟩
  change (∫ z, u (massScalarState ν z) ∂massMarkedLaw ν parameters) = _
  rw [hmap]
  exact integral_const_mul _ _

theorem massCenteredField_entryEnvelope_square_integrable_upper (parameters : Parameters)
    {w : ℂ} (hw : 0 < w.im) :
    Integrable (fun z => Graph.entryEnvelope (massCenteredField ν hm parameters (w,false) z) ^ 2)
      (massMarkedLaw ν parameters) := by
  apply Graph.integrable_entryEnvelope_square
  · intro i j
    have hEval : Measurable (fun A : EndpointMatrix => A i j) :=
      (show Continuous (fun A : EndpointMatrix => A i j) from
        (continuous_apply j).comp (continuous_apply i)).measurable
    exact (hEval.comp (measurable_massCenteredField ν hm parameters (w,false))).aestronglyMeasurable
  · intro i j
    exact (massCenteredField_second_moment_poisson ν hm parameters hw i j).1

/-- The pre-normalization mixed Gaussian fluctuation vanishes at imaginary
infinity in genuine joint L² whenever the scalar heights have bounded first
moments. No particle-number or infinite-mass premise is used. -/
theorem massCenteredField_entryEnvelope_square_tendsto_zero (parameters : Parameters)
    (C : ℝ) (hC : 0 ≤ C)
    (hheight : ∀ n : ℕ, (∫ s : AnchoredCountingState, ‖anchoredNevanlinna s
      ((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I)‖ ∂ν) ≤ C) :
    Tendsto (fun n : ℕ => ∫ z, Graph.entryEnvelope
      (massCenteredField ν hm parameters
        (((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I),false) z) ^ 2
      ∂massMarkedLaw ν parameters) atTop (𝓝 0) := by
  have hbound (n : ℕ) : (∫ z, Graph.entryEnvelope
      (massCenteredField ν hm parameters
        (((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I),false) z) ^ 2
      ∂massMarkedLaw ν parameters) ≤
      512 * ‖(parameters.scale : ℂ)‖ ^ 2 * C / ((n : ℝ) + 1) := by
    let w : ℂ := (((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I
    have hw : 0 < w.im := by dsimp [w]; simp; positivity
    let Z := massCenteredField ν hm parameters (w,false)
    have hZ (i j : Fin 4) : AEStronglyMeasurable (fun z => Z z i j)
        (massMarkedLaw ν parameters) := by
      have hEval : Measurable (fun A : EndpointMatrix => A i j) :=
        (show Continuous (fun A : EndpointMatrix => A i j) from
          (continuous_apply j).comp (continuous_apply i)).measurable
      exact (hEval.comp (measurable_massCenteredField ν hm parameters (w,false))).aestronglyMeasurable
    have hiZ (i j : Fin 4) : Integrable (fun z => ‖Z z i j‖ ^ 2)
        (massMarkedLaw ν parameters) :=
      (massCenteredField_second_moment_poisson ν hm parameters hw i j).1
    have hiNorm := integrable_scalar_norm_of_anchor ν id measurable_id hm (ne_of_gt hw)
    have hscalar : Measurable (fun s : AnchoredCountingState => anchoredNevanlinna s w) :=
      (continuous_anchoredNevanlinna (ne_of_gt hw)).measurable
    have hiIm : Integrable (fun s : AnchoredCountingState => (anchoredNevanlinna s w).im) ν := by
      apply hiNorm.mono' (Complex.measurable_im.comp hscalar).aestronglyMeasurable
      exact Eventually.of_forall (fun s => Complex.abs_im_le_norm _)
    have hIm : (∫ s : AnchoredCountingState, (anchoredNevanlinna s w).im ∂ν) ≤ C :=
      (integral_mono hiIm hiNorm (fun s => Complex.im_le_norm _)).trans (hheight n)
    have hb (i j : Fin 4) : (∫ z, ‖Z z i j‖ ^ 2 ∂massMarkedLaw ν parameters) ≤
        (2 * ‖(parameters.scale : ℂ)‖ ^ 2 / w.im) * C :=
      (massCenteredField_second_moment_poisson ν hm parameters hw i j).2.trans
        (mul_le_mul_of_nonneg_left hIm (by positivity))
    calc
      _ ≤ 16 * (∑ i, ∑ j, ∫ z, ‖Z z i j‖ ^ 2 ∂massMarkedLaw ν parameters) :=
        Graph.integral_entryEnvelope_square_le _ Z hZ hiZ
      _ ≤ 16 * (∑ _i : Fin 4, ∑ _j : Fin 4,
          (2 * ‖(parameters.scale : ℂ)‖ ^ 2 / w.im) * C) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16)
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))
      _ = _ := by dsimp [w]; simp; ring
  have hzero : Tendsto (fun n : ℕ => 512 * ‖(parameters.scale : ℂ)‖ ^ 2 * C /
      ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (512 * ‖(parameters.scale : ℂ)‖ ^ 2 * C)
  exact squeeze_zero (fun n => integral_nonneg (fun z => sq_nonneg _)) hbound hzero

end GeneralizedBulk.Gaussian
