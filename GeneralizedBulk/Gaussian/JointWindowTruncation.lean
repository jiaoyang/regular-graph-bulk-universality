import GeneralizedBulk.Gaussian.GlobalWindow

/-! Joint L² window approximation from the actual first scalar-anchor moment. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology BigOperators
namespace GeneralizedBulk.Gaussian
variable {I S : Type*} [Countable I] [MeasurableSpace S]
variable (P : Measure S) [IsProbabilityMeasure P]
variable (X : S → PresentedState I) (hX : Measurable X)
variable (hm : Integrable (fun x => ‖(X x).scalar.val.2‖) P)

theorem constructedZ_slot_eq_L2_ae (parameters : Parameters) (v : ℂ × Bool) (i j : Fin 4) :
    ∀ᵐ x ∂P, (fun γ => constructedZ P X hX hm parameters x v γ i j) =ᵐ[iidLaw (markLaw parameters.p) I]
      (fun γ => presentedGaussianL2 parameters (X x).presentation v γ i j) := by
  filter_upwards [constructedAnchor_conditional_agreement P X hX hm parameters,
    constructedZ_eq_presented_ae P X hX hm parameters] with x ha heq
  have h1 : (fun γ => constructedZ P X hX hm parameters x v γ i j) =ᵐ[iidLaw (markLaw parameters.p) I]
      (fun γ => presentedGaussianField parameters (X x).presentation
        (fun η => presentedGlobalAnchorMatrix P X hX hm parameters (x,η)) v γ i j) :=
    heq.mono (fun γ h => congrFun (congrFun (h v) i) j)
  exact h1.trans (presentedGaussianField_slot_eq_L2_ae parameters (X x).presentation _ ha v i j)

/-- Uniform conditional control of the actual common analytic field minus
its jointly measurable finite-window projection. -/
theorem constructedWindow_conditional_bound (parameters : Parameters) (R : ℝ)
    (v : ℂ × Bool) (i j : Fin 4) :
    ∀ᵐ x ∂P,
      Integrable (fun γ => ‖constructedZ P X hX hm parameters x v γ i j -
        globalWindowField X parameters R v (x,γ) i j‖ ^ 2) (iidLaw (markLaw parameters.p) I) ∧
      (∫ γ, ‖constructedZ P X hX hm parameters x v γ i j -
        globalWindowField X parameters R v (x,γ) i j‖ ^ 2 ∂iidLaw (markLaw parameters.p) I) ≤
        (8 * (‖(parameters.scale : ℂ)‖ ^ 2 * coefficientSquareEnvelope v)) * ‖(X x).scalar.val.2‖ := by
  filter_upwards [constructedZ_slot_eq_L2_ae P X hX hm parameters v i j,
    constructedZ_memLp_two P X hX hm parameters v i j] with x heq hLp
  have hwindow : (fun γ => windowL2 parameters (X x).presentation R v i j γ) =ᵐ[iidLaw (markLaw parameters.p) I]
      (fun γ => globalWindowField X parameters R v (x,γ) i j) := by
    simpa only [globalWindowField_eq_windowField] using windowL2_coe_ae parameters (X x).presentation R v i j
  have hwLp : MemLp (fun γ => globalWindowField X parameters R v (x,γ) i j) 2
      (iidLaw (markLaw parameters.p) I) := (memLp_congr_ae hwindow).mp (Lp.memLp _)
  refine ⟨(hLp.sub hwLp).integrable_norm_pow',?_⟩
  have hAE : (fun γ => ‖constructedZ P X hX hm parameters x v γ i j -
      globalWindowField X parameters R v (x,γ) i j‖ ^ 2) =ᵐ[iidLaw (markLaw parameters.p) I]
      (fun γ => ‖presentedGaussianL2 parameters (X x).presentation v γ i j -
        windowField parameters (X x).presentation (-R) R v γ i j‖ ^ 2) := by
    filter_upwards [heq] with γ hγ
    rw [hγ,globalWindowField_eq_windowField]
  rw [integral_congr_ae hAE]
  exact windowField_second_moment_error_le_anchor parameters (X x).presentation R v i j

theorem constructedWindow_conditional_tendsto (parameters : Parameters)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (v : ℂ × Bool) (i j : Fin 4) :
    ∀ᵐ x ∂P, Tendsto (fun n => ∫ γ, ‖constructedZ P X hX hm parameters x v γ i j -
      globalWindowField X parameters (R n) v (x,γ) i j‖ ^ 2 ∂iidLaw (markLaw parameters.p) I)
      atTop (𝓝 0) := by
  filter_upwards [constructedZ_slot_eq_L2_ae P X hX hm parameters v i j] with x heq
  have hconv := windowField_second_moment_error_tendsto_zero parameters (X x).presentation R hR v i j
  convert hconv using 1
  funext n
  apply integral_congr_ae
  filter_upwards [heq] with γ hγ
  rw [hγ,globalWindowField_eq_windowField]

theorem constructedWindow_error_integrable (parameters : Parameters) (R : ℝ)
    (v : ℂ × Bool) (i j : Fin 4) :
    Integrable (fun z => ‖constructedField P X hX hm parameters v z i j -
      globalWindowField X parameters R v z i j‖ ^ 2) (P.prod (iidLaw (markLaw parameters.p) I)) := by
  let Q := iidLaw (markLaw parameters.p) I
  let F := fun z : S × (I → Fin 4 → ℝ) => ‖constructedField P X hX hm parameters v z i j -
    globalWindowField X parameters R v z i j‖ ^ 2
  let U := fun x => (8 * (‖(parameters.scale : ℂ)‖ ^ 2 * coefficientSquareEnvelope v)) * ‖(X x).scalar.val.2‖
  have hEval : Measurable (fun A : EndpointMatrix => A i j) :=
    (show Continuous (fun A : EndpointMatrix => A i j) from
      (continuous_apply j).comp (continuous_apply i)).measurable
  have hF : Measurable F := ((hEval.comp (measurable_constructedField P X hX hm parameters v)).sub
    (hEval.comp (measurable_globalWindowField X hX parameters R v))).norm.pow_const 2
  have hcond := constructedWindow_conditional_bound P X hX hm parameters R v i j
  have hi : Integrable (fun x => ∫ γ, F (x,γ) ∂Q) P := by
    apply (hm.const_mul _).mono' hF.aestronglyMeasurable.integral_prod_right'
    filter_upwards [hcond] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun γ => sq_nonneg _))]
    exact hx.2
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  refine ⟨hcond.mono (fun x hx => hx.1),?_⟩
  simpa only [F,norm_pow,norm_norm] using hi

theorem constructedWindow_joint_second_moment_bound (parameters : Parameters) (R : ℝ)
    (v : ℂ × Bool) (i j : Fin 4) :
    (∫ z, ‖constructedField P X hX hm parameters v z i j -
      globalWindowField X parameters R v z i j‖ ^ 2 ∂P.prod (iidLaw (markLaw parameters.p) I)) ≤
      (8 * (‖(parameters.scale : ℂ)‖ ^ 2 * coefficientSquareEnvelope v)) *
        (∫ x, ‖(X x).scalar.val.2‖ ∂P) := by
  have hi := constructedWindow_error_integrable P X hX hm parameters R v i j
  rw [integral_prod _ hi]
  exact (integral_mono_ae hi.integral_prod_left (hm.const_mul _)
    ((constructedWindow_conditional_bound P X hX hm parameters R v i j).mono
      (fun x hx => hx.2))).trans_eq (integral_const_mul _ _)

/-- The actual common analytic version converges jointly in L² to its
retained-window projections. Only the first scalar-anchor moment is used. -/
theorem constructedWindow_joint_second_moment_tendsto_zero (parameters : Parameters)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (v : ℂ × Bool) (i j : Fin 4) :
    Tendsto (fun n => ∫ z, ‖constructedField P X hX hm parameters v z i j -
      globalWindowField X parameters (R n) v z i j‖ ^ 2 ∂P.prod (iidLaw (markLaw parameters.p) I))
      atTop (𝓝 0) := by
  let Q := iidLaw (markLaw parameters.p) I
  let F := fun n (z : S × (I → Fin 4 → ℝ)) => ‖constructedField P X hX hm parameters v z i j -
    globalWindowField X parameters (R n) v z i j‖ ^ 2
  let U := fun x => (8 * (‖(parameters.scale : ℂ)‖ ^ 2 * coefficientSquareEnvelope v)) * ‖(X x).scalar.val.2‖
  have hi (n) : Integrable (F n) (P.prod Q) := constructedWindow_error_integrable P X hX hm parameters (R n) v i j
  have hbound (n) : ∀ᵐ x ∂P, ‖∫ γ, F n (x,γ) ∂Q‖ ≤ U x := by
    filter_upwards [constructedWindow_conditional_bound P X hX hm parameters (R n) v i j] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun γ => sq_nonneg _))]
    exact hx.2
  have ht := tendsto_integral_of_dominated_convergence U
    (fun n => (hi n).aestronglyMeasurable.integral_prod_right') (hm.const_mul _) hbound
    (constructedWindow_conditional_tendsto P X hX hm parameters R hR v i j)
  have ht0 : Tendsto (fun n => ∫ x, (∫ γ, F n (x,γ) ∂Q) ∂P) atTop (𝓝 0) := by
    simpa only [integral_zero] using ht
  convert ht0 using 1
  funext n
  exact integral_prod _ (hi n)

end GeneralizedBulk.Gaussian
