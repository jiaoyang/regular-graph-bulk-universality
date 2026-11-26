import GeneralizedBulk.Gaussian.GlobalConstruction
import GeneralizedBulk.Analysis.NoLinearTerm
import GeneralizedBulk.Matrix.EntryEnvelope
import GeneralizedBulk.Analysis.FiberProducts

/-!
# Sharp Gaussian fluctuation decay at imaginary infinity

The actual orthogonal quadratic-mark series has variance bounded by its
Poisson coefficient sum. The sum is controlled by Im s(w)/Im w, giving the
height decay used before matrix inversion and normalization.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped BigOperators Topology
namespace GeneralizedBulk.Gaussian
variable {I : Type*} [Countable I] {s : AnchoredCountingState}

/-- The coefficient square sum has the sharp actual Poisson-height bound. -/
theorem presented_coefficient_square_sum_le_poisson
    (p : ParticlePresentation s I) (sigma : ℂ) {w : ℂ} (hw : 0 < w.im) :
    (∑' i, ‖sigma * particleCoefficient (p.location i) (w,false)‖ ^ 2) ≤
      ‖sigma‖ ^ 2 * ((anchoredNevanlinna s w).im / w.im) := by
  have heq (x : ℝ) : ‖particleCoefficient x (w,false)‖ ^ 2 =
      (Complex.normSq ((x : ℂ) - w))⁻¹ := by
    have hc : particleCoefficient x (w,false) = ((x : ℂ) - w)⁻¹ := by
      simp [particleCoefficient,ne_of_gt hw]
    rw [hc,← Complex.normSq_eq_norm_sq,Complex.normSq_inv]
  have hsum : (∑' i, ‖sigma * particleCoefficient (p.location i) (w,false)‖ ^ 2) =
      ‖sigma‖ ^ 2 * (∫ x, ‖particleCoefficient x (w,false)‖ ^ 2 ∂s.val.1.measure) := by
    simp only [norm_mul,mul_pow,tsum_mul_left]
    rw [(p.hasSum_observable (integrable_particleCoefficient_sq s (w,false))).tsum_eq]
  have hpoisson : (∫ x, w.im / Complex.normSq ((x : ℂ) - w) ∂s.val.1.measure) =
      w.im * (∫ x, ‖particleCoefficient x (w,false)‖ ^ 2 ∂s.val.1.measure) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by dsimp only; rw [heq]; ring)
  have him := anchoredNevanlinna_im_eq s (ne_of_gt hw)
  rw [hpoisson] at him
  have hbound : (∫ x, ‖particleCoefficient x (w,false)‖ ^ 2 ∂s.val.1.measure) ≤
      (anchoredNevanlinna s w).im / w.im := by
    rw [le_div_iff₀ hw]
    have hlin := mul_nonneg hw.le (anchoredLinearCoefficient_nonneg s)
    nlinarith only [him,hlin]
  rw [hsum]
  exact mul_le_mul_of_nonneg_left hbound (sq_nonneg _)

/-- Sharp variance for the actual L² marked series at every upper spectral
point. The affine coefficient, if present, only improves the bound. -/
theorem presentedGaussianL2_second_moment_poisson (parameters : Parameters)
    (p : ParticlePresentation s I) {w : ℂ} (hw : 0 < w.im) (i j : Fin 4) :
    (∫ γ, ‖presentedGaussianL2 parameters p (w,false) γ i j‖ ^ 2
      ∂iidLaw (markLaw parameters.p) I) ≤
      (2 * ‖(parameters.scale : ℂ)‖ ^ 2 / w.im) * (anchoredNevanlinna s w).im := by
  have hb := integral_norm_sq_l2Series_le (iidLaw (markLaw parameters.p) I)
    (fun n => markQuadraticLp parameters.p n i j)
    (fun n => (parameters.scale : ℂ) * particleCoefficient (p.location n) (w,false)) 2
    (fun n m hnm => markQuadraticLp_inner_off _ parameters.abs_p_lt_one hnm i j)
    (by norm_num) (fun n => markQuadraticLp_norm_sq_le_two _ parameters.abs_p_lt_one n i j)
    (by simpa only [norm_mul,mul_pow] using
      (p.summable_coefficient_sq (w,false)).mul_left (‖(parameters.scale : ℂ)‖ ^ 2))
  apply hb.trans
  convert mul_le_mul_of_nonneg_left
    (presented_coefficient_square_sum_le_poisson p (parameters.scale : ℂ) hw)
    (show (0 : ℝ) ≤ 2 by norm_num) using 1 <;> ring

/-- The common analytic Gaussian version inherits the sharp conditional
variance from its actual L² representative. -/
theorem presentedGaussianField_second_moment_poisson (parameters : Parameters)
    (p : ParticlePresentation s I) (anchor : (I → (Fin 4 → ℝ)) → EndpointMatrix)
    (hanchor : ∀ i j, (fun γ => anchor γ i j) =ᵐ[iidLaw (markLaw parameters.p) I]
      (fun γ => presentedGaussianL2 parameters p (Complex.I,false) γ i j))
    {w : ℂ} (hw : 0 < w.im) (i j : Fin 4) :
    (∫ γ, ‖presentedGaussianField parameters p anchor (w,false) γ i j‖ ^ 2
      ∂iidLaw (markLaw parameters.p) I) ≤
      (2 * ‖(parameters.scale : ℂ)‖ ^ 2 / w.im) * (anchoredNevanlinna s w).im := by
  rw [integral_congr_ae ((presentedGaussianField_slot_eq_L2_ae parameters p anchor hanchor
    (w,false) i j).mono (fun γ hγ => congrArg (fun z : ℂ => ‖z‖ ^ 2) hγ))]
  exact presentedGaussianL2_second_moment_poisson parameters p hw i j

variable {S : Type*} [MeasurableSpace S]
variable (P : Measure S) [IsProbabilityMeasure P]
variable (X : S → PresentedState I) (hX : Measurable X)
variable (hm : Integrable (fun x => ‖(X x).scalar.val.2‖) P)

/-- The actual jointly constructed field has the sharp conditional Poisson
variance, rather than merely a spectral-envelope bound. -/
theorem constructedZ_second_moment_poisson (parameters : Parameters)
    {w : ℂ} (hw : 0 < w.im) (i j : Fin 4) :
    ∀ᵐ x ∂P,
      (∫ γ, ‖constructedZ P X hX hm parameters x (w,false) γ i j‖ ^ 2
        ∂iidLaw (markLaw parameters.p) I) ≤
        (2 * ‖(parameters.scale : ℂ)‖ ^ 2 / w.im) * (anchoredNevanlinna (X x).scalar w).im := by
  filter_upwards [constructedAnchor_conditional_agreement P X hX hm parameters,
    constructedZ_eq_presented_ae P X hX hm parameters] with x ha heq
  rw [integral_congr_ae (heq.mono (fun γ hγ =>
    congrArg (fun A : EndpointMatrix => ‖A i j‖ ^ 2) (hγ (w,false))))]
  exact presentedGaussianField_second_moment_poisson parameters (X x).presentation _ ha hw i j

/-- First scalar-anchor integrability already gives genuine joint
integrability of every upper-half-plane Gaussian fluctuation square. -/
theorem constructedField_norm_sq_integrable_upper (parameters : Parameters)
    {w : ℂ} (hw : 0 < w.im) (i j : Fin 4) :
    Integrable (fun z => ‖constructedField P X hX hm parameters (w,false) z i j‖ ^ 2)
      (P.prod (iidLaw (markLaw parameters.p) I)) := by
  let Q := iidLaw (markLaw parameters.p) I
  let F := fun x γ => constructedZ P X hX hm parameters x (w,false) γ i j
  let U := fun x => (2 * ‖(parameters.scale : ℂ)‖ ^ 2 / w.im) *
    (anchoredNevanlinna (X x).scalar w).im
  have hscalar : Measurable (fun x => anchoredNevanlinna (X x).scalar w) :=
    (continuous_anchoredNevanlinna (ne_of_gt hw)).measurable.comp
      (PresentedState.measurable_scalar.comp hX)
  have hiNorm := Analysis.integrable_scalar_norm_of_anchor P
    (fun x => (X x).scalar) (PresentedState.measurable_scalar.comp hX) hm (ne_of_gt hw)
  have hiIm : Integrable (fun x => (anchoredNevanlinna (X x).scalar w).im) P := by
    apply hiNorm.mono' (Complex.measurable_im.comp hscalar).aestronglyMeasurable
    exact Eventually.of_forall (fun x => Complex.abs_im_le_norm _)
  have hiU : Integrable U P := hiIm.const_mul _
  have hEval : Measurable (fun A : EndpointMatrix => A i j) :=
    (show Continuous (fun A : EndpointMatrix => A i j) from
      (continuous_apply j).comp (continuous_apply i)).measurable
  have hF : AEStronglyMeasurable (fun z : S × (I → (Fin 4 → ℝ)) => F z.1 z.2) (P.prod Q) :=
    (hEval.comp (measurable_constructedField P X hX hm parameters (w,false))).aestronglyMeasurable
  have hsection : ∀ᵐ x ∂P, Integrable (fun γ => ‖F x γ‖ ^ 2) Q := by
    filter_upwards [constructedZ_memLp_two P X hX hm parameters (w,false) i j] with x hx
    exact hx.integrable_norm_pow'
  have hbound : ∀ᵐ x ∂P, (∫ γ, ‖F x γ‖ ^ 2 ∂Q) ≤ U x :=
    constructedZ_second_moment_poisson P X hX hm parameters hw i j
  have hi := Analysis.integrable_weighted_product_of_second_moments P Q F F
    (fun _ => (1 : ℂ)) U U (by simpa only [one_mul] using hF.mul hF)
    hsection hsection hbound hbound (by
      convert hiU using 1
      funext x
      simp only [norm_one,one_mul]
      ring)
  convert hi.norm using 1
  funext z
  simp only [one_mul,norm_mul,pow_two]
  rfl

/-- The actual joint second moment is controlled by the expected scalar
Poisson height, with its exact inverse spectral-height factor. -/
theorem constructedField_second_moment_poisson (parameters : Parameters)
    {w : ℂ} (hw : 0 < w.im) (i j : Fin 4) :
    (∫ z, ‖constructedField P X hX hm parameters (w,false) z i j‖ ^ 2
      ∂P.prod (iidLaw (markLaw parameters.p) I)) ≤
      (2 * ‖(parameters.scale : ℂ)‖ ^ 2 / w.im) *
        (∫ x, (anchoredNevanlinna (X x).scalar w).im ∂P) := by
  have hi := constructedField_norm_sq_integrable_upper P X hX hm parameters hw i j
  have hscalar : Measurable (fun x => anchoredNevanlinna (X x).scalar w) :=
    (continuous_anchoredNevanlinna (ne_of_gt hw)).measurable.comp
      (PresentedState.measurable_scalar.comp hX)
  have hiNorm := Analysis.integrable_scalar_norm_of_anchor P
    (fun x => (X x).scalar) (PresentedState.measurable_scalar.comp hX) hm (ne_of_gt hw)
  have hiIm : Integrable (fun x => (anchoredNevanlinna (X x).scalar w).im) P := by
    apply hiNorm.mono' (Complex.measurable_im.comp hscalar).aestronglyMeasurable
    exact Eventually.of_forall (fun x => Complex.abs_im_le_norm _)
  rw [integral_prod _ hi]
  exact (integral_mono_ae hi.integral_prod_left (hiIm.const_mul _)
    (constructedZ_second_moment_poisson P X hX hm parameters hw i j)).trans_eq
      (integral_const_mul _ _)

/-- Uniform first scalar height moments force the actual entire matrix
fluctuation to vanish in joint L² at imaginary infinity. -/
theorem constructedField_entryEnvelope_square_tendsto_zero (parameters : Parameters)
    (C : ℝ) (hC : 0 ≤ C)
    (hheight : ∀ n : ℕ, (∫ x, ‖anchoredNevanlinna (X x).scalar
      ((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I)‖ ∂P) ≤ C) :
    Tendsto (fun n : ℕ => ∫ z, Graph.entryEnvelope
      (constructedField P X hX hm parameters
        (((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I),false) z) ^ 2
      ∂P.prod (iidLaw (markLaw parameters.p) I)) atTop (𝓝 0) := by
  have hbound (n : ℕ) : (∫ z, Graph.entryEnvelope
      (constructedField P X hX hm parameters
        (((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I),false) z) ^ 2
      ∂P.prod (iidLaw (markLaw parameters.p) I)) ≤
      512 * ‖(parameters.scale : ℂ)‖ ^ 2 * C / ((n : ℝ) + 1) := by
    let w : ℂ := (((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I
    have hw : 0 < w.im := by dsimp [w]; simp; positivity
    let Z := constructedField P X hX hm parameters (w,false)
    have hZ (i j : Fin 4) : AEStronglyMeasurable (fun z => Z z i j)
        (P.prod (iidLaw (markLaw parameters.p) I)) := by
      have hEval : Measurable (fun A : EndpointMatrix => A i j) :=
        (show Continuous (fun A : EndpointMatrix => A i j) from
          (continuous_apply j).comp (continuous_apply i)).measurable
      exact (hEval.comp (measurable_constructedField P X hX hm parameters (w,false))).aestronglyMeasurable
    have hiZ (i j : Fin 4) : Integrable (fun z => ‖Z z i j‖ ^ 2)
        (P.prod (iidLaw (markLaw parameters.p) I)) :=
      constructedField_norm_sq_integrable_upper P X hX hm parameters hw i j
    have hiNorm := Analysis.integrable_scalar_norm_of_anchor P
      (fun x => (X x).scalar) (PresentedState.measurable_scalar.comp hX) hm (ne_of_gt hw)
    have hscalar : Measurable (fun x => anchoredNevanlinna (X x).scalar w) :=
      (continuous_anchoredNevanlinna (ne_of_gt hw)).measurable.comp
        (PresentedState.measurable_scalar.comp hX)
    have hiIm : Integrable (fun x => (anchoredNevanlinna (X x).scalar w).im) P := by
      apply hiNorm.mono' (Complex.measurable_im.comp hscalar).aestronglyMeasurable
      exact Eventually.of_forall (fun x => Complex.abs_im_le_norm _)
    have hIm : (∫ x, (anchoredNevanlinna (X x).scalar w).im ∂P) ≤ C :=
      (integral_mono hiIm hiNorm (fun x => Complex.im_le_norm _)).trans (hheight n)
    have hb (i j : Fin 4) : (∫ z, ‖Z z i j‖ ^ 2
        ∂P.prod (iidLaw (markLaw parameters.p) I)) ≤
        (2 * ‖(parameters.scale : ℂ)‖ ^ 2 / w.im) * C :=
      (constructedField_second_moment_poisson P X hX hm parameters hw i j).trans
        (mul_le_mul_of_nonneg_left hIm (by positivity))
    calc
      _ ≤ 16 * (∑ i, ∑ j, ∫ z, ‖Z z i j‖ ^ 2
          ∂P.prod (iidLaw (markLaw parameters.p) I)) :=
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
