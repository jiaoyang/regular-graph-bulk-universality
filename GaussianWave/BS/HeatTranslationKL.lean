import GaussianWave.BS.EntropyEndpoint
import GaussianWave.BS.HeatDerivatives
import GaussianWave.BS.Reused.Entropy.LogSum

/-! Gaussian convolution contracts translation relative entropy for an arbitrary
mixing probability law. No finite support, entropy, or moment input is needed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS
open Reused.Entropy
attribute [local fun_prop] measurable_heatKernel measurable_heatDensity
set_option maxHeartbeats 1000000
variable {I : Type*} [Fintype I]

def heatKernelTranslationKL (t : ℝ) (h x : I → ℝ) : ℝ :=
  klIntegrand (heatKernel t x) (heatKernel t (x + h))

theorem log_heatKernel_translation_ratio {t : ℝ} (ht : 0 < t) (h x : I → ℝ) :
    Real.log (heatKernel t x / heatKernel t (x + h)) =
      squareRadius h / (4 * t) + (∑ i, x i * h i) / (2 * t) := by
  rw [Real.log_div (heatKernel_pos ht x).ne' (heatKernel_pos ht (x + h)).ne',
    log_heatKernel ht x, log_heatKernel ht (x + h), coe_heatVariance ht.le]
  have hs : squareRadius (x + h) = squareRadius x + 2 * (∑ i, x i * h i) + squareRadius h := by
    simp only [squareRadius, Pi.add_apply, add_sq, Finset.sum_add_distrib,
      ← Finset.mul_sum, mul_assoc]
  rw [hs]
  ring

private theorem integrable_kernel_coordinate {t : ℝ} (ht : 0 < t) (i : I) :
    Integrable (fun x : I → ℝ => heatKernel t x * x i) := by
  apply ((integrable_heatKernel t).add (integrable_heatKernel_mul_coordinate_sq ht i)).mono'
    (((measurable_heatKernel t).mul (measurable_pi_apply i)).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg _ _)]
  have hp := heatKernel_nonneg t x
  have hs : |x i| ≤ 1 + x i ^ 2 := by nlinarith [sq_abs (x i), sq_nonneg (|x i| - 1)]
  change heatKernel t x * |x i| ≤ heatKernel t x + heatKernel t x * x i ^ 2
  simpa only [mul_add, mul_one] using mul_le_mul_of_nonneg_left hs hp

private theorem integral_kernel_coordinate {t : ℝ} (ht : 0 < t) (i : I) :
    (∫ x : I → ℝ, heatKernel t x * x i) = 0 := by
  have he := integral_withDensity_eq_integral_toReal_smul
    (μ := (volume : Measure (I → ℝ))) (measurable_heatKernel t).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) (fun x => x i)
  simp only [ENNReal.toReal_ofReal (heatKernel_nonneg _ _), smul_eq_mul] at he
  rw [← he, ← heatGaussian_eq_withDensity ht, integral_heatGaussian_coordinate]

private theorem integrable_kernel_coordinate_shift
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) (x : I → ℝ) (i : I) :
    Integrable (fun y => heatKernel t (x - y) * (x - y) i) μ := by
  apply (integrable_const ((1 + 4 * t) * heatKernelBound I t)).mono'
    ((((measurable_heatKernel t).comp (measurable_const.sub measurable_id)).mul
      ((measurable_pi_apply i).comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
  filter_upwards [] with y
  change ‖heatKernel t (x - y) * (x - y) i‖ ≤ (1 + 4 * t) * heatKernelBound I t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg _ _), mul_comm]
  exact abs_coordinate_mul_heatKernel_le ht _ i

private theorem kernel_log_ratio_formula {t : ℝ} (ht : 0 < t) (h x : I → ℝ) :
    heatKernel t x * Real.log (heatKernel t x / heatKernel t (x + h)) =
      heatKernel t x * (squareRadius h / (4 * t)) +
        (∑ i, h i * (heatKernel t x * x i)) / (2 * t) := by
  rw [log_heatKernel_translation_ratio ht]
  rw [mul_add]
  congr 1
  calc
    _ = (heatKernel t x * ∑ i, x i * h i) / (2 * t) := by ring
    _ = _ := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

private theorem integrable_kernel_log_ratio {t : ℝ} (ht : 0 < t) (h : I → ℝ) :
    Integrable (fun x => heatKernel t x * Real.log (heatKernel t x / heatKernel t (x + h))) := by
  simp_rw [kernel_log_ratio_formula ht]
  exact ((integrable_heatKernel t).mul_const _).add
    ((integrable_finset_sum _ (fun i _ => (integrable_kernel_coordinate ht i).const_mul (h i))).div_const _)

private theorem integrable_kernel_log_ratio_shift
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) (h x : I → ℝ) :
    Integrable (fun y => heatKernel t (x - y) *
      Real.log (heatKernel t (x - y) / heatKernel t ((x - y) + h))) μ := by
  simp_rw [kernel_log_ratio_formula ht]
  exact ((integrable_heatKernel_shift μ t x).mul_const _).add
    ((integrable_finset_sum _ (fun i _ => (integrable_kernel_coordinate_shift μ ht x i).const_mul (h i))).div_const _)

theorem integrable_heatKernelTranslationKL {t : ℝ} (ht : 0 < t) (h : I → ℝ) :
    Integrable (heatKernelTranslationKL t h) := by
  unfold heatKernelTranslationKL klIntegrand
  exact ((integrable_kernel_log_ratio ht h).sub (integrable_heatKernel t)).add
    (by simpa only [sub_neg_eq_add] using integrable_sub_right (heatKernel t) (integrable_heatKernel t) (-h))

theorem integral_heatKernelTranslationKL {t : ℝ} (ht : 0 < t) (h : I → ℝ) :
    (∫ x, heatKernelTranslationKL t h x) = squareRadius h / (4 * t) := by
  have hf := integrable_kernel_log_ratio ht h
  have hg : Integrable (fun x => heatKernel t (x + h)) := by
    simpa only [sub_neg_eq_add] using integrable_sub_right (heatKernel t) (integrable_heatKernel t) (-h)
  unfold heatKernelTranslationKL klIntegrand
  rw [integral_add (f := fun x => heatKernel t x * Real.log (heatKernel t x / heatKernel t (x + h)) - heatKernel t x)
    (hf.sub (integrable_heatKernel t)) hg,
    integral_sub (f := fun x => heatKernel t x * Real.log (heatKernel t x / heatKernel t (x + h))) hf (integrable_heatKernel t)]
  have hshift : (∫ x, heatKernel t (x + h)) = 1 := by
    simpa only [sub_neg_eq_add] using (integral_sub_right_eq (heatKernel t) (-h)).trans (integral_heatKernel ht)
  rw [integral_heatKernel ht, hshift]
  simp_rw [kernel_log_ratio_formula ht]
  rw [integral_add ((integrable_heatKernel t).mul_const _)
      ((integrable_finset_sum _ (fun i _ => (integrable_kernel_coordinate ht i).const_mul (h i))).div_const _),
    integral_mul_const, integral_div,
    integral_finset_sum _ (fun i _ => (integrable_kernel_coordinate ht i).const_mul (h i))]
  simp only [integral_const_mul, integral_kernel_coordinate ht, mul_zero,
    Finset.sum_const_zero, zero_div, add_zero, integral_heatKernel ht, one_mul]
  ring

private theorem integrable_kernelKL_product
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (h : I → ℝ) :
    Integrable (fun z : (I → ℝ) × (I → ℝ) => heatKernelTranslationKL t h (z.2 - z.1)) (μ.prod volume) := by
  have hm : AEStronglyMeasurable
      (fun z : (I → ℝ) × (I → ℝ) => heatKernelTranslationKL t h (z.2 - z.1)) (μ.prod volume) := by
    unfold heatKernelTranslationKL klIntegrand
    exact (by fun_prop : Measurable (fun z : (I → ℝ) × (I → ℝ) =>
      heatKernel t (z.2 - z.1) * Real.log (heatKernel t (z.2 - z.1) / heatKernel t ((z.2 - z.1) + h)) -
        heatKernel t (z.2 - z.1) + heatKernel t ((z.2 - z.1) + h))).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact ae_of_all _ (fun y => integrable_sub_right _ (integrable_heatKernelTranslationKL ht h) y)
  · simp_rw [integral_sub_right_eq (fun x => ‖heatKernelTranslationKL t h x‖)]
    exact integrable_const _

/-- The actual heat convolution has translation KL bounded by the noise KL.
Integrability and the estimate are derived for arbitrary probability inputs. -/
theorem heatDensity_translation_kl
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (h : I → ℝ) :
    Integrable (fun x => klIntegrand (heatDensity μ t x) (heatDensity μ t (x + h))) ∧
      (∫ x, klIntegrand (heatDensity μ t x) (heatDensity μ t (x + h))) ≤
        squareRadius h / (4 * t) := by
  let F := fun z : (I → ℝ) × (I → ℝ) => heatKernelTranslationKL t h (z.2 - z.1)
  have hF : Integrable F (μ.prod volume) := integrable_kernelKL_product μ ht h
  have hbound (x : I → ℝ) :
      klIntegrand (heatDensity μ t x) (heatDensity μ t (x + h)) ≤ ∫ y, F (y, x) ∂μ := by
    have hi := klIntegrand_integral_le μ
      (fun y => heatKernel t (x - y)) (fun y => heatKernel t ((x - y) + h))
      (fun y => heatKernel_pos ht _) (fun y => heatKernel_pos ht _)
      (integrable_heatKernel_shift μ t x)
      (by simpa only [sub_add_eq_add_sub] using integrable_heatKernel_shift μ t (x + h))
      (integrable_kernel_log_ratio_shift μ ht h x)
      (heatDensity_pos μ ht x)
      (by simpa only [sub_add_eq_add_sub] using heatDensity_pos μ ht (x + h))
    simpa only [heatDensity, F, heatKernelTranslationKL, sub_add_eq_add_sub] using hi
  have hmajor : Integrable (fun x => ∫ y, F (y, x) ∂μ) := hF.integral_prod_right
  have hm : Measurable (fun x => klIntegrand (heatDensity μ t x) (heatDensity μ t (x + h))) := by
    unfold klIntegrand
    fun_prop
  have hi : Integrable (fun x => klIntegrand (heatDensity μ t x) (heatDensity μ t (x + h))) := by
    apply hmajor.mono' hm.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (klIntegrand_nonneg _ _
      (heatDensity_pos μ ht x) (heatDensity_pos μ ht (x + h)))]
    exact hbound x
  refine ⟨hi, (integral_mono hi hmajor hbound).trans_eq ?_⟩
  have hs : Integrable (Function.uncurry (fun x y => F (y, x))) (volume.prod μ) := by
    simpa only [Function.comp_def, Function.uncurry] using hF.swap
  rw [integral_integral_swap hs]
  have he (y : I → ℝ) : (∫ x, F (y, x)) = squareRadius h / (4 * t) := by
    change (∫ x, heatKernelTranslationKL t h (x - y)) = _
    rw [integral_sub_right_eq, integral_heatKernelTranslationKL ht]
  simp_rw [he]
  simp

/-- Symmetric translation entropy bound used by the genuine grid theorem. -/
theorem heatDensity_symmetric_translation_entropy
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (h : I → ℝ) :
    Integrable (fun x => (heatDensity μ t x - heatDensity μ t (x + h)) *
      (Real.log (heatDensity μ t x) - Real.log (heatDensity μ t (x + h)))) ∧
      (∫ x, (heatDensity μ t x - heatDensity μ t (x + h)) *
        (Real.log (heatDensity μ t x) - Real.log (heatDensity μ t (x + h)))) ≤
          squareRadius h / (2 * t) := by
  obtain ⟨hforw, hforwb⟩ := heatDensity_translation_kl μ ht h
  obtain ⟨hback, hbackb⟩ := heatDensity_translation_kl μ ht (-h)
  have hb : Integrable (fun x => klIntegrand (heatDensity μ t (x + h)) (heatDensity μ t x)) := by
    simpa only [sub_neg_eq_add, add_neg_cancel_right] using
      integrable_sub_right _ hback (-h)
  have hbb : (∫ x, klIntegrand (heatDensity μ t (x + h)) (heatDensity μ t x)) ≤ squareRadius h / (4 * t) := by
    have he := integral_sub_right_eq
      (fun x => klIntegrand (heatDensity μ t x) (heatDensity μ t (x + -h))) (-h)
    simp only [sub_neg_eq_add, add_neg_cancel_right] at he
    rw [he]
    simpa only [squareRadius, Pi.neg_apply, neg_sq] using hbackb
  have heq (x : I → ℝ) :
      (heatDensity μ t x - heatDensity μ t (x + h)) *
        (Real.log (heatDensity μ t x) - Real.log (heatDensity μ t (x + h))) =
      klIntegrand (heatDensity μ t x) (heatDensity μ t (x + h)) +
        klIntegrand (heatDensity μ t (x + h)) (heatDensity μ t x) := by
    unfold klIntegrand
    rw [Real.log_div (heatDensity_pos μ ht x).ne' (heatDensity_pos μ ht (x + h)).ne',
      Real.log_div (heatDensity_pos μ ht (x + h)).ne' (heatDensity_pos μ ht x).ne']
    ring
  simp_rw [heq]
  refine ⟨hforw.add hb, ?_⟩
  rw [integral_add hforw hb]
  calc
    _ ≤ squareRadius h / (4 * t) + squareRadius h / (4 * t) := add_le_add hforwb hbb
    _ = squareRadius h / (2 * t) := by ring
end GaussianWave.BS
