import BourgadeHuang.NevanlinnaState
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Holomorphy and bounds of reconstructed particle-generated functions

Differentiation under the genuinely integrable weighted kernel is justified on
a half-imaginary-part ball. The resulting analytic functions retain the anchored
bounds needed for limiting random observables.
-/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

def anchoredResolventDerivativeKernel (z : ℂ) (a : ℝ) : ℂ :=
  (nevanlinnaWeight a : ℂ) * (((a : ℂ) - z)⁻¹) ^ 2

theorem hasDerivAt_anchoredResolventKernel (a : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (fun w => anchoredResolventKernel w a)
      (anchoredResolventDerivativeKernel z a) z := by
  have hh := ((hasDerivAt_const z (nevanlinnaWeight a : ℂ)).div
    ((hasDerivAt_const z (a : ℂ)).sub (hasDerivAt_id z))
      (real_sub_offReal_ne_zero a hz))
  convert hh using 1
  simp [anchoredResolventDerivativeKernel, id_eq, div_eq_mul_inv, inv_pow]

theorem hasDerivAt_integral_anchoredResolventKernel (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (fun w => ∫ a, anchoredResolventKernel w a ∂s.val.1.measure)
      (∫ a, anchoredResolventDerivativeKernel z a ∂s.val.1.measure) z := by
  let R := |z.im| / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hmeas (w : ℂ) : Measurable (anchoredResolventKernel w) :=
    (Complex.measurable_ofReal.comp continuous_nevanlinnaWeight.measurable).div
      (Complex.measurable_ofReal.sub measurable_const)
  have hdm : AEStronglyMeasurable (anchoredResolventDerivativeKernel z) s.val.1.measure := by
    exact ((Complex.measurable_ofReal.comp continuous_nevanlinnaWeight.measurable).mul
      ((Complex.measurable_ofReal.sub measurable_const).inv.pow_const 2)).aestronglyMeasurable
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := anchoredResolventKernel) (F' := anchoredResolventDerivativeKernel)
    (bound := fun a => (1 / R) ^ 2 * nevanlinnaWeight a) hR
    (Filter.Eventually.of_forall (fun w => (hmeas w).aestronglyMeasurable))
    (integrable_anchoredResolventKernel s.val.1.measure s.integrable_weight hz) hdm
    ?_ (s.integrable_weight.const_mul _) ?_).2
  · apply Filter.Eventually.of_forall
    intro a w hw
    have hi := half_imaginary_ball_bound z w hz hw
    have hb : ‖((a : ℂ) - w)⁻¹‖ ≤ 1 / R :=
      (norm_reciprocal_le_im a hi.2).trans (one_div_le_one_div_of_le hR hi.1)
    simp only [anchoredResolventDerivativeKernel, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (nevanlinnaWeight_nonneg a)]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2)
      (nevanlinnaWeight_nonneg a)).trans_eq (by ring)
  · exact Filter.Eventually.of_forall fun a w hw =>
      hasDerivAt_anchoredResolventKernel a (half_imaginary_ball_bound z w hz hw).2

/-- The reconstructed function is complex differentiable at every off-real point. -/
theorem differentiableAt_anchoredNevanlinna (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) : DifferentiableAt ℂ (anchoredNevanlinna s) z := by
  unfold anchoredNevanlinna
  exact ((differentiableAt_const _).add ((differentiableAt_id).mul
    (differentiableAt_const _))).add (((differentiableAt_const _).add
      (differentiableAt_id.pow 2)).mul (hasDerivAt_integral_anchoredResolventKernel s hz).differentiableAt)

/-- Pointwise complex analyticity is derived from differentiation under the integral. -/
theorem analyticAt_anchoredNevanlinna (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) : AnalyticAt ℂ (anchoredNevanlinna s) z := by
  have hopen : IsOpen {w : ℂ | w.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  exact (show DifferentiableOn ℂ (anchoredNevanlinna s) {w : ℂ | w.im ≠ 0} from
    fun w hw => (differentiableAt_anchoredNevanlinna s hw).differentiableWithinAt).analyticAt
      (hopen.mem_nhds hz)

/-- Integral control by the imaginary anchor. -/
theorem norm_integral_anchoredResolventKernel_le (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖∫ a, anchoredResolventKernel z a ∂s.val.1.measure‖ ≤ s.val.2.im / |z.im| := by
  calc
    _ ≤ ∫ a, ‖anchoredResolventKernel z a‖ ∂s.val.1.measure := norm_integral_le_integral_norm _
    _ ≤ ∫ a, nevanlinnaWeight a / |z.im| ∂s.val.1.measure :=
      integral_mono (integrable_anchoredResolventKernel s.val.1.measure s.integrable_weight hz).norm
        (s.integrable_weight.div_const _) (fun a => norm_anchoredResolventKernel_le a hz)
    _ = (∫ a, nevanlinnaWeight a ∂s.val.1.measure) / |z.im| := integral_div _ _
    _ ≤ s.val.2.im / |z.im| := div_le_div_of_nonneg_right s.integral_weight_le_im (abs_nonneg _)

/-- The same single-anchor bound holds for the actual limiting state function. -/
theorem norm_anchoredNevanlinna_le_anchor (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖anchoredNevanlinna s z‖ ≤
      (1 + ‖z‖ + ‖1 + z ^ 2‖ / |z.im|) * ‖s.val.2‖ := by
  unfold anchoredNevanlinna
  calc
    _ ≤ ‖(s.val.2.re : ℂ)‖ + ‖z * (s.val.2.im : ℂ)‖ +
        ‖(1 + z ^ 2) * ∫ a, anchoredResolventKernel z a ∂s.val.1.measure‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ = |s.val.2.re| + ‖z‖ * s.val.2.im +
        ‖1 + z ^ 2‖ * ‖∫ a, anchoredResolventKernel z a ∂s.val.1.measure‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.im_nonneg]
    _ ≤ ‖s.val.2‖ + ‖z‖ * ‖s.val.2‖ + ‖1 + z ^ 2‖ * (‖s.val.2‖ / |z.im|) :=
      add_le_add (add_le_add (Complex.abs_re_le_norm _)
        (mul_le_mul_of_nonneg_left (Complex.im_le_norm _) (norm_nonneg _)))
        (mul_le_mul_of_nonneg_left
          ((norm_integral_anchoredResolventKernel_le s hz).trans
            (div_le_div_of_nonneg_right (Complex.im_le_norm _) (abs_nonneg _)))
          (norm_nonneg _))
    _ = _ := by ring

end BourgadeHuang
