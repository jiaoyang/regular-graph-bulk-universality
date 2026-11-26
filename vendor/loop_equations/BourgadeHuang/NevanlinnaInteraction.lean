import BourgadeHuang.NevanlinnaDerivatives
import BourgadeHuang.NevanlinnaPositivity

/-!
# The representing-measure formula for the interaction

The interaction is a genuine integrable reciprocal-product kernel, including its
diagonal. Its bound has no divided-difference singularity, so it is uniform when
spectral parameters approach one another inside either half-plane.
-/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

/-- A weighted partial-fraction identity for the derivative kernel. -/
theorem reciprocal_sq_weight_decomposition (a : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (((a : ℂ) - z)⁻¹) ^ 2 = (nevanlinnaWeight a : ℂ) +
      2 * z * anchoredPowerKernel 0 z a + (1 + z ^ 2) * anchoredPowerKernel 1 z a := by
  have ha : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
  have ha' : (1 + (a : ℂ) ^ 2) ≠ 0 := by exact_mod_cast ha
  simp only [anchoredPowerKernel, nevanlinnaWeight, Complex.ofReal_inv,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow]
  field_simp [ha', real_sub_ne_zero a hz]
  ring

theorem integrable_reciprocal_sq (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun a : ℝ => (((a : ℂ) - z)⁻¹) ^ 2) s.val.1.measure := by
  simp_rw [reciprocal_sq_weight_decomposition _ hz]
  exact (s.integrable_weight.ofReal.add ((integrable_anchoredPowerKernel 0 s hz).const_mul _)).add
    ((integrable_anchoredPowerKernel 1 s hz).const_mul _)

/-- The true derivative has the classical nonnegative-linear-term representation. -/
theorem anchoredDerivative_eq_integral (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) :
    anchoredDerivative s z = (anchoredLinearCoefficient s : ℂ) +
      ∫ a : ℝ, (((a : ℂ) - z)⁻¹) ^ 2 ∂s.val.1.measure := by
  have h0 : Integrable (fun a => (nevanlinnaWeight a : ℂ)) s.val.1.measure := s.integrable_weight.ofReal
  have h1 : Integrable (fun a => 2 * z * anchoredPowerKernel 0 z a) s.val.1.measure :=
    (integrable_anchoredPowerKernel 0 s hz).const_mul _
  have h2 : Integrable (fun a => (1 + z ^ 2) * anchoredPowerKernel 1 z a) s.val.1.measure :=
    (integrable_anchoredPowerKernel 1 s hz).const_mul _
  have h01 : Integrable (fun a => (nevanlinnaWeight a : ℂ) + 2 * z * anchoredPowerKernel 0 z a)
      s.val.1.measure := h0.add h1
  simp_rw [reciprocal_sq_weight_decomposition _ hz]
  rw [integral_add h01 h2, integral_add h0 h1, integral_const_mul, integral_const_mul,
    integral_complex_ofReal]
  simp only [anchoredDerivative, anchoredPowerIntegral, anchoredLinearCoefficient, Complex.ofReal_sub]
  ring

/-- A collision-free bound for the squared reciprocal relative to the Nevanlinna weight. -/
theorem norm_reciprocal_sq_le_weight (a : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ‖(((a : ℂ) - z)⁻¹) ^ 2‖ ≤
      (1 + (2 * ‖z‖) * (1 / |z.im|) + ‖1 + z ^ 2‖ * (1 / |z.im|) ^ 2) * nevanlinnaWeight a := by
  rw [reciprocal_sq_weight_decomposition a hz]
  calc
    _ ≤ ‖(nevanlinnaWeight a : ℂ)‖ + ‖2 * z * anchoredPowerKernel 0 z a‖ +
        ‖(1 + z ^ 2) * anchoredPowerKernel 1 z a‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ = nevanlinnaWeight a + (2 * ‖z‖) * ‖anchoredPowerKernel 0 z a‖ +
        ‖1 + z ^ 2‖ * ‖anchoredPowerKernel 1 z a‖ := by
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (nevanlinnaWeight_nonneg a)]
    _ ≤ nevanlinnaWeight a + (2 * ‖z‖) * ((1 / |z.im|) * nevanlinnaWeight a) +
        ‖1 + z ^ 2‖ * ((1 / |z.im|) ^ 2 * nevanlinnaWeight a) :=
      add_le_add (add_le_add_left (mul_le_mul_of_nonneg_left
        (by simpa using norm_anchoredPowerKernel_le 0 hz a) (by positivity)) _)
        (mul_le_mul_of_nonneg_left (by simpa using norm_anchoredPowerKernel_le 1 hz a) (norm_nonneg _))
    _ = _ := by ring

/-- The genuine interaction kernel is integrable without any separation of `w` and `v`. -/
theorem integrable_reciprocal_interaction (s : AnchoredCountingState)
    {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    Integrable (fun a : ℝ => ((a : ℂ) - w)⁻¹ * (((a : ℂ) - v)⁻¹) ^ 2) s.val.1.measure := by
  apply ((integrable_reciprocal_sq s hv).norm.const_mul (1 / |w.im|)).mono'
    (((Complex.continuous_ofReal.sub continuous_const).inv₀ (fun a => real_sub_ne_zero a hw)).mul
      (((Complex.continuous_ofReal.sub continuous_const).inv₀
        (fun a => real_sub_ne_zero a hv)).pow 2)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun a => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_reciprocal_le_im a hw) (norm_nonneg _))

/-- The interaction is exactly the representing-measure reciprocal-product integral. -/
theorem anchoredInteraction_eq_integral (s : AnchoredCountingState)
    {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    anchoredInteraction s w v =
      ∫ a : ℝ, ((a : ℂ) - w)⁻¹ * (((a : ℂ) - v)⁻¹) ^ 2 ∂s.val.1.measure := by
  unfold anchoredInteraction
  split_ifs with h
  · subst v
    have he (a : ℝ) : ((a : ℂ) - w)⁻¹ * (((a : ℂ) - w)⁻¹) ^ 2 =
        anchoredPowerKernel 0 w a + 2 * w * anchoredPowerKernel 1 w a +
          (1 + w ^ 2) * anchoredPowerKernel 2 w a := by
      have hh := reciprocal_sq_weight_decomposition a hw
      have hh' := congrArg (fun x : ℂ => x * ((a : ℂ) - w)⁻¹) hh
      convert hh' using 1 <;> simp only [anchoredPowerKernel] <;> ring
    simp_rw [he]
    have h0 := integrable_anchoredPowerKernel 0 s hw
    have h1 : Integrable (fun a => 2 * w * anchoredPowerKernel 1 w a) s.val.1.measure :=
      (integrable_anchoredPowerKernel 1 s hw).const_mul _
    have h2 : Integrable (fun a => (1 + w ^ 2) * anchoredPowerKernel 2 w a) s.val.1.measure :=
      (integrable_anchoredPowerKernel 2 s hw).const_mul _
    have h01 : Integrable (fun a => anchoredPowerKernel 0 w a + 2 * w * anchoredPowerKernel 1 w a)
        s.val.1.measure := h0.add h1
    rw [integral_add h01 h2, integral_add h0 h1, integral_const_mul, integral_const_mul]
    rfl
  · have he (a : ℝ) : ((a : ℂ) - w)⁻¹ * (((a : ℂ) - v)⁻¹) ^ 2 =
        ((regularizedResolventKernel w a - regularizedResolventKernel v a) -
          (w - v) * (((a : ℂ) - v)⁻¹) ^ 2) / (w - v) ^ 2 := by
      simp only [regularizedResolventKernel]
      field_simp [real_sub_ne_zero a hw, real_sub_ne_zero a hv, sub_ne_zero.mpr h]
      ring
    simp_rw [he]
    rw [integral_div]
    have hiw := integrable_regularizedResolventKernel s hw
    have hiv := integrable_regularizedResolventKernel s hv
    have hid : Integrable (fun a : ℝ => (w - v) * (((a : ℂ) - v)⁻¹) ^ 2) s.val.1.measure :=
      (integrable_reciprocal_sq s hv).const_mul _
    have his : Integrable (fun a => regularizedResolventKernel w a - regularizedResolventKernel v a)
        s.val.1.measure := hiw.sub hiv
    rw [integral_sub his hid, integral_sub hiw hiv, integral_const_mul,
      anchoredNevanlinna_eq_regularized s hw, anchoredNevanlinna_eq_regularized s hv,
      anchoredDerivative_eq_integral s hv]
    ring


/-- A uniform compact-parameter bound with no factor involving `w-v`. -/
theorem norm_anchoredInteraction_le_anchor (s : AnchoredCountingState)
    {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    ‖anchoredInteraction s w v‖ ≤
      ((1 / |w.im|) * (1 + (2 * ‖v‖) * (1 / |v.im|) +
        ‖1 + v ^ 2‖ * (1 / |v.im|) ^ 2)) * ‖s.val.2‖ := by
  let C := (1 / |w.im|) * (1 + (2 * ‖v‖) * (1 / |v.im|) + ‖1 + v ^ 2‖ * (1 / |v.im|) ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb (a : ℝ) : ‖((a : ℂ) - w)⁻¹ * (((a : ℂ) - v)⁻¹) ^ 2‖ ≤ C * nevanlinnaWeight a := by
    rw [norm_mul]
    exact (mul_le_mul (norm_reciprocal_le_im a hw) (norm_reciprocal_sq_le_weight a hv)
      (norm_nonneg _) (by positivity)).trans_eq (by dsimp [C]; ring)
  rw [anchoredInteraction_eq_integral s hw hv]
  calc
    _ ≤ ∫ a : ℝ, ‖((a : ℂ) - w)⁻¹ * (((a : ℂ) - v)⁻¹) ^ 2‖ ∂s.val.1.measure :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ a, C * nevanlinnaWeight a ∂s.val.1.measure :=
      integral_mono (integrable_reciprocal_interaction s hw hv).norm (s.integrable_weight.const_mul C) hb
    _ = C * ∫ a, nevanlinnaWeight a ∂s.val.1.measure := integral_const_mul _ _
    _ ≤ C * ‖s.val.2‖ := mul_le_mul_of_nonneg_left
      (s.integral_weight_le_im.trans (Complex.im_le_norm _)) hC

/-- Squared reciprocals are uniformly weight-dominated on bounded sets separated
from the real axis. -/
theorem norm_reciprocal_sq_le_weight_uniform (a : ℝ) {z : ℂ} {δ M : ℝ}
    (hδ : 0 < δ) (him : δ ≤ |z.im|) (hM : ‖z‖ ≤ M) :
    ‖(((a : ℂ) - z)⁻¹) ^ 2‖ ≤
      (1 + (2 * M) * (1 / δ) + (1 + M ^ 2) * (1 / δ) ^ 2) * nevanlinnaWeight a := by
  have hz : z.im ≠ 0 := abs_pos.mp (lt_of_lt_of_le hδ him)
  have hM0 : 0 ≤ M := (norm_nonneg z).trans hM
  have hi := one_div_le_one_div_of_le hδ him
  have h1 : ‖1 + z ^ 2‖ ≤ 1 + M ^ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2‖ := norm_add_le _ _
      _ ≤ 1 + M ^ 2 := by simpa only [norm_one, norm_pow] using
        (add_le_add_left (pow_le_pow_left₀ (norm_nonneg z) hM 2) 1)
  apply (norm_reciprocal_sq_le_weight a hz).trans
  apply mul_le_mul_of_nonneg_right _ (nevanlinnaWeight_nonneg a)
  exact add_le_add (add_le_add_left
    (mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num)) hi (by positivity) (by positivity)) 1)
    (mul_le_mul h1 (pow_le_pow_left₀ (by positivity) hi 2) (by positivity) (by positivity))

/-- Differentiation of the interaction in its repeated parameter is justified
under the actual representing measure, including on the diagonal. -/
theorem hasDerivAt_anchoredInteraction_right (s : AnchoredCountingState)
    {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    HasDerivAt (anchoredInteraction s w)
      (∫ a : ℝ, 2 * ((a : ℂ) - w)⁻¹ * (((a : ℂ) - v)⁻¹) ^ 3 ∂s.val.1.measure) v := by
  let R := |v.im| / 2
  have hR : 0 < R := by dsimp [R]; positivity
  let M := ‖v‖ + R
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let C := (1 + (2 * M) * (1 / R) + (1 + M ^ 2) * (1 / R) ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmeas (u : ℂ) : Measurable (fun a : ℝ => ((a : ℂ) - w)⁻¹ * (((a : ℂ) - u)⁻¹) ^ 2) :=
    (Complex.measurable_ofReal.sub measurable_const).inv.mul
      ((Complex.measurable_ofReal.sub measurable_const).inv.pow_const 2)
  have hdm : AEStronglyMeasurable (fun a : ℝ =>
      2 * ((a : ℂ) - w)⁻¹ * (((a : ℂ) - v)⁻¹) ^ 3) s.val.1.measure :=
    (measurable_const.mul (Complex.measurable_ofReal.sub measurable_const).inv |>.mul
      ((Complex.measurable_ofReal.sub measurable_const).inv.pow_const 3)).aestronglyMeasurable
  have hder : HasDerivAt (fun u : ℂ => ∫ a : ℝ,
      ((a : ℂ) - w)⁻¹ * (((a : ℂ) - u)⁻¹) ^ 2 ∂s.val.1.measure)
      (∫ a : ℝ, 2 * ((a : ℂ) - w)⁻¹ * (((a : ℂ) - v)⁻¹) ^ 3 ∂s.val.1.measure) v := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun u a => ((a : ℂ) - w)⁻¹ * (((a : ℂ) - u)⁻¹) ^ 2)
      (F' := fun u a => 2 * ((a : ℂ) - w)⁻¹ * (((a : ℂ) - u)⁻¹) ^ 3)
      (bound := fun a => (2 * (1 / |w.im|) * (1 / R) * C) * nevanlinnaWeight a) hR
      (Filter.Eventually.of_forall (fun u => (hmeas u).aestronglyMeasurable))
      (integrable_reciprocal_interaction s hw hv) hdm ?_ (s.integrable_weight.const_mul _) ?_).2
    · apply Filter.Eventually.of_forall
      intro a u hu
      have hi := half_imaginary_ball_bound v u hv hu
      have hnormu : ‖u‖ ≤ M := by
        have hh : ‖u‖ ≤ ‖u - v‖ + ‖v‖ := by simpa only [sub_add_cancel] using norm_add_le (u - v) v
        have hu' : ‖u - v‖ < R := by simpa only [Metric.mem_ball, dist_eq_norm] using hu
        dsimp [M]
        linarith
      have hsq := norm_reciprocal_sq_le_weight_uniform a hR hi.1 hnormu
      have hiu := (norm_reciprocal_le_im a hi.2).trans (one_div_le_one_div_of_le hR hi.1)
      have hq : ‖(((a : ℂ) - u)⁻¹) ^ 3‖ ≤ (1 / R) * (C * nevanlinnaWeight a) := by
        rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one, norm_mul]
        exact mul_le_mul hiu hsq (norm_nonneg _) (by positivity)
      simp only [norm_mul, Complex.norm_ofNat]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left (norm_reciprocal_le_im a hw) (by norm_num)) hq
        (norm_nonneg _) (by positivity)).trans_eq (by ring)
    · apply Filter.Eventually.of_forall
      intro a u hu
      have hh := ((hasDerivAt_reciprocal a (half_imaginary_ball_bound v u hv hu).2).pow 2).const_mul
        (((a : ℂ) - w)⁻¹)
      convert hh using 1
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
      ring
  apply hder.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds v hR] with u hu
  exact anchoredInteraction_eq_integral s hw (half_imaginary_ball_bound v u hv hu).2

/-- Interaction parameters remain continuous when they coalesce. -/
theorem continuousAt_anchoredInteraction_right (s : AnchoredCountingState)
    {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    ContinuousAt (anchoredInteraction s w) v :=
  (hasDerivAt_anchoredInteraction_right s hw hv).continuousAt

end BourgadeHuang
