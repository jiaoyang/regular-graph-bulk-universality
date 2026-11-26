import BourgadeHuang.CharacteristicRatioSource

/-! The removable resolvent divided difference and its genuine path integral. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

def anchoredDividedDifference (s : AnchoredCountingState) (w v : ℂ) : ℂ :=
  (anchoredLinearCoefficient s : ℂ) +
    ∫ a : ℝ, ((a : ℂ)-w)⁻¹*((a : ℂ)-v)⁻¹ ∂s.val.1.measure

theorem integrable_reciprocal_product (s : AnchoredCountingState)
    {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    Integrable (fun a : ℝ => ((a : ℂ)-w)⁻¹*((a : ℂ)-v)⁻¹) s.val.1.measure := by
  apply ((integrable_reciprocal_sq s hw).norm.add
    (integrable_reciprocal_sq s hv).norm).mono'
    (((Complex.measurable_ofReal.sub measurable_const).inv).mul
      (Complex.measurable_ofReal.sub measurable_const).inv).aestronglyMeasurable
  filter_upwards [] with a
  simp only [Pi.add_apply, norm_mul, norm_pow]
  nlinarith [sq_nonneg (‖((a : ℂ)-w)⁻¹‖ - ‖((a : ℂ)-v)⁻¹‖)]

theorem anchoredDividedDifference_self (s : AnchoredCountingState)
    {w : ℂ} (hw : w.im ≠ 0) :
    anchoredDividedDifference s w w = anchoredDerivative s w := by
  rw [anchoredDerivative_eq_integral s hw]
  simp only [anchoredDividedDifference, pow_two]

theorem anchoredDividedDifference_eq_quotient (s : AnchoredCountingState)
    {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) (hwv : w ≠ v) :
    anchoredDividedDifference s w v =
      (anchoredNevanlinna s w-anchoredNevanlinna s v)/(w-v) := by
  have he (a : ℝ) : ((a : ℂ)-w)⁻¹*((a : ℂ)-v)⁻¹ =
      (regularizedResolventKernel w a-regularizedResolventKernel v a)/(w-v) := by
    simp only [regularizedResolventKernel]
    field_simp [real_sub_ne_zero a hw, real_sub_ne_zero a hv, sub_ne_zero.mpr hwv]
    ring
  simp_rw [anchoredDividedDifference, he]
  rw [integral_div, integral_sub (integrable_regularizedResolventKernel s hw)
    (integrable_regularizedResolventKernel s hv),
    anchoredNevanlinna_eq_regularized s hw, anchoredNevanlinna_eq_regularized s hv]
  field_simp [sub_ne_zero.mpr hwv]
  ring

theorem hasDerivAt_anchoredDividedDifference_right (s : AnchoredCountingState)
    {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    HasDerivAt (anchoredDividedDifference s w) (anchoredInteraction s w v) v := by
  let R := |v.im|/2
  have hR : 0 < R := by dsimp [R]; positivity
  let M := ‖v‖+R
  let C := 1+(2*M)*(1/R)+(1+M^2)*(1/R)^2
  have hC : 0 ≤ C := by dsimp [C,M]; positivity
  have hmeas (u : ℂ) : Measurable (fun a : ℝ => ((a : ℂ)-w)⁻¹*((a : ℂ)-u)⁻¹) :=
    (Complex.measurable_ofReal.sub measurable_const).inv.mul
      (Complex.measurable_ofReal.sub measurable_const).inv
  have hdm : AEStronglyMeasurable (fun a : ℝ =>
      ((a : ℂ)-w)⁻¹*(((a : ℂ)-v)⁻¹)^2) s.val.1.measure :=
    (integrable_reciprocal_interaction s hw hv).aestronglyMeasurable
  have hd : HasDerivAt (fun u : ℂ => ∫ a : ℝ, ((a : ℂ)-w)⁻¹*((a : ℂ)-u)⁻¹ ∂s.val.1.measure)
      (∫ a : ℝ, ((a : ℂ)-w)⁻¹*(((a : ℂ)-v)⁻¹)^2 ∂s.val.1.measure) v := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun u a => ((a : ℂ)-w)⁻¹*((a : ℂ)-u)⁻¹)
      (F' := fun u a => ((a : ℂ)-w)⁻¹*(((a : ℂ)-u)⁻¹)^2)
      (bound := fun a => ((1/|w.im|)*C)*nevanlinnaWeight a) hR
      (Filter.Eventually.of_forall (fun u => (hmeas u).aestronglyMeasurable))
      (integrable_reciprocal_product s hw hv) hdm ?_ (s.integrable_weight.const_mul _) ?_).2
    · filter_upwards [] with a
      intro u hu
      have hi := half_imaginary_ball_bound v u hv hu
      have hnormu : ‖u‖ ≤ M := by
        have hh : ‖u‖ ≤ ‖u-v‖+‖v‖ := by simpa only [sub_add_cancel] using norm_add_le (u-v) v
        have hu' : ‖u-v‖ < R := by simpa only [Metric.mem_ball,dist_eq_norm] using hu
        dsimp [M]
        linarith
      rw [norm_mul]
      exact (mul_le_mul (norm_reciprocal_le_im a hw)
        (norm_reciprocal_sq_le_weight_uniform a hR hi.1 hnormu) (norm_nonneg _) (by positivity)).trans_eq
          (by dsimp [C]; ring)
    · filter_upwards [] with a
      intro u hu
      exact (hasDerivAt_reciprocal a (half_imaginary_ball_bound v u hv hu).2).const_mul _
  simpa only [anchoredDividedDifference, ← anchoredInteraction_eq_integral s hw hv] using
    hd.const_add (anchoredLinearCoefficient s : ℂ)

theorem continuousAt_anchoredDividedDifference_right (s : AnchoredCountingState)
    {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    ContinuousAt (anchoredDividedDifference s w) v :=
  (hasDerivAt_anchoredDividedDifference_right s hw hv).continuousAt

/-- The interaction path integral is an endpoint difference even when the
path passes through the first spectral parameter. -/
theorem integral_ratioPath_interaction (s : AnchoredCountingState)
    {u v w : ℂ} (huv : SameOpenHalfPlane u v) (hw : w.im ≠ 0) :
    (∫ t : RatioInterval, -(u-v)*anchoredInteraction s w (ratioPath u v t)
      ∂ratioIntervalMeasure) =
        anchoredDividedDifference s w v-anchoredDividedDifference s w u := by
  have hd (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => -anchoredDividedDifference s w (ratioPath u v t))
        (-(u-v)*anchoredInteraction s w (ratioPath u v t)) t := by
    have hoff := ratioPath_offReal huv (Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1) ▸ ht)
    have hp := ((hasDerivAt_const (t : ℂ) v).add ((hasDerivAt_id (t : ℂ)).mul_const (u-v)))
    have hh := ((hasDerivAt_anchoredDividedDifference_right s hw hoff).neg.comp (t : ℂ) hp).comp_ofReal
    convert hh using 1 <;> simp only [ratioPath, zero_add, one_mul] <;> ring
  have hc : ContinuousOn (fun t : ℝ => -(u-v)*anchoredInteraction s w (ratioPath u v t))
      (Set.uIcc (0 : ℝ) 1) := by
    intro t ht
    have hoff := ratioPath_offReal huv (Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1) ▸ ht)
    exact (continuousAt_const.mul ((continuousAt_anchoredInteraction_right s hw hoff).comp
      (continuous_ratioPath u v).continuousAt)).continuousWithinAt
  rw [integral_ratioInterval (fun t : ℝ => -(u-v)*anchoredInteraction s w (ratioPath u v t))]
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  simpa [ratioPath, sub_eq_add_neg, add_comm] using hf

/-- The limiting characteristic-ratio loop identity written entirely in
endpoint resolvents, with the divided difference extended over collisions. -/
theorem characteristicRatio_endpoint_loop
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {u v w : ℂ} (huv : SameOpenHalfPlane u v) (hw : w.im ≠ 0) :
    Integrable (fun s => (anchoredLoopHead β s w+(2/β.value)*
      (anchoredDividedDifference s w v-anchoredDividedDifference s w u))*
        anchoredCharacteristicRatio s u v) ν ∧
    (∫ s, (anchoredLoopHead β s w+(2/β.value)*
      (anchoredDividedDifference s w v-anchoredDividedDifference s w u))*
        anchoredCharacteristicRatio s u v ∂ν) = 0 := by
  have hid (s : AnchoredCountingState) :
      (∫ t : RatioInterval, -(u-v)*((2/β.value)*anchoredInteraction s w (ratioPath u v t))
        ∂ratioIntervalMeasure) =
      (2/β.value)*(anchoredDividedDifference s w v-anchoredDividedDifference s w u) := by
    simp_rw [mul_left_comm (-(u-v)) (2/β.value)]
    rw [integral_const_mul, integral_ratioPath_interaction s huv hw]
  have h := (characteristicRatio_integrable_and_loop ν β hh ha he huv hw).2
  simpa only [hid] using h

end BourgadeHuang
