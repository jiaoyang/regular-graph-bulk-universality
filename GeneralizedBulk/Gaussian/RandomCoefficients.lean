import GeneralizedBulk.Gaussian.Presentation
import GeneralizedBulk.Analysis.MeasurableSeries

/-! Jointly integrable coefficient squares for a random presented particle state. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology BigOperators

namespace GeneralizedBulk.Gaussian

theorem integrable_presented_weight_sum
    {ι S : Type*} [Countable ι] [MeasurableSpace S]
    (P : Measure S) (X : S → PresentedState ι) (hX : Measurable X)
    (hm : Integrable (fun x => ‖(X x).scalar.val.2‖) P) :
    Integrable (fun x => ∑' i, nevanlinnaWeight ((X x).location i)) P := by
  have hmeas (i : ι) : Measurable (fun x => nevanlinnaWeight ((X x).location i)) :=
    continuous_nevanlinnaWeight.measurable.comp ((PresentedState.measurable_location i).comp hX)
  apply hm.mono' (GeneralizedBulk.Analysis.measurable_nonneg_tsum _ hmeas
    (fun i x => nevanlinnaWeight_nonneg _)).aestronglyMeasurable
  filter_upwards [] with x
  have hsum := ((X x).presentation.hasSum_observable (X x).scalar.integrable_weight).tsum_eq
  change (∑' i, nevanlinnaWeight ((X x).location i)) = _ at hsum
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun i => nevanlinnaWeight_nonneg _)), hsum]
  exact (X x).scalar.integral_weight_le_im.trans (Complex.im_le_norm _)

theorem particleCoefficient_anchor_sq_bound (x : ℝ) :
    ‖particleCoefficient x (Complex.I, false)‖ ^ 2 ≤ 5 * nevanlinnaWeight x := by
  have hb := norm_reciprocal_sq_le_weight_uniform x (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) ≤ |Complex.I.im|) (by simp : ‖Complex.I‖ ≤ (1 : ℝ))
  norm_num at hb
  simpa [particleCoefficient, norm_pow, norm_inv, inv_pow] using hb

/-- The coefficient expectation is summable jointly over states and particles.
This constructs the global L² anchor without a nonmeasurable choice of a
conditional representative. -/
theorem summable_anchor_coefficient_integrals
    {ι S : Type*} [Countable ι] [MeasurableSpace S]
    (P : Measure S) (X : S → PresentedState ι) (hX : Measurable X)
    (hm : Integrable (fun x => ‖(X x).scalar.val.2‖) P) (sigma : ℂ) :
    Summable (fun i => ∫ x,
      ‖sigma * particleCoefficient ((X x).location i) (Complex.I, false)‖ ^ 2 ∂P) := by
  let F : ι → S → ℝ := fun i x =>
    ‖sigma * particleCoefficient ((X x).location i) (Complex.I, false)‖ ^ 2
  let bound : ι → S → ℝ := fun i x =>
    (5 * ‖sigma‖ ^ 2) * nevanlinnaWeight ((X x).location i)
  have hF (i : ι) : AEStronglyMeasurable (F i) P := by
    exact (((measurable_particleCoefficient (Complex.I, false)).comp
      ((PresentedState.measurable_location i).comp hX)).const_mul sigma).norm.pow_const 2 |>.aestronglyMeasurable
  have hb (i : ι) : ∀ᵐ x ∂P, ‖F i x‖ ≤ bound i x := by
    filter_upwards [] with x
    dsimp [F, bound]
    rw [abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    exact (mul_le_mul_of_nonneg_left (particleCoefficient_anchor_sq_bound _) (sq_nonneg ‖sigma‖)).trans_eq (by ring)
  have hs : ∀ᵐ x ∂P, Summable (fun i => bound i x) :=
    Filter.Eventually.of_forall (fun x => (X x).presentation.summable_weight.mul_left _)
  have hi : Integrable (fun x => ∑' i, bound i x) P := by
    simpa only [bound, tsum_mul_left] using (integrable_presented_weight_sum P X hX hm).const_mul (5 * ‖sigma‖ ^ 2)
  have hlim : ∀ᵐ x ∂P, HasSum (fun i => F i x) (∑' i, F i x) :=
    Filter.Eventually.of_forall (fun x => by
      have hh := (X x).presentation.summable_coefficient_sq (Complex.I, false)
      simpa only [F, norm_mul, mul_pow] using (hh.mul_left (‖sigma‖ ^ 2)).hasSum)
  exact (hasSum_integral_of_dominated_convergence bound hF hb hs hi hlim).summable

end GeneralizedBulk.Gaussian
