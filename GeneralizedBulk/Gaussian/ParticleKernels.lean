import BourgadeHuang.CountingParticleLabels
import BourgadeHuang.NevanlinnaDividedDifference
import Mathlib

/-!
# Actual particle coefficients for the Gaussian marked series

Particle labels retain every occurrence of a repeated atom. Coefficients are
zero on real spectral parameters; off the real axis the two slots are the
resolvent and its actual complex derivative. All square summability and kernel
identities follow from weighted local finiteness, not extra model assumptions.
-/

noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology BigOperators

namespace GeneralizedBulk.Gaussian

def particleCoefficient (x : ℝ) (v : ℂ × Bool) : ℂ :=
  if v.1.im = 0 then 0 else if v.2 then (((x : ℂ) - v.1)⁻¹) ^ 2 else ((x : ℂ) - v.1)⁻¹

theorem measurable_particleCoefficient (v : ℂ × Bool) : Measurable (fun x => particleCoefficient x v) := by
  unfold particleCoefficient
  split_ifs <;> fun_prop

theorem integrable_reciprocal_four (s : AnchoredCountingState) {w : ℂ} (hw : w.im ≠ 0) :
    Integrable (fun x : ℝ => (((x : ℂ) - w)⁻¹) ^ 4) s.val.1.measure := by
  apply (((integrable_reciprocal_sq s hw).norm).const_mul ((1 / |w.im|) ^ 2)).mono'
    (((Complex.measurable_ofReal.sub measurable_const).inv).pow_const 4).aestronglyMeasurable
  filter_upwards [] with x
  have hb := pow_le_pow_left₀ (norm_nonneg (((x : ℂ) - w)⁻¹)) (norm_reciprocal_le_im x hw) 2
  simp only [norm_pow]
  calc
    ‖((x : ℂ) - w)⁻¹‖ ^ 4 = ‖((x : ℂ) - w)⁻¹‖ ^ 2 * ‖((x : ℂ) - w)⁻¹‖ ^ 2 := by ring
    _ ≤ (1 / |w.im|) ^ 2 * ‖((x : ℂ) - w)⁻¹‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hb (sq_nonneg _)

theorem integrable_particleCoefficient_sq (s : AnchoredCountingState) (v : ℂ × Bool) :
    Integrable (fun x => ‖particleCoefficient x v‖ ^ 2) s.val.1.measure := by
  by_cases hv : v.1.im = 0
  · simp [particleCoefficient, hv]
  · cases hslot : v.2
    · simpa [particleCoefficient, hv, hslot, norm_pow] using (integrable_reciprocal_sq s hv).norm
    · simpa [particleCoefficient, hv, hslot, norm_pow, ← pow_mul] using (integrable_reciprocal_four s hv).norm

/-- Both value and spectral derivative slots have square-summable coefficients. -/
theorem summable_particleCoefficient_sq (s : AnchoredCountingState) (v : ℂ × Bool) :
    Summable (fun i : s.val.1.ParticleLabels =>
      ‖particleCoefficient (s.val.1.particleLocation i) v‖ ^ 2) :=
  (s.val.1.hasSum_particleLocations (integrable_particleCoefficient_sq s v)).summable

/-- Derivative coefficients are absolutely summable; this is stronger than
their square summability and supports differentiation of the L² series. -/
theorem summable_particleCoefficient_derivative_norm (s : AnchoredCountingState) (w : ℂ) :
    Summable (fun i : s.val.1.ParticleLabels =>
      ‖particleCoefficient (s.val.1.particleLocation i) (w, true)‖) := by
  by_cases hw : w.im = 0
  · simpa [particleCoefficient, hw] using
      (summable_zero : Summable (fun _ : s.val.1.ParticleLabels => (0 : ℝ)))
  · simpa [particleCoefficient, hw] using s.val.1.summable_norm_particleLocations
      (integrable_reciprocal_sq s hw)

theorem integrable_particleCoefficient_product (s : AnchoredCountingState) (v u : ℂ × Bool) :
    Integrable (fun x => particleCoefficient x v * particleCoefficient x u) s.val.1.measure := by
  apply ((integrable_particleCoefficient_sq s v).add
    (integrable_particleCoefficient_sq s u)).mono'
    ((measurable_particleCoefficient v).mul (measurable_particleCoefficient u)).aestronglyMeasurable
  filter_upwards [] with x
  simp only [norm_mul, Pi.add_apply]
  nlinarith [sq_nonneg (‖particleCoefficient x v‖ - ‖particleCoefficient x u‖),
    mul_nonneg (norm_nonneg (particleCoefficient x v)) (norm_nonneg (particleCoefficient x u))]

def particleKernel (s : AnchoredCountingState) (v u : ℂ × Bool) : ℂ :=
  ∫ x, particleCoefficient x v * particleCoefficient x u ∂s.val.1.measure

theorem hasSum_particleKernel (s : AnchoredCountingState) (v u : ℂ × Bool) :
    HasSum (fun i : s.val.1.ParticleLabels =>
      particleCoefficient (s.val.1.particleLocation i) v *
      particleCoefficient (s.val.1.particleLocation i) u) (particleKernel s v u) :=
  s.val.1.hasSum_particleLocations (integrable_particleCoefficient_product s v u)

theorem particleKernel_diagonal (s : AnchoredCountingState)
    (hlinear : anchoredLinearCoefficient s = 0) {w : ℂ} (hw : w.im ≠ 0) :
    particleKernel s (w, false) (w, false) = anchoredDerivative s w := by
  rw [anchoredDerivative_eq_integral s hw, hlinear]
  simp [particleKernel, particleCoefficient, hw, pow_two]

theorem particleKernel_interaction (s : AnchoredCountingState)
    {w u : ℂ} (hw : w.im ≠ 0) (hu : u.im ≠ 0) :
    particleKernel s (w, false) (u, true) = anchoredInteraction s w u := by
  rw [anchoredInteraction_eq_integral s hw hu]
  simp [particleKernel, particleCoefficient, hw, hu]

/-- The derivative slot is the actual derivative of the value coefficient. -/
theorem hasDerivAt_particleCoefficient (x : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    HasDerivAt (fun z => particleCoefficient x (z, false))
      (particleCoefficient x (w, true)) w := by
  simp only [particleCoefficient, hw, ↓reduceIte]
  apply (hasDerivAt_reciprocal x hw).congr_of_eventuallyEq
  have hR : 0 < |w.im| / 2 := by positivity
  filter_upwards [Metric.ball_mem_nhds w hR] with z hz
  simp [particleCoefficient, (half_imaginary_ball_bound w z hw hz).2]

def derivativeEnvelope (w : ℂ) : ℝ :=
  let δ := |w.im| / 2
  let M := ‖w‖ + δ
  1 + (2 * M) * (1 / δ) + (1 + M ^ 2) * (1 / δ) ^ 2

theorem derivativeEnvelope_nonneg (w : ℂ) : 0 ≤ derivativeEnvelope w := by
  unfold derivativeEnvelope
  positivity

/-- A summable deterministic envelope for the actual derivative on a complex
ball. The bound is uniform in the spectral parameter and in particle labels. -/
theorem particleCoefficient_derivative_ball_bound (x : ℝ)
    {w z : ℂ} (hw : w.im ≠ 0) (hz : z ∈ Metric.ball w (|w.im| / 2)) :
    ‖particleCoefficient x (z, true)‖ ≤ derivativeEnvelope w * nevanlinnaWeight x := by
  have hi := half_imaginary_ball_bound w z hw hz
  have hn : ‖z‖ ≤ ‖w‖ + |w.im| / 2 := by
    have ht : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
      simpa only [sub_add_cancel] using norm_add_le (z - w) w
    have hdist : ‖z - w‖ < |w.im| / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    linarith
  simpa only [particleCoefficient, hi.2, ↓reduceIte, derivativeEnvelope] using
    norm_reciprocal_sq_le_weight_uniform x (by positivity : 0 < |w.im| / 2) hi.1 hn

end GeneralizedBulk.Gaussian
