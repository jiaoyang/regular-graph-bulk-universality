import GeneralizedBulk.Gaussian.ParticleKernels
import GeneralizedBulk.Analysis.SummableRandom

/-!
# Pathwise analytic versions of the marked series

Anchor the conditionally convergent series at `i`. Its difference from that
anchor is absolutely summable with a deterministic particle-weight envelope.
This produces genuine sample analytic functions on one common full-measure set,
rather than unrelated L² representatives for each spectral parameter.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology BigOperators

namespace GeneralizedBulk.Gaussian

def anchorCorrection (x : ℝ) (w : ℂ) : ℂ :=
  if w.im = 0 then 0 else
    particleCoefficient x (w, false) - particleCoefficient x (Complex.I, false)

theorem anchorCorrection_factor (x : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    anchorCorrection x w = (w - Complex.I) * ((x : ℂ) - w)⁻¹ *
      ((x : ℂ) - Complex.I)⁻¹ := by
  simp only [anchorCorrection, particleCoefficient, hw, ↓reduceIte, Complex.I_im,
    one_ne_zero]
  field_simp [real_sub_ne_zero x hw, real_sub_ne_zero x (by simp : Complex.I.im ≠ 0)]

def correctionEnvelope (δ M : ℝ) : ℝ :=
  (M + 1) * (1 + 2 * M * (1 / δ) + (1 + M ^ 2) * (1 / δ) ^ 2 + 5)

theorem anchorCorrection_bound (x : ℝ) {w : ℂ} {δ M : ℝ}
    (hδ : 0 < δ) (him : δ ≤ |w.im|) (hnorm : ‖w‖ ≤ M) :
    ‖anchorCorrection x w‖ ≤ correctionEnvelope δ M * nevanlinnaWeight x := by
  have hw : w.im ≠ 0 := abs_pos.mp (lt_of_lt_of_le hδ him)
  have hM : 0 ≤ M := (norm_nonneg _).trans hnorm
  have hdiff : ‖w - Complex.I‖ ≤ M + 1 :=
    (norm_sub_le _ _).trans (by simpa using add_le_add_right hnorm 1)
  have hprod : ‖((x : ℂ) - w)⁻¹‖ * ‖((x : ℂ) - Complex.I)⁻¹‖ ≤
      ‖((x : ℂ) - w)⁻¹‖ ^ 2 + ‖((x : ℂ) - Complex.I)⁻¹‖ ^ 2 := by
    nlinarith [sq_nonneg (‖((x : ℂ) - w)⁻¹‖ - ‖((x : ℂ) - Complex.I)⁻¹‖),
      mul_nonneg (norm_nonneg (((x : ℂ) - w)⁻¹)) (norm_nonneg (((x : ℂ) - Complex.I)⁻¹))]
  have hwbound := norm_reciprocal_sq_le_weight_uniform x hδ him hnorm
  have hibound := norm_reciprocal_sq_le_weight_uniform x (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) ≤ |Complex.I.im|) (by simp : ‖Complex.I‖ ≤ (1 : ℝ))
  simp only [norm_pow] at hwbound hibound
  norm_num at hibound
  have hIbound : ‖((x : ℂ) - Complex.I)⁻¹‖ ^ 2 ≤ 5 * nevanlinnaWeight x := by
    simpa only [norm_inv, inv_pow] using hibound
  rw [anchorCorrection_factor x hw, norm_mul, norm_mul]
  calc
    _ = ‖w - Complex.I‖ *
        (‖((x : ℂ) - w)⁻¹‖ * ‖((x : ℂ) - Complex.I)⁻¹‖) := by ring
    _ ≤ (M + 1) * (‖((x : ℂ) - w)⁻¹‖ ^ 2 +
        ‖((x : ℂ) - Complex.I)⁻¹‖ ^ 2) :=
      mul_le_mul hdiff hprod (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ ≤ (M + 1) * ((1 + 2 * M * (1 / δ) + (1 + M ^ 2) * (1 / δ) ^ 2) *
        nevanlinnaWeight x + 5 * nevanlinnaWeight x) :=
      mul_le_mul_of_nonneg_left (add_le_add hwbound hIbound) (by positivity)
    _ = _ := by unfold correctionEnvelope; ring

theorem hasDerivAt_anchorCorrection (x : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    HasDerivAt (anchorCorrection x) (particleCoefficient x (w, true)) w := by
  apply ((hasDerivAt_particleCoefficient x hw).sub_const
    (particleCoefficient x (Complex.I, false))).congr_of_eventuallyEq
  have hR : 0 < |w.im| / 2 := by positivity
  filter_upwards [Metric.ball_mem_nhds w hR] with z hz
  simp [anchorCorrection, (half_imaginary_ball_bound w z hw hz).2]

/-- A concrete analytic function; the anchor may be the actual L² series value. -/
def anchoredMarkedEntry (s : AnchoredCountingState) (anchor sigma : ℂ)
    (mark : s.val.1.ParticleLabels → ℂ) (w : ℂ) : ℂ :=
  if w.im = 0 then 0 else anchor +
    ∑' i, sigma * anchorCorrection (s.val.1.particleLocation i) w * mark i

theorem summable_anchorCorrection (s : AnchoredCountingState) (sigma : ℂ)
    (mark : s.val.1.ParticleLabels → ℂ)
    (hweight : Summable (fun i => nevanlinnaWeight (s.val.1.particleLocation i) * ‖mark i‖))
    {w : ℂ} (hw : w.im ≠ 0) :
    Summable (fun i => sigma * anchorCorrection (s.val.1.particleLocation i) w * mark i) := by
  let C := ‖sigma‖ * correctionEnvelope |w.im| ‖w‖
  apply Summable.of_norm_bounded _ (hweight.mul_left C)
  intro i
  simp only [norm_mul]
  have hb := anchorCorrection_bound (s.val.1.particleLocation i)
    (abs_pos.mpr hw) (le_refl |w.im|) (le_refl ‖w‖)
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    (norm_nonneg _)).trans_eq (by dsimp [C]; ring)

/-- Absolute convergence of the anchor correction produces an actual complex
derivative at every nonreal point on the same weighted-summability event. -/
theorem hasDerivAt_anchoredMarkedEntry (s : AnchoredCountingState) (anchor sigma : ℂ)
    (mark : s.val.1.ParticleLabels → ℂ)
    (hweight : Summable (fun i => nevanlinnaWeight (s.val.1.particleLocation i) * ‖mark i‖))
    {w : ℂ} (hw : w.im ≠ 0) :
    HasDerivAt (anchoredMarkedEntry s anchor sigma mark)
      (∑' i, sigma * particleCoefficient (s.val.1.particleLocation i) (w, true) * mark i) w := by
  let u : s.val.1.ParticleLabels → ℝ := fun i =>
    (‖sigma‖ * derivativeEnvelope w) *
      (nevanlinnaWeight (s.val.1.particleLocation i) * ‖mark i‖)
  have hu : Summable u := hweight.mul_left _
  have hR : 0 < |w.im| / 2 := by positivity
  have hder (i : s.val.1.ParticleLabels) (z : ℂ) (hz : z ∈ Metric.ball w (|w.im| / 2)) :
      HasDerivAt (fun y => sigma * anchorCorrection (s.val.1.particleLocation i) y * mark i)
        (sigma * particleCoefficient (s.val.1.particleLocation i) (z, true) * mark i) z :=
    ((hasDerivAt_anchorCorrection _ (half_imaginary_ball_bound w z hw hz).2).const_mul sigma).mul_const _
  have hbound (i : s.val.1.ParticleLabels) (z : ℂ) (hz : z ∈ Metric.ball w (|w.im| / 2)) :
      ‖sigma * particleCoefficient (s.val.1.particleLocation i) (z, true) * mark i‖ ≤ u i := by
    simp only [norm_mul]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (particleCoefficient_derivative_ball_bound _ hw hz) (norm_nonneg _))
      (norm_nonneg _)).trans_eq (by dsimp [u]; ring)
  have hd := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball w _).isPreconnected hder hbound (Metric.mem_ball_self hR)
    (summable_anchorCorrection s sigma mark hweight hw) (Metric.mem_ball_self hR)
  apply (hd.const_add anchor).congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds w hR] with z hz
  simp [anchoredMarkedEntry, (half_imaginary_ball_bound w z hw hz).2]

@[simp] theorem anchoredMarkedEntry_at_I (s : AnchoredCountingState) (anchor sigma : ℂ)
    (mark : s.val.1.ParticleLabels → ℂ) :
    anchoredMarkedEntry s anchor sigma mark Complex.I = anchor := by
  simp [anchoredMarkedEntry, anchorCorrection]

/-- Gaussian marks with a uniform expected norm yield one common full-measure
set on which the anchored series is analytic at all nonreal parameters. -/
theorem ae_differentiable_anchoredMarkedEntry
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : AnchoredCountingState) (anchor : Ω → ℂ) (sigma : ℂ)
    (mark : s.val.1.ParticleLabels → Ω → ℂ) (B : ℝ)
    (hmark : ∀ i, Integrable (mark i) μ)
    (hbound : ∀ i, (∫ ω, ‖mark i ω‖ ∂μ) ≤ B) :
    ∀ᵐ ω ∂μ, ∀ w : ℂ, w.im ≠ 0 →
      DifferentiableAt ℂ (anchoredMarkedEntry s (anchor ω) sigma (fun i => mark i ω)) w := by
  have hs := GeneralizedBulk.Analysis.ae_weighted_summable μ mark _ B hmark
    (fun i => nevanlinnaWeight_nonneg _) s.summable_particle_weight hbound
  filter_upwards [hs] with ω hω
  intro w hw
  exact (hasDerivAt_anchoredMarkedEntry s (anchor ω) sigma _ hω hw).differentiableAt

end GeneralizedBulk.Gaussian
