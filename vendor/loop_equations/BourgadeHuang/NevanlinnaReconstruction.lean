import BourgadeHuang.HierarchyCharacterization
import BourgadeHuang.FactorialTopology

/-!
# Reconstruction from a counting measure and one resolvent value

The value at `i` records the real centering and the weighted total particle mass.
The remaining kernel decays by one additional power at infinity. This is the
actual deterministic identity required before passing loop equations through a
joint limit of counting configurations and their anchored resolvents.
-/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

/-- The finite Nevanlinna weight. -/
def nevanlinnaWeight (a : ℝ) : ℝ := (1 + a ^ 2)⁻¹

/-- The remainder after subtracting the constant and linear anchor terms. -/
def anchoredResolventKernel (z : ℂ) (a : ℝ) : ℂ :=
  (nevanlinnaWeight a : ℂ) / ((a : ℂ) - z)

theorem nevanlinnaWeight_nonneg (a : ℝ) : 0 ≤ nevanlinnaWeight a := by
  dsimp [nevanlinnaWeight]
  positivity

theorem continuous_nevanlinnaWeight : Continuous nevanlinnaWeight := by
  exact (continuous_const.add (continuous_id.pow 2)).inv₀ (fun a => by positivity)

theorem real_sub_offReal_ne_zero (a : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (a : ℂ) - z ≠ 0 := by
  intro h
  have hh := congrArg Complex.im h
  simp at hh
  exact hz hh

/-- The exact one-particle anchored partial-fraction identity. -/
theorem reciprocal_anchor_decomposition (a : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ((a : ℂ) - z)⁻¹ = (a * nevanlinnaWeight a : ℝ) +
      z * (nevanlinnaWeight a : ℂ) + (1 + z ^ 2) * anchoredResolventKernel z a := by
  have ha : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
  have ha' : (1 + (a : ℂ) ^ 2) ≠ 0 := by exact_mod_cast ha
  simp only [anchoredResolventKernel, nevanlinnaWeight, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow]
  field_simp [ha', real_sub_offReal_ne_zero a hz]
  <;> ring

/-- The imaginary part at `i` is exactly the weighted particle mass. -/
theorem microscopicResolvent_im_I_eq_weight {N : ℕ} (x : Fin N → ℝ) (center : ℝ) :
    (microscopicResolvent x center Complex.I).im = ∑ i, nevanlinnaWeight (x i) := by
  rw [microscopicResolvent_im_eq]
  simp only [Complex.I_im, one_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp [nevanlinnaWeight, Complex.normSq_apply, pow_two]
  ring

/-- The real part at `i` is the corresponding real centering. -/
theorem microscopicResolvent_re_I_eq_weight {N : ℕ} (x : Fin N → ℝ) (center : ℝ) :
    (microscopicResolvent x center Complex.I).re =
      (∑ i, x i * nevanlinnaWeight (x i)) - center := by
  simp only [microscopicResolvent, Complex.sub_re, Complex.re_sum, Complex.ofReal_re]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.inv_re, Complex.normSq_apply, nevanlinnaWeight, div_eq_mul_inv, pow_two]
  ring_nf
  simp

/-- Every finite particle resolvent is determined by its counting measure and its
single value at `i`, through an absolutely integrable decaying kernel. -/
theorem microscopicResolvent_anchor_reconstruction {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    microscopicResolvent x center z =
      ((microscopicResolvent x center Complex.I).re : ℂ) +
      z * ((microscopicResolvent x center Complex.I).im : ℂ) +
      (1 + z ^ 2) * ∑ i, anchoredResolventKernel z (x i) := by
  rw [microscopicResolvent_re_I_eq_weight, microscopicResolvent_im_I_eq_weight]
  simp only [Complex.ofReal_sub, Complex.ofReal_sum, Finset.mul_sum]
  simp_rw [microscopicResolvent, reciprocal_anchor_decomposition _ hz]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

theorem continuous_anchoredResolventKernel {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (anchoredResolventKernel z) :=
  (Complex.continuous_ofReal.comp continuous_nevanlinnaWeight).div
    (Complex.continuous_ofReal.sub continuous_const) (fun a => real_sub_offReal_ne_zero a hz)

/-- Absolute integrability is controlled by the finite Nevanlinna weight. -/
theorem norm_anchoredResolventKernel_le (a : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ‖anchoredResolventKernel z a‖ ≤ nevanlinnaWeight a / |z.im| := by
  rw [anchoredResolventKernel, div_eq_mul_inv, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (nevanlinnaWeight_nonneg a)]
  simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left
    (norm_reciprocal_le_im a hz) (nevanlinnaWeight_nonneg a)

theorem integrable_anchoredResolventKernel (μ : Measure ℝ)
    (hweight : Integrable nevanlinnaWeight μ) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (anchoredResolventKernel z) μ := by
  apply (hweight.div_const |z.im|).mono'
    (continuous_anchoredResolventKernel hz).measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun a => norm_anchoredResolventKernel_le a hz)

/-- Uniform control at every off-real point follows from the single anchored value. -/
theorem norm_microscopicResolvent_le_anchor {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ‖microscopicResolvent x center z‖ ≤
      (1 + ‖z‖ + ‖1 + z ^ 2‖ / |z.im|) *
        ‖microscopicResolvent x center Complex.I‖ := by
  let A := microscopicResolvent x center Complex.I
  have him : 0 ≤ A.im := microscopicResolvent_im_nonneg x center (by simp)
  have hs : ‖∑ i, anchoredResolventKernel z (x i)‖ ≤ A.im / |z.im| := by
    calc
      _ ≤ ∑ i, ‖anchoredResolventKernel z (x i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, nevanlinnaWeight (x i) / |z.im| :=
        Finset.sum_le_sum (fun i _ => norm_anchoredResolventKernel_le _ hz)
      _ = A.im / |z.im| := by rw [← Finset.sum_div, ← microscopicResolvent_im_I_eq_weight x center]
  rw [microscopicResolvent_anchor_reconstruction x center hz]
  calc
    _ ≤ ‖(A.re : ℂ)‖ + ‖z * (A.im : ℂ)‖ + ‖(1 + z ^ 2) * ∑ i, anchoredResolventKernel z (x i)‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ = |A.re| + ‖z‖ * A.im + ‖1 + z ^ 2‖ * ‖∑ i, anchoredResolventKernel z (x i)‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg him]
    _ ≤ ‖A‖ + ‖z‖ * ‖A‖ + ‖1 + z ^ 2‖ * (‖A‖ / |z.im|) := by
      exact add_le_add (add_le_add (Complex.abs_re_le_norm A)
        (mul_le_mul_of_nonneg_left (Complex.im_le_norm A) (norm_nonneg _)))
        (mul_le_mul_of_nonneg_left
          (hs.trans (div_le_div_of_nonneg_right (Complex.im_le_norm A) (abs_nonneg _)))
          (norm_nonneg _))
    _ = _ := by ring

end BourgadeHuang
