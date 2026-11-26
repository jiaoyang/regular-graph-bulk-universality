import GeneralizedBulk.Analysis.NoLinearTerm

/-! The upper-half-plane factorization selects the positive normalization root. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Analysis

/-- On the closed upper half plane the other quadratic root stays at least
unit distance away. -/
theorem one_le_norm_add_I (z : ℂ) (hz : 0 ≤ z.im) : 1 ≤ ‖z + Complex.I‖ := by
  have hi := Complex.abs_im_le_norm (z + Complex.I)
  simp only [Complex.add_im, Complex.I_im] at hi
  rw [abs_of_nonneg (by linarith)] at hi
  linarith

/-- The quadratic switching polynomial controls the actual normalization
error, with no square-root choice or inversion of the matrix field. -/
theorem norm_sub_I_le_norm_sq_add_one (z : ℂ) (hz : 0 ≤ z.im) :
    ‖z - Complex.I‖ ≤ ‖z ^ 2 + 1‖ := by
  have hfactor : (z - Complex.I) * (z + Complex.I) = z ^ 2 + 1 := by
    calc
      _ = z ^ 2 - Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hnorm := mul_le_mul_of_nonneg_left (one_le_norm_add_I z hz) (norm_nonneg (z - Complex.I))
  rw [mul_one, ← norm_mul, hfactor] at hnorm
  exact hnorm

/-- Vanishing L1 quadratic residual implies genuine L1 normalization at i
for upper-half-plane scalar fields. -/
theorem integral_norm_sub_I_tendsto_zero_of_quadratic
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : ℕ → Ω → ℂ) (hs : ∀ n, AEStronglyMeasurable (s n) P)
    (hupper : ∀ n, ∀ᵐ x ∂P, 0 ≤ (s n x).im)
    (hpoly : ∀ n, Integrable (fun x => s n x ^ 2 + 1) P)
    (hzero : Tendsto (fun n => ∫ x, ‖s n x ^ 2 + 1‖ ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖s n x - Complex.I‖ ∂P) atTop (𝓝 0) := by
  have hi (n) : Integrable (fun x => ‖s n x - Complex.I‖) P := by
    apply (hpoly n).norm.mono' ((hs n).sub aestronglyMeasurable_const).norm
    filter_upwards [hupper n] with x hx
    rw [norm_norm]
    exact norm_sub_I_le_norm_sq_add_one (s n x) hx
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) _ hzero
  intro n
  exact integral_mono_ae (hi n) (hpoly n).norm
    ((hupper n).mono (fun x hx => norm_sub_I_le_norm_sq_add_one (s n x) hx))

end GeneralizedBulk.Analysis
