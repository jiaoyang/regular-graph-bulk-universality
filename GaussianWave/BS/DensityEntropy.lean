import GaussianWave.Foundation

/-!
# Gibbs' inequality for genuine integrable probability densities

This is an analytic component of the large-time endpoint in the upper-bound
blueprint. It does not assume any BS entropy inequality or Gaussianity.
Every integral required for subtraction is explicitly integrable.
-/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

def densityEntropy {E : Type*} [MeasurableSpace E]
    (m : Measure E) (f : E → ℝ) : ℝ := -(∫ x, f x * Real.log (f x) ∂m)

/-- The elementary integrand underlying relative entropy nonnegativity. -/
theorem gibbs_integrand_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ a * Real.log a - a * Real.log b - a + b := by
  by_cases hzero : a = 0
  · simp [hzero, hb.le]
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    have hlog := Real.log_le_sub_one_of_pos (div_pos hb hapos)
    rw [Real.log_div (ne_of_gt hb) hzero] at hlog
    have hm := mul_le_mul_of_nonneg_left hlog ha
    have heq : a * (b / a - 1) = b - a := by field_simp
    rw [heq] at hm
    nlinarith

/-- Maximum entropy is bounded by the cross entropy against any strictly
positive normalized reference density. This is proved from the logarithm
inequality, rather than postulated through an entropy interface. -/
theorem densityEntropy_le_crossEntropy
    {E : Type*} [MeasurableSpace E] (m : Measure E) (f g : E → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 < g x)
    (hfi : Integrable f m) (hgi : Integrable g m)
    (hf : (∫ x, f x ∂m) = 1) (hg : (∫ x, g x ∂m) = 1)
    (hflog : Integrable (fun x => f x * Real.log (f x)) m)
    (hcross : Integrable (fun x => f x * Real.log (g x)) m) :
    densityEntropy m f ≤ -(∫ x, f x * Real.log (g x) ∂m) := by
  have hn : 0 ≤ ∫ x,
      f x * Real.log (f x) - f x * Real.log (g x) - f x + g x ∂m :=
    integral_nonneg (fun x => gibbs_integrand_nonneg _ _ (hf0 x) (hg0 x))
  rw [integral_add (f := fun x =>
    f x * Real.log (f x) - f x * Real.log (g x) - f x)
    ((hflog.sub hcross).sub hfi) hgi,
    integral_sub (f := fun x => f x * Real.log (f x) - f x * Real.log (g x))
      (hflog.sub hcross) hfi,
    integral_sub (f := fun x => f x * Real.log (f x)) hflog hcross, hf, hg] at hn
  unfold densityEntropy
  linarith

/-- Matching the sufficient quadratic statistics of a Gaussian reference
identifies its cross entropy. This is pure integration of the stated log
density formula; no entropy comparison is assumed. -/
theorem crossEntropy_eq_of_quadratic_log_density
    {E : Type*} [MeasurableSpace E] (m : Measure E) (f g q : E → ℝ)
    (hfi : Integrable f m) (hgi : Integrable g m)
    (hfq : Integrable (fun x => f x * q x) m)
    (hgq : Integrable (fun x => g x * q x) m)
    (hf : (∫ x, f x ∂m) = 1) (hg : (∫ x, g x ∂m) = 1)
    (hmoment : (∫ x, f x * q x ∂m) = ∫ x, g x * q x ∂m)
    (A B : ℝ) (hlog : ∀ x, Real.log (g x) = A - B * q x) :
    (∫ x, f x * Real.log (g x) ∂m) =
      ∫ x, g x * Real.log (g x) ∂m := by
  have heq (p : E → ℝ) : (fun x => p x * Real.log (g x)) =
      (fun x => A * p x - B * (p x * q x)) := by
    funext x
    rw [hlog]
    ring
  rw [heq f, heq g,
    integral_sub (f := fun x => A * f x) (hfi.const_mul A) (hfq.const_mul B),
    integral_sub (f := fun x => A * g x) (hgi.const_mul A) (hgq.const_mul B)]
  simp only [integral_const_mul, hf, hg, hmoment]

end GaussianWave.BS
