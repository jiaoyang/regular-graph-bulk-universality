import Mathlib

/-! Entropy additivity for the actual product of positive probability densities. -/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.Analysis
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem product_density_entropy (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (f : X → ℝ) (g : Y → ℝ) (hf : Integrable f μ) (hg : Integrable g ν)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ y, 0 < g y)
    (hflog : Integrable (fun x => f x * Real.log (f x)) μ)
    (hglog : Integrable (fun y => g y * Real.log (g y)) ν)
    (hfnorm : ∫ x, f x ∂μ = 1) (hgnorm : ∫ y, g y ∂ν = 1) :
    Integrable (fun z : X × Y => f z.1 * g z.2 * Real.log (f z.1 * g z.2)) (μ.prod ν) ∧
    -(∫ z : X × Y, f z.1 * g z.2 * Real.log (f z.1 * g z.2) ∂μ.prod ν) =
      -(∫ x, f x * Real.log (f x) ∂μ) - ∫ y, g y * Real.log (g y) ∂ν := by
  have he (z : X × Y) : f z.1 * g z.2 * Real.log (f z.1 * g z.2) =
      (f z.1 * Real.log (f z.1)) * g z.2 + f z.1 * (g z.2 * Real.log (g z.2)) := by
    rw [Real.log_mul (hfp _).ne' (hgp _).ne']
    ring
  simp_rw [he]
  refine ⟨(hflog.mul_prod hg).add (hf.mul_prod hglog), ?_⟩
  rw [integral_add (hflog.mul_prod hg) (hf.mul_prod hglog),
    integral_prod_mul (fun x => f x * Real.log (f x)) g,
    integral_prod_mul f (fun y => g y * Real.log (g y)), hfnorm, hgnorm]
  ring

end GeneralizedBulk.Analysis
