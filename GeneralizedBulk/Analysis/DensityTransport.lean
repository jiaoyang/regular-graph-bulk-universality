import Mathlib

/-! Actual density transport under measurable coordinate equivalences. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace GeneralizedBulk.Analysis
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem map_withDensity_equiv (μ : Measure X) (e : X ≃ᵐ Y) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  calc
    _ = ∫⁻ x, φ (e x) ∂μ.withDensity f := lintegral_map hφ e.measurable
    _ = ∫⁻ x, f x * φ (e x) ∂μ :=
      lintegral_withDensity_eq_lintegral_mul μ hf (hφ.comp e.measurable)
    _ = ∫⁻ y, f (e.symm y) * φ y ∂μ.map e := by
      have h := lintegral_map (μ := μ) (f := fun y => f (e.symm y) * φ y)
        ((hf.comp e.symm.measurable).mul hφ) e.measurable
      simpa only [e.symm_apply_apply] using h.symm
    _ = _ := (lintegral_withDensity_eq_lintegral_mul (μ.map e) (hf.comp e.symm.measurable) hφ).symm

theorem map_realDensity_scaled_reference (μ : Measure X) (e : X ≃ᵐ X) (r : ℝ) (hr : 0 ≤ r)
    (hmap : μ.map e = ENNReal.ofReal r • μ) (f : X → ℝ) (hf : Measurable f) :
    (μ.withDensity (fun x => ENNReal.ofReal (f x))).map e =
      μ.withDensity (fun y => ENNReal.ofReal (r * f (e.symm y))) := by
  rw [map_withDensity_equiv μ e _ hf.ennreal_ofReal, hmap, withDensity_smul_measure]
  calc
    _ = μ.withDensity (ENNReal.ofReal r • (fun y => ENNReal.ofReal (f (e.symm y)))) :=
      (withDensity_smul (ENNReal.ofReal r) (hf.comp e.symm.measurable).ennreal_ofReal).symm
    _ = _ := by
      congr 1
      funext y
      exact (ENNReal.ofReal_mul hr).symm

end GeneralizedBulk.Analysis
