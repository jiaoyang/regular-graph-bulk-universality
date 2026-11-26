import GeneralizedBulk.Spectral.PairedAngularLogIntegrable
import GeneralizedBulk.Spectral.TreeLogFactor

/-! The actual Kesten–McKay logarithmic potential evaluated at the small-root
spectral parameter. -/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Spectral

theorem logSeriesParameter_treeLogParameter (d : ℝ) (hd : 3 ≤ d) (g : ℂ) :
    logSeriesParameter d (treeLogParameter d g) = g ^ 2 := by
  rw [logSeriesParameter, treeLogParameter_sq d hd]
  have hc : -((d - 1 : ℝ) : ℂ) * ((-1 / (d - 1) : ℝ) : ℂ) = 1 := by
    have hq : d - 1 ≠ 0 := by linarith
    rw [← Complex.ofReal_neg, ← Complex.ofReal_mul]
    norm_cast
    field_simp
  calc
    _ = g ^ 2 * (-((d - 1 : ℝ) : ℂ) * ((-1 / (d - 1) : ℝ) : ℂ)) := by ring
    _ = _ := by rw [hc, mul_one]

theorem logNorm_treeSpectralPoint (d : ℝ) (hd : 3 ≤ d) (g : ℂ) (hg : g ≠ 0)
    (hu : ‖treeLogParameter d g‖ < 1) (theta : ℝ) :
    Real.log ‖treeSpectralPoint d g - ((radius d * Real.sin theta : ℝ) : ℂ)‖ =
      -Real.log ‖g‖ + (pairedLog (treeLogParameter d g) theta).re := by
  have hs (t : ℝ) : ‖treeLogParameter d g * circlePoint 1 t‖ < 1 := by
    simpa only [norm_mul, circlePoint_norm, abs_one, mul_one] using hu
  have hA : 1 - treeLogParameter d g * circlePoint 1 theta ≠ 0 := by
    intro hz
    have hh : treeLogParameter d g * circlePoint 1 theta = 1 := (sub_eq_zero.mp hz).symm
    have ht := hs theta
    rw [hh, norm_one] at ht
    exact lt_irrefl 1 ht
  have hB : 1 + treeLogParameter d g * circlePoint 1 (-theta) ≠ 0 := by
    intro hz
    have hh : treeLogParameter d g * circlePoint 1 (-theta) = -1 := eq_neg_of_add_eq_zero_right hz
    have ht := hs (-theta)
    rw [hh, norm_neg, norm_one] at ht
    exact lt_irrefl 1 ht
  rw [treeSpectralPoint_factor d hd g hg, norm_mul, norm_mul, norm_neg, norm_inv,
    Real.log_mul (inv_ne_zero (norm_ne_zero_iff.mpr hg))
      (mul_ne_zero (norm_ne_zero_iff.mpr hA) (norm_ne_zero_iff.mpr hB)),
    Real.log_mul (norm_ne_zero_iff.mpr hA) (norm_ne_zero_iff.mpr hB), Real.log_inv]
  simp only [pairedLog, Complex.add_re, Complex.log_re]

/-- Exact actual potential identity. The integral is against the normalized
angular law constructed from the literal Kesten–McKay density. -/
theorem integral_logNorm_treeSpectralPoint (d : ℝ) (hd : 3 ≤ d) (g : ℂ) (hg : g ≠ 0)
    (hu : ‖treeLogParameter d g‖ < 1) :
    (∫ theta, Real.log ‖treeSpectralPoint d g - ((radius d * Real.sin theta : ℝ) : ℂ)‖ ∂angularLaw d) =
      -Real.log ‖g‖ - (d - 2) / 2 * Real.log ‖1 - g ^ 2‖ := by
  letI := angularLaw_isProbability d hd
  simp_rw [logNorm_treeSpectralPoint d hd g hg hu]
  have hi : Integrable (fun theta => (pairedLog (treeLogParameter d g) theta).re) (angularLaw d) :=
    (integrable_pairedLog d hd _ hu).re
  rw [integral_add (integrable_const _) hi,
    integral_const, integral_pairedLog_re d hd _ hu, logSeriesParameter_treeLogParameter d hd]
  simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul]
  ring

end GeneralizedBulk.KestenMcKay
