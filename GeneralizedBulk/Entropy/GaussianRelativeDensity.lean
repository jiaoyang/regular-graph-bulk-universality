import GeneralizedBulk.Analysis.PiDensity
import GeneralizedBulk.Entropy.HermiteMultivariate
import GeneralizedBulk.Entropy.MehlerKernelCalculus

/-! The smoothing kernel is the actual Gaussian relative density. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis

def gaussianRelative (mean : ℝ) (variance : ℝ≥0) (x : ℝ) : ℝ :=
  gaussianPDFReal mean variance x / gaussianPDFReal 0 1 x

theorem gaussianRelative_nonneg (mean : ℝ) (variance : ℝ≥0) (x : ℝ) :
    0 ≤ gaussianRelative mean variance x :=
  div_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)

theorem measurable_gaussianRelative (mean : ℝ) (variance : ℝ≥0) :
    Measurable (gaussianRelative mean variance) :=
  (measurable_gaussianPDFReal mean variance).div (measurable_gaussianPDFReal 0 1)

/-- This is an equality of measures, rather than a stipulated density. -/
theorem gaussianReal_eq_standardNormal_withDensity (mean : ℝ) (variance : ℝ≥0)
    (hvar : variance ≠ 0) :
    gaussianReal mean variance =
      standardNormal.withDensity (fun x => ENNReal.ofReal (gaussianRelative mean variance x)) := by
  rw [standardNormal, gaussianReal_of_var_ne_zero 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0),
    ← withDensity_mul _ (measurable_gaussianPDF 0 1)
      (measurable_gaussianRelative mean variance).ennreal_ofReal,
    gaussianReal_of_var_ne_zero mean hvar]
  congr 1
  funext x
  change ENNReal.ofReal (gaussianPDFReal mean variance x) =
    ENNReal.ofReal (gaussianPDFReal 0 1 x) * ENNReal.ofReal (gaussianRelative mean variance x)
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x)]
  congr 1
  unfold gaussianRelative
  field_simp [ne_of_gt (gaussianPDFReal_pos 0 1 x one_ne_zero)]

theorem integrable_gaussianRelative (mean : ℝ) (variance : ℝ≥0) (hvar : variance ≠ 0) :
    Integrable (gaussianRelative mean variance) standardNormal := by
  have hi : Integrable (fun _ : ℝ => (1 : ℝ))
      (standardNormal.withDensity (fun x => ENNReal.ofReal (gaussianRelative mean variance x))) := by
    rw [← gaussianReal_eq_standardNormal_withDensity mean variance hvar]
    exact integrable_const 1
  have h := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianRelative mean variance).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hi
  simpa only [ENNReal.toReal_ofReal (gaussianRelative_nonneg mean variance _),
    smul_eq_mul, mul_one] using h

theorem integral_gaussianRelative (mean : ℝ) (variance : ℝ≥0) (hvar : variance ≠ 0) :
    (∫ x, gaussianRelative mean variance x ∂standardNormal) = 1 := by
  have h := integral_withDensity_eq_integral_toReal_smul
    (μ := standardNormal) (measurable_gaussianRelative mean variance).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) (fun _ : ℝ => (1 : ℝ))
  rw [← gaussianReal_eq_standardNormal_withDensity mean variance hvar] at h
  simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul,
    ENNReal.toReal_ofReal (gaussianRelative_nonneg mean variance _), mul_one] using h.symm

/-- Completing the square gives the logarithmic kernel formula. -/
theorem gaussianRelative_eq_exp (mean : ℝ) (variance : ℝ≥0) (hvar : variance ≠ 0) (x : ℝ) :
    gaussianRelative mean variance x = Real.exp (-(Real.log variance / 2) +
      (x ^ 2 / 2 - (x - mean) ^ 2 / (2 * variance))) := by
  have hv : 0 < (variance : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hvar)
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hvs : Real.sqrt (variance : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hv)
  have he : Real.exp (-(x - mean) ^ 2 / (2 * variance)) /
      Real.exp (-(x ^ 2) / 2) =
      Real.exp (x ^ 2 / 2 - (x - mean) ^ 2 / (2 * variance)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hh : Real.exp (-(Real.log (variance : ℝ) / 2)) = (Real.sqrt (variance : ℝ))⁻¹ := by
    rw [Real.exp_neg, Real.exp_half, Real.exp_log hv]
  calc
    gaussianRelative mean variance x = (Real.sqrt (variance : ℝ))⁻¹ *
        (Real.exp (-(x - mean) ^ 2 / (2 * variance)) / Real.exp (-(x ^ 2) / 2)) := by
      unfold gaussianRelative gaussianPDFReal
      simp only [NNReal.coe_one, mul_one, sub_zero]
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
      field_simp
      ring
    _ = _ := by rw [he, ← hh, ← Real.exp_add]

theorem gaussianRelative_smoothing (a y z : ℝ) (ha : 0 < 1 - a ^ 2) :
    gaussianRelative (a * y) ⟨1 - a ^ 2, ha.le⟩ z = kernel 1 (z * y) (y ^ 2 + z ^ 2) a := by
  rw [gaussianRelative_eq_exp _ _ (by
    intro h
    exact (ne_of_gt ha) (congrArg (fun r : ℝ≥0 => (r : ℝ)) h))]
  unfold kernel logKernel
  congr 1
  dsimp
  field_simp
  ring

end GeneralizedBulk.Entropy.Mehler
