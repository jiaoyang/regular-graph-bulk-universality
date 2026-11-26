import GeneralizedBulk.Matrix.LimitNormalization
import GeneralizedBulk.Matrix.EntryEnvelope

/-! Actual calibrated means and their rank-shift perturbation bounds. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Graph
open Exterior GeneralizedSwitching

def calibratedMeanEnvelope (parameters : Parameters) : ℝ :=
  2 * |parameters.center| + 2 * parameters.scale + parameters.r

theorem calibratedMeanEnvelope_nonneg (parameters : Parameters) :
    0 ≤ calibratedMeanEnvelope parameters := by
  unfold calibratedMeanEnvelope
  have := parameters.scale_pos
  have := parameters.r_pos
  positivity

/-- The deterministic mean has a uniform linear scalar envelope. -/
theorem calibratedMean_entryBound (parameters : Parameters) (s : ℂ) :
    EntryBound (calibratedMean parameters s) (calibratedMeanEnvelope parameters * (1 + ‖s‖)) := by
  let g : ℂ := (parameters.center : ℂ) + (parameters.scale : ℂ) * s
  let b : ℂ := (parameters.p : ℂ) * g + parameters.r
  have hg : ‖g‖ ≤ |parameters.center| + parameters.scale * ‖s‖ := by
    exact (norm_add_le _ _).trans (by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos parameters.scale_pos]
      exact le_refl _)
  have hb : ‖b‖ ≤ ‖g‖ + parameters.r := by
    calc
      _ ≤ ‖(parameters.p : ℂ)‖ * ‖g‖ + ‖(parameters.r : ℂ)‖ := by
        simpa only [norm_mul] using norm_add_le ((parameters.p : ℂ) * g) (parameters.r : ℂ)
      _ ≤ ‖g‖ + parameters.r := by
        rw [Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos parameters.r_pos]
        have hmul := mul_le_mul_of_nonneg_right parameters.abs_p_lt_one.le (norm_nonneg g)
        simpa only [one_mul] using add_le_add_right hmul parameters.r
  have hgn : ‖g‖ ≤ calibratedMeanEnvelope parameters * (1 + ‖s‖) := by
    have hscale := parameters.scale_pos.le
    have hr := parameters.r_pos.le
    have hs := norm_nonneg s
    have ha := abs_nonneg parameters.center
    dsimp [calibratedMeanEnvelope]
    nlinarith
  have hbn : ‖b‖ ≤ calibratedMeanEnvelope parameters * (1 + ‖s‖) := by
    have hscale := parameters.scale_pos.le
    have hr := parameters.r_pos.le
    have hs := norm_nonneg s
    have ha := abs_nonneg parameters.center
    dsimp [calibratedMeanEnvelope]
    nlinarith
  have hzero : 0 ≤ calibratedMeanEnvelope parameters * (1 + ‖s‖) :=
    mul_nonneg (calibratedMeanEnvelope_nonneg parameters) (by positivity)
  intro i j
  change ‖meanMatrix g b 0 i j‖ ≤ _
  fin_cases i <;> fin_cases j <;> norm_num [meanMatrix] <;>
    first | exact hgn | exact hbn | exact hzero


/-- Every covariance entry has norm at most one. -/
theorem entryBound_covarianceMatrix (parameters : Parameters) :
    EntryBound (covarianceMatrix (parameters.p : ℂ)) 1 := by
  intro i j
  rw [covarianceMatrix_eq]
  have hp : ‖(parameters.p : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using parameters.abs_p_lt_one.le
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,norm_zero,norm_one] <;>
    first | exact hp | norm_num

/-- The affine mean difference is exactly the scalar difference times the
endpoint covariance; its fixed edge background cancels. -/
theorem calibratedMean_sub (parameters : Parameters) (s t : ℂ) :
    calibratedMean parameters t - calibratedMean parameters s =
      ((parameters.scale : ℂ) * (t - s)) • covarianceMatrix (parameters.p : ℂ) := by
  have heq (u : ℂ) : calibratedMean parameters u =
      ((parameters.center : ℂ) + (parameters.scale : ℂ) * u) • covarianceMatrix (parameters.p : ℂ) +
        (parameters.r : ℂ) • edgeMatrix := (meanMatrix_from_covariance _ _ _).symm
  rw [heq,heq]
  ext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

/-- The scalar rank bound transfers directly to an entrywise mean shift. -/
theorem calibratedMean_sub_entryBound (parameters : Parameters) (s t : ℂ) :
    EntryBound (calibratedMean parameters t - calibratedMean parameters s)
      (parameters.scale * ‖t - s‖) := by
  rw [calibratedMean_sub]
  have h := (entryBound_covarianceMatrix parameters).smul ((parameters.scale : ℂ) * (t - s))
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos parameters.scale_pos,mul_one] using h

end GeneralizedBulk.Graph
