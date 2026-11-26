import GeneralizedBulk.Entropy.GaussianVolumeDensity
import GeneralizedBulk.Gaussian.FiniteVector

/-! Actual nonsingular Gaussian densities under linear coordinate transport. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite
variable {I : Type*} [Fintype I] [DecidableEq I]

def matrixEquiv (M : Matrix I I ℝ) (hM : M.det ≠ 0) : (I → ℝ) ≃L[ℝ] (I → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { Matrix.toLin' M with
      invFun := M⁻¹.mulVec
      left_inv := fun x => by
        change M⁻¹.mulVec (M.mulVec x) = x
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]
      right_inv := fun x => by
        change M.mulVec (M⁻¹.mulVec x) = x
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec] }

@[simp] theorem matrixEquiv_apply (M : Matrix I I ℝ) (hM : M.det ≠ 0) (x : I → ℝ) :
    matrixEquiv M hM x = M.mulVec x := rfl
@[simp] theorem matrixEquiv_symm_apply (M : Matrix I I ℝ) (hM : M.det ≠ 0) (x : I → ℝ) :
    (matrixEquiv M hM).symm x = M⁻¹.mulVec x := rfl

def matrixMeasurableEquiv (M : Matrix I I ℝ) (hM : M.det ≠ 0) : (I → ℝ) ≃ᵐ (I → ℝ) :=
  (matrixEquiv M hM).toHomeomorph.toMeasurableEquiv

def linearGaussianPDF (M : Matrix I I ℝ) (x : I → ℝ) : ℝ :=
  |M.det|⁻¹ * standardGaussianPDF (M⁻¹.mulVec x)

theorem linearGaussianPDF_pos (M : Matrix I I ℝ) (hM : M.det ≠ 0) (x : I → ℝ) :
    0 < linearGaussianPDF M x :=
  mul_pos (inv_pos.mpr (abs_pos.mpr hM)) (standardGaussianPDF_pos _)

theorem measurable_linearGaussianPDF (M : Matrix I I ℝ) : Measurable (linearGaussianPDF M) :=
  (measurable_standardGaussianPDF.comp (measurable_finiteMatrixAction M⁻¹)).const_mul _

theorem linearImageGaussian_eq_volume_withDensity (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    linearImageGaussian M = volume.withDensity (fun x => ENNReal.ofReal (linearGaussianPDF M x)) := by
  have hmap : (volume : Measure (I → ℝ)).map (matrixMeasurableEquiv M hM) =
      ENNReal.ofReal |M.det|⁻¹ • volume := by
    change (volume : Measure (I → ℝ)).map (Matrix.toLin' M) = _
    simpa only [abs_inv] using Real.map_matrix_volume_pi_eq_smul_volume_pi hM
  have h := map_realDensity_scaled_reference (volume : Measure (I → ℝ))
    (matrixMeasurableEquiv M hM) |M.det|⁻¹ (by positivity) hmap
    standardGaussianPDF measurable_standardGaussianPDF
  rw [← standardGaussian_eq_volume_withDensity] at h
  exact h

theorem linearGaussianPDF_pullback (M : Matrix I I ℝ) (hM : M.det ≠ 0) (x : I → ℝ) :
    linearGaussianPDF M (M.mulVec x) = |M.det|⁻¹ * standardGaussianPDF x := by
  unfold linearGaussianPDF
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]

theorem log_linearGaussianPDF_pullback (M : Matrix I I ℝ) (hM : M.det ≠ 0) (x : I → ℝ) :
    Real.log (linearGaussianPDF M (M.mulVec x)) = -Real.log |M.det| + Real.log (standardGaussianPDF x) := by
  rw [linearGaussianPDF_pullback M hM, Real.log_mul (inv_ne_zero (abs_ne_zero.mpr hM))
    (ne_of_gt (standardGaussianPDF_pos x)), Real.log_inv]

theorem integrable_log_linearGaussianPDF (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    Integrable (fun x => Real.log (linearGaussianPDF M x)) (linearImageGaussian M) := by
  change Integrable _ ((standardGaussian I).map (matrixMeasurableEquiv M hM))
  apply (integrable_map_equiv (matrixMeasurableEquiv M hM) _).mpr
  change Integrable (fun x => Real.log (linearGaussianPDF M (M.mulVec x))) (standardGaussian I)
  simp_rw [log_linearGaussianPDF_pullback M hM]
  exact (integrable_const _).add integrable_log_standardGaussianPDF

theorem linearGaussian_differentialEntropy (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    -(∫ x, Real.log (linearGaussianPDF M x) ∂linearImageGaussian M) =
      Real.log |M.det| + (Fintype.card I : ℝ) / 2 * (1 + Real.log (2 * Real.pi)) := by
  rw [linearImageGaussian, integral_map (measurable_finiteMatrixAction M).aemeasurable
    (integrable_log_linearGaussianPDF M hM).aestronglyMeasurable]
  change -(∫ x, Real.log (linearGaussianPDF M (M.mulVec x)) ∂standardGaussian I) = _
  simp_rw [log_linearGaussianPDF_pullback M hM]
  rw [integral_add (integrable_const _) integrable_log_standardGaussianPDF, integral_const]
  simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul]
  linarith [integral_neg_log_standardGaussianPDF (I := I)]

theorem linearGaussian_differentialEntropy_covariance (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    -(∫ x, Real.log (linearGaussianPDF M x) ∂linearImageGaussian M) =
      Real.log (M * M.transpose).det / 2 +
        (Fintype.card I : ℝ) / 2 * (1 + Real.log (2 * Real.pi)) := by
  rw [linearGaussian_differentialEntropy M hM, Matrix.det_mul, Matrix.det_transpose,
    Real.log_mul hM hM, Real.log_abs]
  ring

end GeneralizedBulk.Entropy
