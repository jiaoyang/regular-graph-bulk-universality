import GeneralizedBulk.Entropy.GaussianAffineEntropy
import GeneralizedBulk.Analysis.RealDensityIntegration

/-! Translation of the actual nonsingular multivariate Gaussian density. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite
variable {I : Type*} [Fintype I] [DecidableEq I]

def affineGaussian (mean : I → ℝ) (M : Matrix I I ℝ) : Measure (I → ℝ) :=
  (linearImageGaussian M).map (fun x => mean + x)

instance (mean : I → ℝ) (M : Matrix I I ℝ) : IsProbabilityMeasure (affineGaussian mean M) :=
  isProbabilityMeasure_map (by fun_prop : Measurable (fun x : I → ℝ => mean + x)).aemeasurable

def affineGaussianPDF (mean : I → ℝ) (M : Matrix I I ℝ) (x : I → ℝ) : ℝ :=
  linearGaussianPDF M (x - mean)

theorem affineGaussianPDF_pos (mean : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) (x : I → ℝ) :
    0 < affineGaussianPDF mean M x := linearGaussianPDF_pos M hM _

theorem measurable_affineGaussianPDF (mean : I → ℝ) (M : Matrix I I ℝ) :
    Measurable (affineGaussianPDF mean M) :=
  (measurable_linearGaussianPDF M).comp (measurable_id.sub measurable_const)

theorem affineGaussian_eq_volume_withDensity (mean : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    affineGaussian mean M = volume.withDensity (fun x => ENNReal.ofReal (affineGaussianPDF mean M x)) := by
  rw [affineGaussian, linearImageGaussian_eq_volume_withDensity M hM]
  change (volume.withDensity (fun x => ENNReal.ofReal (linearGaussianPDF M x))).map
    (MeasurableEquiv.addLeft mean) = _
  rw [map_withDensity_equiv _ _ _ (measurable_linearGaussianPDF M).ennreal_ofReal]
  have hm : (volume : Measure (I → ℝ)).map (MeasurableEquiv.addLeft mean) = volume :=
    (measurePreserving_add_left volume mean).map_eq
  rw [hm]
  congr 1
  funext x
  change ENNReal.ofReal (linearGaussianPDF M (-mean + x)) = _
  congr 2
  abel

theorem affineGaussian_map_standardGaussian (mean : I → ℝ) (M : Matrix I I ℝ) :
    affineGaussian mean M = (standardGaussian I).map (fun x => mean + M.mulVec x) := by
  rw [affineGaussian, linearImageGaussian,
    Measure.map_map (by fun_prop) (measurable_finiteMatrixAction M)]
  rfl

theorem affineGaussianPDF_pullback (mean : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) (x : I → ℝ) :
    affineGaussianPDF mean M (mean + M.mulVec x) = |M.det|⁻¹ * standardGaussianPDF x := by
  unfold affineGaussianPDF
  rw [add_sub_cancel_left, linearGaussianPDF_pullback M hM]

theorem log_affineGaussianPDF_pullback (mean : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) (x : I → ℝ) :
    Real.log (affineGaussianPDF mean M (mean + M.mulVec x)) =
      -Real.log |M.det| + Real.log (standardGaussianPDF x) := by
  rw [affineGaussianPDF_pullback mean M hM, Real.log_mul (inv_ne_zero (abs_ne_zero.mpr hM))
    (ne_of_gt (standardGaussianPDF_pos x)), Real.log_inv]

theorem integrable_log_affineGaussianPDF (mean : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    Integrable (fun x => Real.log (affineGaussianPDF mean M x)) (affineGaussian mean M) := by
  rw [affineGaussian]
  change Integrable _ ((linearImageGaussian M).map (MeasurableEquiv.addLeft mean))
  apply (integrable_map_equiv (MeasurableEquiv.addLeft mean) _).mpr
  change Integrable (fun x => Real.log (affineGaussianPDF mean M ((MeasurableEquiv.addLeft mean) x)))
    (linearImageGaussian M)
  have he : (fun x => Real.log (affineGaussianPDF mean M ((MeasurableEquiv.addLeft mean) x))) =
      (fun x => Real.log (linearGaussianPDF M x)) := by
    funext x
    change Real.log (linearGaussianPDF M (mean + x - mean)) = _
    rw [add_sub_cancel_left]
  rw [he]
  exact integrable_log_linearGaussianPDF M hM

theorem affineGaussian_differentialEntropy (mean : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    -(∫ x, Real.log (affineGaussianPDF mean M x) ∂affineGaussian mean M) =
      Real.log (M * M.transpose).det / 2 +
        (Fintype.card I : ℝ) / 2 * (1 + Real.log (2 * Real.pi)) := by
  rw [affineGaussian, integral_map (by fun_prop : Measurable (fun x : I → ℝ => mean + x)).aemeasurable
    (integrable_log_affineGaussianPDF mean M hM).aestronglyMeasurable]
  simp only [affineGaussianPDF, add_sub_cancel_left]
  exact linearGaussian_differentialEntropy_covariance M hM

end GeneralizedBulk.Entropy
