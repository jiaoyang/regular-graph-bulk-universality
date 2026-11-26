import GeneralizedBulk.Entropy.GaussianShiftEntropy
import GeneralizedBulk.Entropy.LogSum

/-! The relative entropy of an actual Gaussian and its translate. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem integrable_affineGaussianPDF (mean : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    Integrable (affineGaussianPDF mean M) volume := by
  have h := (integrable_realDensity_iff volume (affineGaussianPDF mean M) (fun _ => 1)
    (measurable_affineGaussianPDF mean M) (fun x => (affineGaussianPDF_pos mean M hM x).le))
  rw [← affineGaussian_eq_volume_withDensity mean M hM] at h
  simpa only [mul_one] using h.mp (integrable_const 1)

theorem integral_affineGaussianPDF (mean : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    (∫ x, affineGaussianPDF mean M x) = 1 := by
  have h := integral_realDensity volume (affineGaussianPDF mean M) (fun _ => 1)
    (measurable_affineGaussianPDF mean M) (fun x => (affineGaussianPDF_pos mean M hM x).le)
  rw [← affineGaussian_eq_volume_withDensity mean M hM] at h
  simpa only [mul_one, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using h.symm

theorem log_affineGaussianPDF (mean : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) (x : I → ℝ) :
    Real.log (affineGaussianPDF mean M x) = -Real.log |M.det| -
      (Fintype.card I : ℝ) / 2 * Real.log (2 * Real.pi) -
        (∑ i, (M⁻¹.mulVec (x - mean) i) ^ 2) / 2 := by
  unfold affineGaussianPDF linearGaussianPDF
  rw [Real.log_mul (inv_ne_zero (abs_ne_zero.mpr hM)) (ne_of_gt (standardGaussianPDF_pos _)),
    Real.log_inv, log_standardGaussianPDF]
  ring

theorem gaussian_log_ratio_pullback (mean target : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) (z : I → ℝ) :
    Real.log (affineGaussianPDF mean M (mean + M.mulVec z) /
      affineGaussianPDF target M (mean + M.mulVec z)) =
        (∑ i, (M⁻¹.mulVec (mean - target) i) ^ 2) / 2 +
          ∑ i, M⁻¹.mulVec (mean - target) i * z i := by
  have harg : M⁻¹.mulVec (mean + M.mulVec z - target) = M⁻¹.mulVec (mean - target) + z := by
    rw [show mean + M.mulVec z - target = (mean - target) + M.mulVec z by abel,
      Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mulVec]
  rw [Real.log_div (ne_of_gt (affineGaussianPDF_pos mean M hM _))
    (ne_of_gt (affineGaussianPDF_pos target M hM _)),
    log_affineGaussianPDF_pullback mean M hM, log_standardGaussianPDF,
    log_affineGaussianPDF target M hM, harg]
  simp only [Pi.add_apply]
  have he : (∑ i, (M⁻¹.mulVec (mean - target) i + z i) ^ 2) =
      (∑ i, (M⁻¹.mulVec (mean - target) i) ^ 2) +
      2 * (∑ i, M⁻¹.mulVec (mean - target) i * z i) + (∑ i, z i ^ 2) := by
    simp only [add_sq, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
  rw [he]
  ring

theorem integrable_gaussian_log_ratio (mean target : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    Integrable (fun x => Real.log (affineGaussianPDF mean M x / affineGaussianPDF target M x))
      (affineGaussian mean M) := by
  rw [affineGaussian_map_standardGaussian]
  apply (integrable_map_measure
    (((measurable_affineGaussianPDF mean M).div (measurable_affineGaussianPDF target M)).log.aestronglyMeasurable)
    (by fun_prop : Measurable (fun x : I → ℝ => mean + M.mulVec x)).aemeasurable).mpr
  change Integrable (fun z => Real.log (affineGaussianPDF mean M (mean + M.mulVec z) /
    affineGaussianPDF target M (mean + M.mulVec z))) (standardGaussian I)
  simp_rw [gaussian_log_ratio_pullback mean target M hM]
  exact (integrable_const _).add (integrable_finset_sum _
    (fun i _ => by simpa only [pow_one] using
      (standardGaussian_integrable_coordinate_pow i 1).const_mul (M⁻¹.mulVec (mean - target) i)))

theorem gaussian_relativeEntropy_translation (mean target : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    (∫ x, Real.log (affineGaussianPDF mean M x / affineGaussianPDF target M x)
      ∂affineGaussian mean M) = (∑ i, (M⁻¹.mulVec (mean - target) i) ^ 2) / 2 := by
  rw [affineGaussian_map_standardGaussian,
    integral_map (by fun_prop : Measurable (fun x : I → ℝ => mean + M.mulVec x)).aemeasurable
      (((measurable_affineGaussianPDF mean M).div (measurable_affineGaussianPDF target M)).log.aestronglyMeasurable)]
  simp_rw [gaussian_log_ratio_pullback mean target M hM]
  rw [integral_add (integrable_const _) (integrable_finset_sum _
    (fun i _ => by simpa only [pow_one] using
      (standardGaussian_integrable_coordinate_pow i 1).const_mul (M⁻¹.mulVec (mean - target) i))),
    integral_const, integral_finset_sum _ (fun i _ => by simpa only [pow_one] using
      (standardGaussian_integrable_coordinate_pow i 1).const_mul (M⁻¹.mulVec (mean - target) i))]
  have hz (i : I) : (∫ z : I → ℝ, z i ∂standardGaussian I) = 0 := by
    have h := integral_iid_eval standardNormal I i id measurable_id.aestronglyMeasurable
    simpa only [id_eq, iidLaw, Measure.infinitePi_eq_pi, standardGaussian, standardNormal_moment_one] using h
  simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul, integral_const_mul, hz,
    mul_zero, Finset.sum_const_zero, add_zero]

theorem gaussian_klIntegrand_translation (mean target : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    Integrable (fun x => klIntegrand (affineGaussianPDF mean M x) (affineGaussianPDF target M x)) volume ∧
      (∫ x, klIntegrand (affineGaussianPDF mean M x) (affineGaussianPDF target M x)) =
        (∑ i, (M⁻¹.mulVec (mean - target) i) ^ 2) / 2 := by
  have hlog := integrable_gaussian_log_ratio mean target M hM
  rw [affineGaussian_eq_volume_withDensity mean M hM] at hlog
  have hprod := (integrable_realDensity_iff volume _ _ (measurable_affineGaussianPDF mean M)
    (fun x => (affineGaussianPDF_pos mean M hM x).le)).mp hlog
  have hi := (hprod.sub (integrable_affineGaussianPDF mean M hM)).add (integrable_affineGaussianPDF target M hM)
  refine ⟨hi, ?_⟩
  change (∫ x, (affineGaussianPDF mean M x * Real.log
    (affineGaussianPDF mean M x / affineGaussianPDF target M x) - affineGaussianPDF mean M x) +
      affineGaussianPDF target M x) = _
  have h := integral_realDensity volume (affineGaussianPDF mean M)
    (fun x => Real.log (affineGaussianPDF mean M x / affineGaussianPDF target M x))
    (measurable_affineGaussianPDF mean M) (fun x => (affineGaussianPDF_pos mean M hM x).le)
  rw [← affineGaussian_eq_volume_withDensity mean M hM, gaussian_relativeEntropy_translation mean target M hM] at h
  calc
    _ = (∫ x, affineGaussianPDF mean M x * Real.log
        (affineGaussianPDF mean M x / affineGaussianPDF target M x) - affineGaussianPDF mean M x) +
          ∫ x, affineGaussianPDF target M x :=
      integral_add (hprod.sub (integrable_affineGaussianPDF mean M hM)) (integrable_affineGaussianPDF target M hM)
    _ = ((∫ x, affineGaussianPDF mean M x * Real.log
        (affineGaussianPDF mean M x / affineGaussianPDF target M x)) - ∫ x, affineGaussianPDF mean M x) +
          ∫ x, affineGaussianPDF target M x := by
      rw [integral_sub hprod (integrable_affineGaussianPDF mean M hM)]
    _ = _ := by rw [← h, integral_affineGaussianPDF mean M hM, integral_affineGaussianPDF target M hM]; ring

end GeneralizedBulk.Entropy
