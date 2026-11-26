import GeneralizedBulk.Analysis.DensityTransport
import GeneralizedBulk.Analysis.PiDensity
import GeneralizedBulk.Entropy.HermiteMultivariate
import GeneralizedBulk.Gaussian.IID

/-! Lebesgue densities and differential entropy of actual finite Gaussian laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite
variable {I : Type*} [Fintype I]

def standardGaussianPDF (x : I → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

theorem standardGaussianPDF_pos (x : I → ℝ) : 0 < standardGaussianPDF x := by
  exact Finset.prod_pos (fun i _ => gaussianPDFReal_pos 0 1 (x i) one_ne_zero)

theorem measurable_standardGaussianPDF : Measurable (standardGaussianPDF (I := I)) := by
  exact Finset.measurable_prod _ (fun i _ => (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i))

theorem standardGaussian_eq_volume_withDensity : standardGaussian I =
    volume.withDensity (fun x => ENNReal.ofReal (standardGaussianPDF x)) := by
  unfold standardGaussian standardNormal
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  change Measure.pi (fun _ : I => volume.withDensity (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x))) = _
  rw [pi_withDensity_ofReal (fun _ : I => volume) (fun _ => gaussianPDFReal 0 1)
    (fun _ => integrable_gaussianPDFReal 0 1) (fun _ => gaussianPDFReal_nonneg 0 1)]
  simp only [volume_pi, standardGaussianPDF]

theorem log_standardNormalPDF (x : ℝ) :
    Real.log (gaussianPDFReal 0 1 x) = -(Real.log (2 * Real.pi)) / 2 - x ^ 2 / 2 := by
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [Real.log_mul (inv_ne_zero hs) (Real.exp_ne_zero _), Real.log_inv,
    Real.log_sqrt (by positivity : 0 ≤ 2 * Real.pi), Real.log_exp]
  ring

theorem log_standardGaussianPDF (x : I → ℝ) :
    Real.log (standardGaussianPDF x) =
      -(Fintype.card I : ℝ) / 2 * Real.log (2 * Real.pi) - (∑ i, x i ^ 2) / 2 := by
  rw [standardGaussianPDF, Real.log_prod _ _ (fun i _ => ne_of_gt (gaussianPDFReal_pos 0 1 (x i) one_ne_zero))]
  simp_rw [log_standardNormalPDF]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_div]
  ring

theorem standardGaussian_eval_measurePreserving (i : I) :
    MeasurePreserving (fun x : I → ℝ => x i) (standardGaussian I) standardNormal := by
  have h := iidLaw_eval_measurePreserving standardNormal I i
  simpa only [iidLaw, Measure.infinitePi_eq_pi, standardGaussian] using h

theorem standardGaussian_integrable_coordinate_pow (i : I) (n : ℕ) :
    Integrable (fun x : I → ℝ => x i ^ n) (standardGaussian I) :=
  ((standardGaussian_eval_measurePreserving i).integrable_comp
    (standardNormal_integrable_pow n).aestronglyMeasurable).mpr (standardNormal_integrable_pow n)

theorem standardGaussian_coordinate_sq (i : I) :
    (∫ x : I → ℝ, x i ^ 2 ∂standardGaussian I) = 1 := by
  have h := integral_iid_eval standardNormal I i (fun t => t ^ 2)
    (by fun_prop : AEStronglyMeasurable (fun t : ℝ => t ^ 2) standardNormal)
  simpa only [iidLaw, Measure.infinitePi_eq_pi, standardGaussian, standardNormal_moment_two] using h

theorem integrable_log_standardGaussianPDF :
    Integrable (fun x => Real.log (standardGaussianPDF x)) (standardGaussian I) := by
  simp_rw [log_standardGaussianPDF]
  exact (integrable_const _).sub
    ((integrable_finset_sum _ (fun i _ => standardGaussian_integrable_coordinate_pow i 2)).div_const 2)

theorem integral_neg_log_standardGaussianPDF :
    -(∫ x, Real.log (standardGaussianPDF x) ∂standardGaussian I) =
      (Fintype.card I : ℝ) / 2 * (1 + Real.log (2 * Real.pi)) := by
  simp_rw [log_standardGaussianPDF]
  rw [integral_sub (integrable_const _) ((integrable_finset_sum _
    (fun i _ => standardGaussian_integrable_coordinate_pow i 2)).div_const 2), integral_const,
    integral_div, integral_finset_sum _ (fun i _ => standardGaussian_integrable_coordinate_pow i 2)]
  simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul, standardGaussian_coordinate_sq,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

end GeneralizedBulk.Entropy
