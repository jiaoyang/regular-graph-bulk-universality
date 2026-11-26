import GeneralizedBulk.Entropy.MehlerLebesgueDensity

/-! Exact conversion between the constructed Mehler relative entropy and the
differential entropy of the actual smoothed finite signal. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

theorem smoothingFactor_coordinateVariance (a : ℝ) (ha : 0 < 1-a^2) (i : I) :
    (coordinateVariance (smoothingFactor I a) i : ℝ) = 1-a^2 := by
  simp [coordinateVariance,smoothingFactor,Matrix.diagonal_apply,Real.sq_sqrt ha.le]

namespace NormalizedFiniteSignal
variable (D : NormalizedFiniteSignal I S)

theorem smoothingLaw_probability (a : ℝ) (ha : 0 < 1-a^2) :
    IsProbabilityMeasure (D.smoothingLaw a) :=
  gaussianMixtureLaw_probability _ _ _ D.nonneg D.total (fun _ => smoothingFactor_det_ne_zero a ha)

theorem smoothingLaw_coordinate_sq_integrable (a : ℝ) (i : I) :
    Integrable (fun x : I → ℝ => x i^2) (D.smoothingLaw a) := by
  exact integrable_gaussianMixtureLaw_of_components _ _ _ _ (fun s =>
    gaussianLaw_integrable_pow _ _ _ _ (affineGaussian_coordinate_law _ _ i) 2)

theorem smoothingLaw_coordinate_sq (a : ℝ) (ha : 0 < 1-a^2) (i : I) :
    (∫ x : I → ℝ,x i^2 ∂D.smoothingLaw a) = 1 := by
  change (∫ x : I → ℝ,x i^2 ∂gaussianMixtureLaw _ _ _) = _
  rw [integral_gaussianMixtureLaw _ _ _ D.nonneg _ (fun s =>
    gaussianLaw_integrable_pow _ _ _ _ (affineGaussian_coordinate_law _ _ i) 2)]
  simp_rw [gaussianLaw_second_moment _ _ _ _ (affineGaussian_coordinate_law _ _ i),
    smoothingFactor_coordinateVariance a ha]
  have hc : (∑ s,D.weight s*D.signal s i^2) = 1 := by
    simpa only [pow_two,mul_assoc,ite_true] using D.covariance i i
  calc
    _ = a^2*(∑ s,D.weight s*D.signal s i^2)+(1-a^2)*(∑ s,D.weight s) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = 1 := by rw [hc,D.total]; ring

theorem smoothingLaw_log_standard_integrable (a : ℝ) (ha : 0 < 1-a^2) :
    Integrable (fun x : I → ℝ => Real.log (standardGaussianPDF x)) (D.smoothingLaw a) := by
  letI := D.smoothingLaw_probability a ha
  simp_rw [log_standardGaussianPDF]
  exact (integrable_const _).sub ((integrable_finset_sum _
    (fun i _ => D.smoothingLaw_coordinate_sq_integrable a i)).div_const 2)

theorem smoothingLaw_log_standard (a : ℝ) (ha : 0 < 1-a^2) :
    (∫ x : I → ℝ,Real.log (standardGaussianPDF x) ∂D.smoothingLaw a) =
      -(Fintype.card I : ℝ)/2*(1+Real.log (2*Real.pi)) := by
  letI := D.smoothingLaw_probability a ha
  simp_rw [log_standardGaussianPDF]
  rw [integral_sub (integrable_const _) ((integrable_finset_sum _
    (fun i _ => D.smoothingLaw_coordinate_sq_integrable a i)).div_const 2),integral_const,
    integral_div,integral_finset_sum _ (fun i _ => D.smoothingLaw_coordinate_sq_integrable a i)]
  simp only [measureReal_univ_eq_one,smul_eq_mul,one_mul,D.smoothingLaw_coordinate_sq a ha,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  ring

theorem lebesgueDensity_mul_log_integrable (a : ℝ) (ha : 0 < 1-a^2) :
    Integrable (fun x => D.lebesgueDensity a x*Real.log (D.lebesgueDensity a x)) volume :=
  integrable_gaussianMixturePDF_mul_log _ _ _ D.nonneg D.total (fun _ => smoothingFactor_det_ne_zero a ha)

theorem lebesgueDensity_mul_log_standard_integrable (a : ℝ) (ha : 0 < 1-a^2) :
    Integrable (fun x => D.lebesgueDensity a x*Real.log (standardGaussianPDF x)) volume := by
  apply (integrable_realDensity_iff volume _ _ (D.measurable_lebesgueDensity a)
    (fun x => (D.lebesgueDensity_pos a ha x).le)).mp
  rw [← D.smoothingLaw_lebesgue a ha]
  exact D.smoothingLaw_log_standard_integrable a ha

theorem relative_integrand_lebesgue_ae (a : ℝ) (ha : 0 < 1-a^2) :
    (fun x => standardGaussianPDF x*(D.density a x*Real.log (D.density a x))) =ᵐ[volume]
      (fun x => D.lebesgueDensity a x*Real.log (D.lebesgueDensity a x)-
        D.lebesgueDensity a x*Real.log (standardGaussianPDF x)) := by
  filter_upwards [D.lebesgueDensity_eq_relative_ae a ha] with x hx
  have hp : 0 < D.density a x := (mul_pos_iff_of_pos_left (standardGaussianPDF_pos x)).mp
    (hx ▸ D.lebesgueDensity_pos a ha x)
  rw [hx,Real.log_mul (standardGaussianPDF_pos x).ne' hp.ne']
  ring

theorem density_mul_log_integrable (a : ℝ) (ha : 0 < 1-a^2) :
    Integrable (fun x => D.density a x*Real.log (D.density a x)) (standardGaussian I) := by
  rw [standardGaussian_eq_volume_withDensity]
  apply (integrable_realDensity_iff volume _ _ measurable_standardGaussianPDF
    (fun x => (standardGaussianPDF_pos x).le)).mpr
  exact ((D.lebesgueDensity_mul_log_integrable a ha).sub
    (D.lebesgueDensity_mul_log_standard_integrable a ha)).congr
      (D.relative_integrand_lebesgue_ae a ha).symm

theorem relativeEntropy_eq_standard_sub_differential (a : ℝ) (ha : 0 < 1-a^2) :
    relativeEntropy (standardGaussian I) (D.density a) =
      (Fintype.card I : ℝ)/2*(1+Real.log (2*Real.pi))-
        differentialEntropy (D.lebesgueDensity a) := by
  unfold relativeEntropy
  rw [standardGaussian_eq_volume_withDensity,integral_realDensity volume _ _
    measurable_standardGaussianPDF (fun x => (standardGaussianPDF_pos x).le),
    integral_congr_ae (D.relative_integrand_lebesgue_ae a ha),
    integral_sub (D.lebesgueDensity_mul_log_integrable a ha)
      (D.lebesgueDensity_mul_log_standard_integrable a ha)]
  have h := D.smoothingLaw_log_standard a ha
  rw [D.smoothingLaw_lebesgue a ha,integral_realDensity volume _ _
    (D.measurable_lebesgueDensity a) (fun x => (D.lebesgueDensity_pos a ha x).le)] at h
  rw [h]
  unfold differentialEntropy
  ring

end NormalizedFiniteSignal
end GeneralizedBulk.Entropy.Mehler
