import GeneralizedBulk.Entropy.GaussianMixtureJacobian

/-! Adding literal independent standard-normal coordinates contributes exactly
their Gaussian differential entropy to an arbitrary finite Gaussian mixture. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Matrix
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Analysis Hermite
variable {I J S : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype S]

theorem integrable_standardGaussianPDF : Integrable (standardGaussianPDF (I := I)) volume := by
  have he : affineGaussianPDF (0 : I → ℝ) 1 = standardGaussianPDF := by
    funext x
    rw [affineGaussianPDF_identity, sub_zero]
  rw [← he]
  exact integrable_affineGaussianPDF (0 : I → ℝ) 1 (by simp)

theorem integral_standardGaussianPDF : (∫ x : I → ℝ, standardGaussianPDF x) = 1 := by
  simpa only [affineGaussianPDF_identity, sub_zero] using
    integral_affineGaussianPDF (0 : I → ℝ) 1 (by simp)

theorem integrable_standardGaussianPDF_mul_log :
    Integrable (fun x : I → ℝ => standardGaussianPDF x * Real.log (standardGaussianPDF x)) volume := by
  apply (integrable_realDensity_iff volume _ _ measurable_standardGaussianPDF
    (fun x => (standardGaussianPDF_pos x).le)).mp
  rw [← standardGaussian_eq_volume_withDensity]
  exact integrable_log_standardGaussianPDF

theorem differentialEntropy_standardGaussianPDF :
    differentialEntropy (standardGaussianPDF (I := I)) =
      (Fintype.card I : ℝ) / 2 * (1 + Real.log (2 * Real.pi)) := by
  have hh := integral_neg_log_standardGaussianPDF (I := I)
  rw [standardGaussian_eq_volume_withDensity,
    integral_realDensity volume _ _ measurable_standardGaussianPDF (fun x => (standardGaussianPDF_pos x).le)] at hh
  exact hh

theorem gaussianMixturePDF_sum_normal (weight : S → ℝ) (mean : S → I → ℝ) :
    gaussianMixturePDF weight (fun s => Sum.elim (mean s) (fun _ : J => 0))
      (fun _ => (1 : Matrix (I ⊕ J) (I ⊕ J) ℝ)) =
      sumProductDensity (gaussianMixturePDF weight mean (fun _ => (1 : Matrix I I ℝ)))
        (standardGaussianPDF (I := J)) := by
  funext x
  simp [gaussianMixturePDF, affineGaussianPDF_identity, standardGaussianPDF, sumProductDensity,
    Fintype.prod_sum_type, Finset.sum_mul, mul_assoc]

theorem gaussianMixture_entropy_sum_normal (weight : S → ℝ) (mean : S → I → ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) :
    differentialEntropy (gaussianMixturePDF weight (fun s => Sum.elim (mean s) (fun _ : J => 0))
      (fun _ => (1 : Matrix (I ⊕ J) (I ⊕ J) ℝ))) =
      differentialEntropy (gaussianMixturePDF weight mean (fun _ => (1 : Matrix I I ℝ))) +
        (Fintype.card J : ℝ) / 2 * (1 + Real.log (2 * Real.pi)) := by
  rw [gaussianMixturePDF_sum_normal]
  rw [(sumProductDensity_entropy _ _
    (integrable_gaussianMixturePDF _ _ _ (fun _ => by simp)) integrable_standardGaussianPDF
    (gaussianMixturePDF_pos _ _ _ hw hnorm (fun _ => by simp)) standardGaussianPDF_pos
    (integrable_gaussianMixturePDF_mul_log _ _ _ hw hnorm (fun _ => by simp))
    integrable_standardGaussianPDF_mul_log
    (integral_gaussianMixturePDF _ _ _ hnorm (fun _ => by simp)) integral_standardGaussianPDF).2,
    differentialEntropy_standardGaussianPDF]

end GeneralizedBulk.Entropy
