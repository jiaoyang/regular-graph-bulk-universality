import GeneralizedBulk.Entropy.GaussianMixtureEntropy

/-! The literal probability measure, moments, and density of a finite Gaussian mixture. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite Mehler
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

def gaussianMixtureLaw (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ) : Measure (I → ℝ) :=
  ∑ s, ENNReal.ofReal (weight s) • affineGaussian (mean s) (M s)

theorem gaussianMixtureLaw_eq_withDensity (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hM : ∀ s, (M s).det ≠ 0) :
    gaussianMixtureLaw weight mean M = volume.withDensity (fun x => ENNReal.ofReal (gaussianMixturePDF weight mean M x)) := by
  have h := withDensity_finite_mixture (volume : Measure (I → ℝ)) weight
    (fun s => affineGaussianPDF (mean s) (M s)) hw
    (fun s => measurable_affineGaussianPDF _ _) (fun s x => (affineGaussianPDF_pos _ _ (hM s) x).le)
  change (∑ s, ENNReal.ofReal (weight s) • affineGaussian (mean s) (M s)) = _
  rw [show (fun x => ENNReal.ofReal (gaussianMixturePDF weight mean M x)) =
    (fun x => ENNReal.ofReal (∑ s, weight s * affineGaussianPDF (mean s) (M s) x)) from rfl, h]
  apply Finset.sum_congr rfl
  intro s hs
  rw [affineGaussian_eq_volume_withDensity _ _ (hM s)]

theorem gaussianMixtureLaw_probability (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) (hM : ∀ s, (M s).det ≠ 0) :
    IsProbabilityMeasure (gaussianMixtureLaw weight mean M) := by
  constructor
  rw [gaussianMixtureLaw_eq_withDensity weight mean M hw hM, withDensity_apply _ MeasurableSet.univ]
  simp only [Set.univ_inter, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianMixturePDF weight mean M hM)
    (ae_of_all _ (fun x => (gaussianMixturePDF_pos weight mean M hw hnorm hM x).le)),
    integral_gaussianMixturePDF weight mean M hnorm hM, ENNReal.ofReal_one]

theorem affineGaussian_integrable_coordinateL1 (mean : I → ℝ) (M : Matrix I I ℝ) :
    Integrable coordinateL1 (affineGaussian mean M) := by
  apply ((integrable_const (1 : ℝ)).add (affineGaussian_integrable_coordinateL1_sq mean M)).mono'
    continuous_coordinateL1.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (coordinateL1_nonneg x)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (coordinateL1 x - 1 / 2)]

theorem integrable_gaussianMixturePDF_mul_coordinateL1 (weight : S → ℝ) (mean : S → I → ℝ)
    (M : S → Matrix I I ℝ) (hM : ∀ s, (M s).det ≠ 0) :
    Integrable (fun x => gaussianMixturePDF weight mean M x * coordinateL1 x) volume := by
  have hi (s) : Integrable (fun x => affineGaussianPDF (mean s) (M s) x * coordinateL1 x) volume := by
    apply (integrable_realDensity_iff volume _ _ (measurable_affineGaussianPDF _ _)
      (fun x => (affineGaussianPDF_pos _ _ (hM s) x).le)).mp
    rw [← affineGaussian_eq_volume_withDensity _ _ (hM s)]
    exact affineGaussian_integrable_coordinateL1 _ _
  have he (x) : gaussianMixturePDF weight mean M x * coordinateL1 x =
      ∑ s, weight s * (affineGaussianPDF (mean s) (M s) x * coordinateL1 x) := by
    rw [gaussianMixturePDF, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  simp_rw [he]
  exact integrable_finset_sum _ (fun s _ => (hi s).const_mul _)

end GeneralizedBulk.Entropy
