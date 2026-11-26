import GeneralizedBulk.Entropy.GaussianLogBounds
import GeneralizedBulk.Analysis.DensityMixture

/-! Finiteness and actual integral formulas for finite Gaussian-mixture entropy. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite Mehler
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

def gaussianLogEnvelope (mean : I → ℝ) (M : Matrix I I ℝ) : ℝ :=
  |Real.log (|M.det|)| + (Fintype.card I : ℝ) / 2 * |Real.log (2 * Real.pi)| +
    matrixEntryL1 M⁻¹ ^ 2 * (1 + coordinateL1 mean ^ 2)

theorem gaussianLogEnvelope_nonneg (mean : I → ℝ) (M : Matrix I I ℝ) :
    0 ≤ gaussianLogEnvelope mean M := by unfold gaussianLogEnvelope; positivity

theorem abs_log_affineGaussianPDF_quadratic (mean : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) (x : I → ℝ) :
    |Real.log (affineGaussianPDF mean M x)| ≤ gaussianLogEnvelope mean M * (1 + coordinateL1 x ^ 2) := by
  refine (abs_log_affineGaussianPDF_le mean M hM x).trans ?_
  unfold gaussianLogEnvelope
  have h0 : 0 ≤ |Real.log (|M.det|)| := abs_nonneg _
  have h1 : 0 ≤ (Fintype.card I : ℝ) / 2 * |Real.log (2 * Real.pi)| := by positivity
  nlinarith [mul_nonneg (sq_nonneg (matrixEntryL1 M⁻¹))
    (mul_nonneg (sq_nonneg (coordinateL1 mean)) (sq_nonneg (coordinateL1 x))),
    mul_nonneg h0 (sq_nonneg (coordinateL1 x)), mul_nonneg h1 (sq_nonneg (coordinateL1 x))]

theorem abs_log_gaussianMixturePDF_quadratic (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) (hM : ∀ s, (M s).det ≠ 0) (x : I → ℝ) :
    |Real.log (gaussianMixturePDF weight mean M x)| ≤
      (∑ s, gaussianLogEnvelope (mean s) (M s)) * (1 + coordinateL1 x ^ 2) := by
  apply abs_log_weighted_sum_le weight _ hw hnorm (fun s => affineGaussianPDF_pos _ _ (hM s) x)
  intro s
  refine (abs_log_affineGaussianPDF_quadratic _ _ (hM s) x).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Finset.single_le_sum (fun t _ => gaussianLogEnvelope_nonneg (mean t) (M t)) (Finset.mem_univ s)

theorem affineGaussian_integrable_coordinateL1_sq (mean : I → ℝ) (M : Matrix I I ℝ) :
    Integrable (fun x => coordinateL1 x ^ 2) (affineGaussian mean M) := by
  rw [affineGaussian_map_standardGaussian]
  exact (integrable_map_measure (continuous_coordinateL1.pow 2).aestronglyMeasurable
    (by fun_prop : Measurable (fun z : I → ℝ => mean + M.mulVec z)).aemeasurable).mpr
      (standardGaussian_integrable_affine_coordinateL1_sq mean M)

theorem integrable_log_gaussianMixturePDF_under_affineGaussian
    (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) (hM : ∀ s, (M s).det ≠ 0)
    (mean' : I → ℝ) (M' : Matrix I I ℝ) :
    Integrable (fun x => Real.log (gaussianMixturePDF weight mean M x)) (affineGaussian mean' M') := by
  apply (((integrable_const (1 : ℝ)).add (affineGaussian_integrable_coordinateL1_sq mean' M')).const_mul
    (∑ s, gaussianLogEnvelope (mean s) (M s))).mono'
    (measurable_gaussianMixturePDF weight mean M).log.aestronglyMeasurable
  filter_upwards [] with x
  exact abs_log_gaussianMixturePDF_quadratic weight mean M hw hnorm hM x

theorem integrable_gaussianMixturePDF_mul_log (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) (hM : ∀ s, (M s).det ≠ 0) :
    Integrable (fun x => gaussianMixturePDF weight mean M x * Real.log (gaussianMixturePDF weight mean M x)) volume := by
  have hi (s : S) : Integrable (fun x => affineGaussianPDF (mean s) (M s) x *
      Real.log (gaussianMixturePDF weight mean M x)) volume := by
    apply (integrable_realDensity_iff volume _ _ (measurable_affineGaussianPDF _ _)
      (fun x => (affineGaussianPDF_pos _ _ (hM s) x).le)).mp
    rw [← affineGaussian_eq_volume_withDensity _ _ (hM s)]
    exact integrable_log_gaussianMixturePDF_under_affineGaussian weight mean M hw hnorm hM _ _
  have he (x) : gaussianMixturePDF weight mean M x * Real.log (gaussianMixturePDF weight mean M x) =
      ∑ s, weight s * (affineGaussianPDF (mean s) (M s) x * Real.log (gaussianMixturePDF weight mean M x)) := by
    rw [gaussianMixturePDF, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  simp_rw [he]
  exact integrable_finset_sum _ (fun s _ => (hi s).const_mul _)

def differentialEntropy (f : (I → ℝ) → ℝ) : ℝ := -(∫ x, f x * Real.log (f x))

theorem differentialEntropy_gaussianMixture_as_expectations
    (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) (hM : ∀ s, (M s).det ≠ 0) :
    differentialEntropy (gaussianMixturePDF weight mean M) =
      -∑ s, weight s * ∫ x, Real.log (gaussianMixturePDF weight mean M x) ∂affineGaussian (mean s) (M s) := by
  have hi (s : S) := integrable_log_gaussianMixturePDF_under_affineGaussian weight mean M hw hnorm hM (mean s) (M s)
  have hp (s : S) : Integrable (fun x => affineGaussianPDF (mean s) (M s) x *
      Real.log (gaussianMixturePDF weight mean M x)) volume := by
    apply (integrable_realDensity_iff volume _ _ (measurable_affineGaussianPDF _ _)
      (fun x => (affineGaussianPDF_pos _ _ (hM s) x).le)).mp
    rw [← affineGaussian_eq_volume_withDensity _ _ (hM s)]
    exact hi s
  unfold differentialEntropy
  have he (x) : gaussianMixturePDF weight mean M x * Real.log (gaussianMixturePDF weight mean M x) =
      ∑ s, weight s * (affineGaussianPDF (mean s) (M s) x * Real.log (gaussianMixturePDF weight mean M x)) := by
    rw [gaussianMixturePDF, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  simp_rw [he]
  rw [integral_finset_sum _ (fun s _ => (hp s).const_mul _)]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [integral_const_mul, affineGaussian_eq_volume_withDensity _ _ (hM s),
    integral_realDensity volume _ _ (measurable_affineGaussianPDF _ _)
      (fun x => (affineGaussianPDF_pos _ _ (hM s) x).le)]

end GeneralizedBulk.Entropy
