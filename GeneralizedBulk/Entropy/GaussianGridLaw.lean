import GeneralizedBulk.Entropy.GaussianGridEntropy
import GeneralizedBulk.Entropy.CountableLaw

/-! Actual quantizer law masses equal the proved Lebesgue cell masses. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

theorem lawMass_withDensity_gridLabel (a : ℝ) (ha : 0 < a) (f : (I → ℝ) → ℝ)
    (hf : Integrable f) (hp : ∀ x, 0 ≤ f x) (j : I → ℤ) :
    lawMass (volume.withDensity (fun x => ENNReal.ofReal (f x))) (gridLabel a) j = gridMass a f j := by
  rw [lawMass, measureReal_def, ← gridCell_eq_fiber a ha j,
    withDensity_apply _ (measurableSet_gridCell a j)]
  rw [← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_of_all _ hp)]
  exact ENNReal.toReal_ofReal (integral_nonneg hp)

theorem lawMass_gaussianMixture_gridLabel (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) (hM : ∀ s, (M s).det ≠ 0)
    (a : ℝ) (ha : 0 < a) :
    lawMass (gaussianMixtureLaw weight mean M) (gridLabel a) = gridMass a (gaussianMixturePDF weight mean M) := by
  funext j
  rw [gaussianMixtureLaw_eq_withDensity weight mean M hw hM]
  exact lawMass_withDensity_gridLabel a ha _ (integrable_gaussianMixturePDF weight mean M hM)
    (fun x => (gaussianMixturePDF_pos weight mean M hw hnorm hM x).le) j

theorem lawMass_affineGaussian_gridLabel (mean : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0)
    (a : ℝ) (ha : 0 < a) :
    lawMass (affineGaussian mean M) (gridLabel a) = gridMass a (affineGaussianPDF mean M) := by
  funext j
  rw [affineGaussian_eq_volume_withDensity mean M hM]
  exact lawMass_withDensity_gridLabel a ha _ (integrable_affineGaussianPDF mean M hM)
    (fun x => (affineGaussianPDF_pos mean M hM x).le) j

theorem lawMass_shifted_linearGaussian_gridLabel (mean : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0)
    (a : ℝ) (ha : 0 < a) :
    lawMass (linearImageGaussian M) (fun x => gridLabel a (mean+x)) = gridMass a (affineGaussianPDF mean M) := by
  rw [← lawMass_affineGaussian_gridLabel mean M hM a ha]
  funext j
  rw [lawMass, lawMass, affineGaussian, measureReal_def, measureReal_def,
    Measure.map_apply (by fun_prop : Measurable (fun x : I → ℝ => mean+x))
      ((measurable_gridLabel a) (measurableSet_singleton j))]
  rfl

end GeneralizedBulk.Entropy
