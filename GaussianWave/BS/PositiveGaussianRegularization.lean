import GaussianWave.BS.GaussianSmoothingEntropy
import GaussianWave.BS.GaussianInnovationDensities
import GaussianWave.BS.IndependentAddition

/-! Actual positive finite-entropy densities after nondegenerate Gaussian
regularization. The original probability law needs only a finite second
moment; its density and entropy are not assumed to exist. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

theorem gaussianFactorRegularizationEntropyDensity_positive
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ)
    (A : Matrix I I ℝ) (hA : A.det ≠ 0) {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    0 < (gaussianFactorRegularizationEntropyDensity μ hμ A hA ht).density x := by
  change 0 < |A.det|⁻¹ * heatDensity (Measure.map A⁻¹.mulVec μ) t (A⁻¹.mulVec x)
  letI : IsProbabilityMeasure (Measure.map A⁻¹.mulVec μ) :=
    isProbabilityMeasure_map (measurable_finiteMatrixAction A⁻¹).aemeasurable
  exact mul_pos (inv_pos.mpr (abs_pos.mpr hA)) (heatDensity_pos _ ht _)

/-- The actual convolution with any surjective rectangular Gaussian factor
has a positive density with absolutely integrable density times log density. -/
def gaussianLinearRegularizationPositiveDensity
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ)
    (L : Matrix I J ℝ) (hL : Function.Surjective L.mulVec) :
    PositiveEntropyDensity (volume : Measure (I → ℝ)) :=
  (gaussianFactorRegularizationEntropyDensity μ hμ
    (rowGram_posDef_of_surjective L hL).posSemidef.sqrt
    (posDef_sqrt_det_ne_zero _ (rowGram_posDef_of_surjective L hL))
    (by norm_num : (0 : ℝ) < 1 / 2)).toPositive
      (gaussianFactorRegularizationEntropyDensity_positive μ hμ _ _ _)

@[simp] theorem gaussianLinearRegularizationPositiveDensity_law
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ)
    (L : Matrix I J ℝ) (hL : Function.Surjective L.mulVec) :
    (gaussianLinearRegularizationPositiveDensity μ hμ L hL).law =
      Measure.conv μ (linearImageGaussian L) := by
  rw [gaussianLinearRegularizationPositiveDensity, FiniteEntropyDensity.toPositive_law]
  congr 1
  rw [heatGaussian_half_eq_standardVector]
  exact (eq_gaussianCovarianceLaw _ _ (rowGram_posDef_of_surjective L hL).posSemidef
    (linearImageGaussian_characteristic L)).symm

theorem independentAddLaw_one_eq_conv {I : Type*} [Fintype I]
    (μ ν : Measure (I → ℝ)) : independentAddLaw μ ν 1 = Measure.conv μ ν := by
  simp only [independentAddLaw, Measure.conv, one_smul]

end GaussianWave.BS
