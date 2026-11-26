import GaussianWave.BS.GaussianEntropyWitness
import GaussianWave.BS.LinearEntropy
import GaussianWave.BS.HeatSymmetry

/-! Positive Gaussian regularization gives an actual finite-entropy density
for every finite-second-moment law, including arbitrary nondegenerate
covariance factors and initially singular laws. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

/-- A finite-entropy density witness of the actual arbitrary-law heat flow. -/
def heatedLawEntropyDensity {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) :
    FiniteEntropyDensity (heatedLaw μ t) where
  density := heatDensity μ t
  measurable := measurable_heatDensity μ t
  nonneg := heatDensity_nonneg μ t
  integrable := integrable_heatDensity μ ht
  integral_eq_one := integral_heatDensity μ ht
  integrable_log := integrable_heatDensity_log μ hμ ht
  measure_eq := heatedLaw_eq_withDensity μ ht

@[simp] theorem heatedLawEntropyDensity_entropy {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) :
    (heatedLawEntropyDensity μ hμ ht).entropy = densityEntropy volume (heatDensity μ t) := rfl

/-- Invertibly transported heat noise still smooths an arbitrary law. The
law equality is proved from actual linear maps and convolution; finite
entropy is constructed, not required of the original law. -/
def gaussianFactorRegularizationEntropyDensity
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ)
    (A : Matrix I I ℝ) (hA : A.det ≠ 0) {t : ℝ} (ht : 0 < t) :
    FiniteEntropyDensity (Measure.conv μ (Measure.map A.mulVec (heatGaussian I t))) := by
  let ν := Measure.map A⁻¹.mulVec μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map (measurable_finiteMatrixAction A⁻¹).aemeasurable
  have hν := integrable_squareRadius_matrixImage μ hμ A⁻¹
  have hmap : Measure.map A.mulVec ν = μ := by
    rw [Measure.map_map (measurable_finiteMatrixAction A) (measurable_finiteMatrixAction A⁻¹)]
    have he : A.mulVec ∘ A⁻¹.mulVec = id := by
      funext x
      rw [Function.comp_apply, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]
      rfl
    rw [he, Measure.map_id]
  have hactual : Measure.map A.mulVec (heatedLaw ν t) =
      Measure.conv μ (Measure.map A.mulVec (heatGaussian I t)) := by
    rw [heatedLaw, map_convolution_of_measurable_additive ν _ A.mulVec
      (measurable_finiteMatrixAction A) (fun x y => Matrix.mulVec_add A x y), hmap]
  exact ((heatedLawEntropyDensity ν hν ht).linearImage A hA).cast hactual.symm
end GaussianWave.BS
