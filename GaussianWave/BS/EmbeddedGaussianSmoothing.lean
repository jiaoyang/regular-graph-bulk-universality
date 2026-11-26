import GaussianWave.BS.EmbeddingEntropy
import GaussianWave.BS.GaussianSmoothingEntropy

/-! Smoothness inside the actual range of a full-column Gaussian factor.
The unknown law needs only finite second moment and its proved a.e. support;
all intrinsic chart densities of its Gaussian regularization are constructed. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The regularized probability law on the actual Gaussian support range. -/
def embeddedGaussianRegularizationRangeLaw
    (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B*L=1)
    (μ : Measure (I → ℝ)) (t : ℝ) : Measure (MatrixRange L) :=
  Measure.map (matrixRangeEquiv L B hBL) (heatedLaw (Measure.map B.mulVec μ) t)

instance embeddedGaussianRegularizationRangeLaw_isProbability
    (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B*L=1)
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] (t : ℝ) :
    IsProbabilityMeasure (embeddedGaussianRegularizationRangeLaw L B hBL μ t) := by
  letI : IsProbabilityMeasure (Measure.map B.mulVec μ) :=
    isProbabilityMeasure_map (measurable_finiteMatrixAction B).aemeasurable
  unfold embeddedGaussianRegularizationRangeLaw
  exact isProbabilityMeasure_map (matrixRangeEquiv L B hBL).continuous.measurable.aemeasurable

/-- Its ambient image is literally the independent sum of the unknown signal
and the embedded Gaussian noise; no support reconstruction is assumed for
the regularized law. -/
theorem embeddedGaussianRegularizationRangeLaw_ambient
    (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B*L=1)
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hsupport : ∀ᵐ x ∂μ, L.mulVec (B.mulVec x) = x) (t : ℝ) :
    Measure.map (fun z : MatrixRange L => (z : I → ℝ))
      (embeddedGaussianRegularizationRangeLaw L B hBL μ t) =
        Measure.conv μ (Measure.map L.mulVec (heatGaussian J t)) := by
  let ν := Measure.map B.mulVec μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map (measurable_finiteMatrixAction B).aemeasurable
  have hrec : Measure.map L.mulVec ν = μ := by
    rw [Measure.map_map (measurable_finiteMatrixAction L) (measurable_finiteMatrixAction B)]
    have he : L.mulVec ∘ B.mulVec =ᵐ[μ] id := hsupport
    rw [Measure.map_congr he, Measure.map_id]
  unfold embeddedGaussianRegularizationRangeLaw
  rw [Measure.map_map continuous_subtype_val.measurable (matrixRangeEquiv L B hBL).continuous.measurable]
  change Measure.map L.mulVec (heatedLaw ν t) = _
  rw [heatedLaw, map_convolution_of_measurable_additive ν _ L.mulVec
    (measurable_finiteMatrixAction L) (fun x y => Matrix.mulVec_add L x y), hrec]

/-- Every intrinsic linear chart of the regularized support law has a
constructed finite entropy density, including initially singular signal laws
and the zero-rank support convention. -/
def embeddedGaussianRegularizationChartDensity
    (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B*L=1)
    (chart : MatrixRange L ≃ₗ[ℝ] (J → ℝ))
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) :
    FiniteEntropyDensity (Measure.map chart (embeddedGaussianRegularizationRangeLaw L B hBL μ t)) := by
  let ν := Measure.map B.mulVec μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map (measurable_finiteMatrixAction B).aemeasurable
  have hν := integrable_squareRadius_matrixImage μ hμ B
  have hactual : Measure.map chart (embeddedGaussianRegularizationRangeLaw L B hBL μ t) =
      Measure.map (embeddingChartMatrix L B hBL chart).mulVec (heatedLaw ν t) := by
    have hc : Measurable (chart : MatrixRange L → (J → ℝ)) := chart.continuous_of_finiteDimensional.measurable
    unfold embeddedGaussianRegularizationRangeLaw
    rw [Measure.map_map hc
      (matrixRangeEquiv L B hBL).continuous.measurable]
    congr 1
    funext y
    exact (embeddingChartMatrix_mulVec L B hBL chart y).symm
  exact ((heatedLawEntropyDensity ν hν ht).linearImage (embeddingChartMatrix L B hBL chart)
    (embeddingChartMatrix_det_ne_zero L B hBL chart)).cast hactual
end GaussianWave.BS
