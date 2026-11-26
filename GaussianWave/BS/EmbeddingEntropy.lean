import GaussianWave.BS.LinearEntropy
import GaussianWave.BS.GaussianEntropyWitness

/-!
# Intrinsic entropy charts for arbitrary full-column embeddings

The range equivalence and its inverse are constructed from `B*L=1`.
Finite entropy in an arbitrary intrinsic chart is transported to the actual
white law. The same Jacobian cancels against the actual embedded Gaussian;
no moment, density, or Gaussianity claim about the unknown white law is an
assumption.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

abbrev MatrixRange (L : Matrix I J ℝ) := LinearMap.range (Matrix.toLin' L)

/-- Actual continuous linear coordinates on the range of a full-column
matrix; the supplied left inverse is used as its literal inverse. -/
def matrixRangeEquiv (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1) :
    (J → ℝ) ≃L[ℝ] MatrixRange L :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun y => ⟨L.mulVec y, ⟨y, rfl⟩⟩
      invFun := fun z => B.mulVec z
      left_inv := fun y => by
        change B.mulVec (L.mulVec y) = y
        rw [Matrix.mulVec_mulVec, hBL, Matrix.one_mulVec]
      right_inv := fun z => by
        apply Subtype.ext
        rcases z.property with ⟨y, hy⟩
        change L.mulVec (B.mulVec z.val) = z.val
        change L.mulVec y = z.val at hy
        rw [← hy]
        have hleft : B.mulVec (L.mulVec y) = y := by
          rw [Matrix.mulVec_mulVec, hBL, Matrix.one_mulVec]
        exact congrArg L.mulVec hleft
      map_add' := fun x y => Subtype.ext (Matrix.mulVec_add L x y)
      map_smul' := fun a x => Subtype.ext (Matrix.mulVec_smul L a x) }

@[simp] theorem matrixRangeEquiv_coe (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (y : J → ℝ) : (matrixRangeEquiv L B hBL y : I → ℝ) = L.mulVec y := rfl

@[simp] theorem matrixRangeEquiv_symm_apply (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (z : MatrixRange L) : (matrixRangeEquiv L B hBL).symm z = B.mulVec z := rfl

def embeddingChartEquiv (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (chart : MatrixRange L ≃ₗ[ℝ] (J → ℝ)) : (J → ℝ) ≃ₗ[ℝ] (J → ℝ) :=
  (matrixRangeEquiv L B hBL).toLinearEquiv.trans chart

def embeddingChartMatrix (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (chart : MatrixRange L ≃ₗ[ℝ] (J → ℝ)) : Matrix J J ℝ :=
  LinearMap.toMatrix' (embeddingChartEquiv L B hBL chart).toLinearMap

def embeddingInverseChartMatrix (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (chart : MatrixRange L ≃ₗ[ℝ] (J → ℝ)) : Matrix J J ℝ :=
  LinearMap.toMatrix' (embeddingChartEquiv L B hBL chart).symm.toLinearMap

theorem embeddingChartMatrix_mulVec (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (chart : MatrixRange L ≃ₗ[ℝ] (J → ℝ)) (y : J → ℝ) :
    (embeddingChartMatrix L B hBL chart).mulVec y = chart (matrixRangeEquiv L B hBL y) := by
  change Matrix.toLin' (LinearMap.toMatrix' (embeddingChartEquiv L B hBL chart).toLinearMap) y = _
  rw [Matrix.toLin'_toMatrix']
  rfl

theorem embeddingInverseChartMatrix_mulVec (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (chart : MatrixRange L ≃ₗ[ℝ] (J → ℝ)) (y : J → ℝ) :
    (embeddingInverseChartMatrix L B hBL chart).mulVec y =
      (matrixRangeEquiv L B hBL).symm (chart.symm y) := by
  change Matrix.toLin' (LinearMap.toMatrix' (embeddingChartEquiv L B hBL chart).symm.toLinearMap) y = _
  rw [Matrix.toLin'_toMatrix']
  rfl

theorem embeddingChartMatrix_det_ne_zero (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (chart : MatrixRange L ≃ₗ[ℝ] (J → ℝ)) : (embeddingChartMatrix L B hBL chart).det ≠ 0 := by
  simpa only [embeddingChartMatrix, LinearMap.det_toMatrix'] using
    (embeddingChartEquiv L B hBL chart).isUnit_det'.ne_zero

theorem embeddingInverseChartMatrix_det_ne_zero (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (chart : MatrixRange L ≃ₗ[ℝ] (J → ℝ)) : (embeddingInverseChartMatrix L B hBL chart).det ≠ 0 := by
  simpa only [embeddingInverseChartMatrix, LinearMap.det_toMatrix'] using
    (embeddingChartEquiv L B hBL chart).symm.isUnit_det'.ne_zero

/-- The actual white law, without an assumed density or covariance. -/
def embeddingWhiteLaw (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (N : Measure (MatrixRange L)) : Measure (J → ℝ) :=
  Measure.map (matrixRangeEquiv L B hBL).symm N

instance embeddingWhiteLaw_isProbability
    (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (N : Measure (MatrixRange L)) [IsProbabilityMeasure N] :
    IsProbabilityMeasure (embeddingWhiteLaw L B hBL N) :=
  isProbabilityMeasure_map (matrixRangeEquiv L B hBL).symm.continuous.measurable.aemeasurable

theorem embeddingWhiteLaw_eq_inverseChartImage
    (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (chart : MatrixRange L ≃ₗ[ℝ] (J → ℝ)) (N : Measure (MatrixRange L)) :
    embeddingWhiteLaw L B hBL N =
      Measure.map (fun y => (embeddingInverseChartMatrix L B hBL chart).mulVec y) (Measure.map chart N) := by
  have hc : Measurable (chart : MatrixRange L → (J → ℝ)) :=
    chart.continuous_of_finiteDimensional.measurable
  unfold embeddingWhiteLaw
  rw [Measure.map_map (measurable_finiteMatrixAction _) hc]
  congr 1
  funext z
  change (matrixRangeEquiv L B hBL).symm z =
    (embeddingInverseChartMatrix L B hBL chart).mulVec (chart z)
  rw [embeddingInverseChartMatrix_mulVec, chart.symm_apply_apply]

/-- A white finite-entropy density is constructed from an intrinsic chart
density by the proved invertible-matrix density transport. -/
def FiniteEntropyDensity.embeddingWhite
    (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (chart : MatrixRange L ≃ₗ[ℝ] (J → ℝ))
    (N : Measure (MatrixRange L)) [IsProbabilityMeasure N]
    (f : FiniteEntropyDensity (Measure.map chart N)) :
    FiniteEntropyDensity (embeddingWhiteLaw L B hBL N) := by
  letI : IsProbabilityMeasure (Measure.map chart N) :=
    isProbabilityMeasure_map chart.continuous_of_finiteDimensional.measurable.aemeasurable
  exact (f.linearImage (embeddingInverseChartMatrix L B hBL chart)
    (embeddingInverseChartMatrix_det_ne_zero L B hBL chart)).cast
      (embeddingWhiteLaw_eq_inverseChartImage L B hBL chart N)

theorem embeddingWhite_entropy_difference
    (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (chart : MatrixRange L ≃ₗ[ℝ] (J → ℝ))
    (N M : Measure (MatrixRange L)) [IsProbabilityMeasure N] [IsProbabilityMeasure M]
    (f : FiniteEntropyDensity (Measure.map chart N)) (g : FiniteEntropyDensity (Measure.map chart M)) :
    (f.embeddingWhite L B hBL chart N).entropy - (g.embeddingWhite L B hBL chart M).entropy =
      f.entropy - g.entropy := by
  letI : IsProbabilityMeasure (Measure.map chart N) :=
    isProbabilityMeasure_map chart.continuous_of_finiteDimensional.measurable.aemeasurable
  letI : IsProbabilityMeasure (Measure.map chart M) :=
    isProbabilityMeasure_map chart.continuous_of_finiteDimensional.measurable.aemeasurable
  exact f.linearImage_entropy_difference g (embeddingInverseChartMatrix L B hBL chart)
    (embeddingInverseChartMatrix_det_ne_zero L B hBL chart)

/-- The actual Gaussian probability law on the embedded range. -/
def embeddingGaussian (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1) :
    Measure (MatrixRange L) := Measure.map (matrixRangeEquiv L B hBL) (standardVector J)

instance embeddingGaussian_isProbability (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1) :
    IsProbabilityMeasure (embeddingGaussian L B hBL) :=
  isProbabilityMeasure_map (matrixRangeEquiv L B hBL).continuous.measurable.aemeasurable

theorem embeddingWhiteLaw_embeddingGaussian (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1) :
    embeddingWhiteLaw L B hBL (embeddingGaussian L B hBL) = standardVector J := by
  rw [embeddingWhiteLaw, embeddingGaussian,
    Measure.map_map (matrixRangeEquiv L B hBL).symm.continuous.measurable
      (matrixRangeEquiv L B hBL).continuous.measurable]
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
    (Measure.map_id (μ := standardVector J))

def embeddingGaussianChartDensity
    (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (chart : MatrixRange L ≃ₗ[ℝ] (J → ℝ)) :
    FiniteEntropyDensity (Measure.map chart (embeddingGaussian L B hBL)) := by
  have hmap : Measure.map chart (embeddingGaussian L B hBL) =
      Measure.map (fun y => (embeddingChartMatrix L B hBL chart).mulVec y) (standardVector J) := by
    have hc : Measurable (chart : MatrixRange L → (J → ℝ)) :=
      chart.continuous_of_finiteDimensional.measurable
    rw [embeddingGaussian, Measure.map_map hc
      (matrixRangeEquiv L B hBL).continuous.measurable]
    congr 1
    funext y
    exact (embeddingChartMatrix_mulVec L B hBL chart y).symm
  exact ((standardVectorEntropyDensity J).linearImage (embeddingChartMatrix L B hBL chart)
    (embeddingChartMatrix_det_ne_zero L B hBL chart)).cast hmap

/-- Intrinsic Gaussian-relative entropy cancellation for an actual unknown
range law and the actual embedded standard Gaussian. -/
theorem embeddingGaussian_relative_entropy_cancellation
    (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (chart : MatrixRange L ≃ₗ[ℝ] (J → ℝ))
    (N : Measure (MatrixRange L)) [IsProbabilityMeasure N]
    (f : FiniteEntropyDensity (Measure.map chart N)) :
    f.entropy - (embeddingGaussianChartDensity L B hBL chart).entropy =
      (f.embeddingWhite L B hBL chart N).entropy - (standardVectorEntropyDensity J).entropy := by
  have h := embeddingWhite_entropy_difference L B hBL chart N (embeddingGaussian L B hBL)
    f (embeddingGaussianChartDensity L B hBL chart)
  have hg := ((embeddingGaussianChartDensity L B hBL chart).embeddingWhite L B hBL chart
    (embeddingGaussian L B hBL)).entropy_eq_of_measure_eq (standardVectorEntropyDensity J)
      (embeddingWhiteLaw_embeddingGaussian L B hBL)
  rw [hg] at h
  exact h.symm

theorem embeddingWhiteLaw_eq_ambient_leftInverse
    (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (N : Measure (MatrixRange L)) :
    embeddingWhiteLaw L B hBL N =
      Measure.map (fun x => B.mulVec x) (Measure.map (fun z : MatrixRange L => (z : I → ℝ)) N) := by
  rw [embeddingWhiteLaw, Measure.map_map (measurable_finiteMatrixAction B) measurable_subtype_coe]
  rfl

theorem matrixRangeEquiv_map_embeddingWhiteLaw
    (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1)
    (N : Measure (MatrixRange L)) :
    Measure.map (matrixRangeEquiv L B hBL) (embeddingWhiteLaw L B hBL N) = N := by
  rw [embeddingWhiteLaw, Measure.map_map (matrixRangeEquiv L B hBL).continuous.measurable
    (matrixRangeEquiv L B hBL).symm.continuous.measurable]
  simpa only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using
    (Measure.map_id (μ := N))

theorem embeddingGaussian_ambient_law
    (L : Matrix I J ℝ) (B : Matrix J I ℝ) (hBL : B * L = 1) :
    Measure.map (fun z : MatrixRange L => (z : I → ℝ)) (embeddingGaussian L B hBL) =
      linearImageGaussian L := by
  rw [embeddingGaussian, Measure.map_map measurable_subtype_coe
    (matrixRangeEquiv L B hBL).continuous.measurable]
  rfl

end GaussianWave.BS
