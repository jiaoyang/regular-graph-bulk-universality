import GaussianWave.BS.GaussianBallSupport

/-!
# Actual intrinsic Gaussian density and entropy

A rectangular surjective Gaussian factor has positive definite row Gram.
Its actual density and entropy are constructed through the proved square
Gaussian factor, rather than postulated as an entropy formula.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

theorem rowGram_posDef_of_surjective {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (L : Matrix I J ℝ)
    (hL : Function.Surjective L.mulVec) : (L * L.transpose).PosDef := by
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hL
  have hinj : Function.Injective (fun x => Matrix.vecMul x L) := by
    intro x y hxy
    have h := congrArg (fun z => Matrix.vecMul z B) hxy
    simpa only [Matrix.vecMul_vecMul, hB, Matrix.vecMul_one] using h
  have h := (Matrix.PosDef.one : (1 : Matrix J J ℝ).PosDef).mul_mul_conjTranspose_same hinj
  simpa only [Matrix.mul_one, Matrix.conjTranspose, star_trivial, Matrix.map_id] using h

theorem posDef_sqrt_det_ne_zero {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℝ) (hC : C.PosDef) : hC.posSemidef.sqrt.det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det hC.posSemidef.sqrt_mul_self
  rw [Matrix.det_mul, hzero, zero_mul] at hdet
  exact hC.det_pos.ne' hdet.symm

def positiveGaussianEntropyDensity {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℝ) (hC : C.PosDef) :
    FiniteEntropyDensity (gaussianCovarianceLaw C hC.posSemidef) :=
  (standardVectorEntropyDensity I).linearImage hC.posSemidef.sqrt (posDef_sqrt_det_ne_zero C hC)

theorem positiveGaussianEntropyDensity_entropy {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℝ) (hC : C.PosDef) :
    (positiveGaussianEntropyDensity C hC).entropy =
      gaussianEntropyValue I 1 + (1 / 2 : ℝ) * Real.log C.det := by
  unfold positiveGaussianEntropyDensity
  rw [FiniteEntropyDensity.linearImage_entropy, standardVectorEntropyDensity_entropy]
  have hdet : hC.posSemidef.sqrt.det ^ 2 = C.det := by
    rw [pow_two, ← Matrix.det_mul, hC.posSemidef.sqrt_mul_self]
  have hlog : Real.log C.det = 2 * Real.log |hC.posSemidef.sqrt.det| := by
    rw [← hdet, Real.log_pow, Real.log_abs]
    norm_num
  rw [hlog]
  ring

def linearImageGaussianEntropyDensity {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (L : Matrix I J ℝ)
    (hL : Function.Surjective L.mulVec) : FiniteEntropyDensity (linearImageGaussian L) :=
  (positiveGaussianEntropyDensity (L * L.transpose) (rowGram_posDef_of_surjective L hL)).cast
    (eq_gaussianCovarianceLaw _ _ (rowGram_posDef_of_surjective L hL).posSemidef
      (linearImageGaussian_characteristic L))

theorem linearImageGaussianEntropyDensity_entropy {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (L : Matrix I J ℝ)
    (hL : Function.Surjective L.mulVec) :
    (linearImageGaussianEntropyDensity L hL).entropy =
      gaussianEntropyValue I 1 + (1 / 2 : ℝ) * Real.log (L * L.transpose).det := by
  exact positiveGaussianEntropyDensity_entropy (L * L.transpose) (rowGram_posDef_of_surjective L hL)

def vertexInnovationGaussianMatrix (m k : ℕ) (energy : ℝ) :
    Matrix (VertexBallInnovation (m + 2) k) (VertexGaussianInput m k) ℝ :=
  LinearMap.toMatrix' (vertexGaussianInnovationLinear m k energy)

def edgeInnovationGaussianMatrix (m k : ℕ) (energy : ℝ) :
    Matrix (EdgeBallInnovation (m + 2) k) (EdgeGaussianInput m k) ℝ :=
  LinearMap.toMatrix' (edgeGaussianInnovationLinear m k energy)

theorem vertexInnovationGaussianMatrix_surjective (m k : ℕ) (energy : ℝ)
    (he : |energy| < ((m + 2 : ℕ) : ℝ)) :
    Function.Surjective (vertexInnovationGaussianMatrix m k energy).mulVec := by
  have h : (vertexInnovationGaussianMatrix m k energy).mulVec =
      vertexGaussianInnovationLinear m k energy :=
    congrArg DFunLike.coe (Matrix.toLin'_toMatrix' (vertexGaussianInnovationLinear m k energy))
  rw [h]
  exact vertexGaussianInnovation_surjective m k energy he

theorem edgeInnovationGaussianMatrix_surjective (m k : ℕ) (energy : ℝ)
    (he : |energy| < ((m + 2 : ℕ) : ℝ)) :
    Function.Surjective (edgeInnovationGaussianMatrix m k energy).mulVec := by
  have h : (edgeInnovationGaussianMatrix m k energy).mulVec =
      edgeGaussianInnovationLinear m k energy :=
    congrArg DFunLike.coe (Matrix.toLin'_toMatrix' (edgeGaussianInnovationLinear m k energy))
  rw [h]
  exact edgeGaussianInnovation_surjective m k energy he

def vertexInnovationGaussianEntropyDensity (m k : ℕ) (energy : ℝ)
    (he : |energy| < ((m + 2 : ℕ) : ℝ)) :
    FiniteEntropyDensity (linearImageGaussian (vertexInnovationGaussianMatrix m k energy)) :=
  linearImageGaussianEntropyDensity _ (vertexInnovationGaussianMatrix_surjective m k energy he)

def edgeInnovationGaussianEntropyDensity (m k : ℕ) (energy : ℝ)
    (he : |energy| < ((m + 2 : ℕ) : ℝ)) :
    FiniteEntropyDensity (linearImageGaussian (edgeInnovationGaussianMatrix m k energy)) :=
  linearImageGaussianEntropyDensity _ (edgeInnovationGaussianMatrix_surjective m k energy he)

end GaussianWave.BS
