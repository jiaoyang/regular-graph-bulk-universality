import GaussianWave.BS.HeatFlow
import GaussianWave.BS.UpperStrictness

/-!
# Heat flow commutes with orthogonal projections and preserves symmetries

All statements below are equalities of actual measures. A rectangular matrix
with orthonormal rows maps the ambient heat noise to the correct lower
dimensional heat noise. Thus the marginal flow used in the entropy functional
is the heat flow of the original marginal.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace GaussianWave.BS

theorem centeredGaussian_characteristic_integral (v : ℝ≥0) (s : ℝ) :
    (∫ x : ℝ, Complex.exp ((↑(s * x) : ℂ) * Complex.I) ∂gaussianReal 0 v) =
      Complex.exp (↑(-(1 / 2 : ℝ) * (v : ℝ) * s ^ 2) : ℂ) := by
  calc
    _ = charFun (gaussianReal 0 v) s := by
      rw [charFun_apply]
      congr 1
    _ = _ := by
      rw [charFun_gaussianReal]
      congr 1
      push_cast
      ring

theorem heatGaussian_characteristic {I : Type*} [Fintype I] (t : ℝ) (s : I → ℝ) :
    characteristicIntegral (heatGaussian I t) s =
      Complex.exp (↑(-(1 / 2 : ℝ) * (heatVariance t : ℝ) * squareMass s) : ℂ) := by
  have heq : (fun x : I → ℝ => Complex.exp ((↑(finiteLinearForm s x) : ℂ) * Complex.I)) =
      (fun x => ∏ i, Complex.exp ((↑(s i * x i) : ℂ) * Complex.I)) := by
    funext x
    simp only [finiteLinearForm, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  unfold characteristicIntegral
  rw [heq]
  have hfub : (∫ x : I → ℝ, ∏ i, Complex.exp ((↑(s i * x i) : ℂ) * Complex.I)
      ∂heatGaussian I t) =
      ∏ i, ∫ x : ℝ, Complex.exp ((↑(s i * x) : ℂ) * Complex.I) ∂gaussianReal 0 (heatVariance t) := by
    letI : MeasureSpace ℝ := ⟨gaussianReal 0 (heatVariance t)⟩
    letI : IsProbabilityMeasure (volume : Measure ℝ) :=
      (inferInstance : IsProbabilityMeasure (gaussianReal 0 (heatVariance t)))
    simpa only [heatGaussian, volume_pi] using integral_fintype_prod_eq_prod I
      (fun i : I => fun x : ℝ => Complex.exp ((↑(s i * x) : ℂ) * Complex.I))
  rw [hfub]
  simp_rw [centeredGaussian_characteristic_integral]
  rw [← Complex.exp_sum]
  congr 1
  simp only [squareMass]
  push_cast
  simp only [Finset.mul_sum, Complex.ofReal_sum]

theorem squareMass_vecMul_of_orthonormal_rows
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (O : Matrix J I ℝ) (hO : O * O.transpose = 1) (s : J → ℝ) :
    squareMass (Matrix.vecMul s O) = squareMass s := by
  calc
    _ = Matrix.vecMul s O ⬝ᵥ O.transpose.mulVec s := by
      rw [Matrix.mulVec_transpose]
      simp only [squareMass, dotProduct, pow_two]
    _ = s ⬝ᵥ O.mulVec (O.transpose.mulVec s) := (Matrix.dotProduct_mulVec ..).symm
    _ = s ⬝ᵥ (O * O.transpose).mulVec s := by rw [Matrix.mulVec_mulVec]
    _ = _ := by rw [hO, Matrix.one_mulVec]; simp only [squareMass, dotProduct, pow_two]

/-- Actual projection of isotropic Gaussian noise, in any target dimension. -/
theorem heatGaussian_map_orthonormal_rows
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (O : Matrix J I ℝ) (hO : O * O.transpose = 1) (t : ℝ) :
    Measure.map (fun x : I → ℝ => O.mulVec x) (heatGaussian I t) = heatGaussian J t := by
  letI : IsProbabilityMeasure (Measure.map (fun x : I → ℝ => O.mulVec x) (heatGaussian I t)) :=
    isProbabilityMeasure_map (measurable_finiteMatrixAction O).aemeasurable
  apply measure_eq_of_linear_characteristic
  intro s
  change (∫ x, (linearCharacteristic s) x
    ∂Measure.map (fun x : I → ℝ => O.mulVec x) (heatGaussian I t)) = _
  rw [integral_map (measurable_finiteMatrixAction O).aemeasurable
    (linearCharacteristic s).continuous.measurable.aestronglyMeasurable]
  change (∫ x, Complex.exp ((↑(finiteLinearForm s (O.mulVec x)) : ℂ) * Complex.I)
    ∂heatGaussian I t) = _
  simp_rw [finiteLinearForm_matrixAction]
  change characteristicIntegral (heatGaussian I t) (Matrix.vecMul s O) =
    characteristicIntegral (heatGaussian J t) s
  rw [heatGaussian_characteristic, heatGaussian_characteristic,
    squareMass_vecMul_of_orthonormal_rows O hO]

theorem map_convolution_of_measurable_additive
    {I J : Type*} [Fintype I] [Fintype J]
    (μ ν : Measure (I → ℝ)) [SFinite μ] [SFinite ν]
    (f : (I → ℝ) → (J → ℝ)) (hf : Measurable f)
    (hadd : ∀ x y, f (x + y) = f x + f y) :
    Measure.map f (Measure.conv μ ν) = Measure.conv (Measure.map f μ) (Measure.map f ν) := by
  unfold Measure.conv
  rw [Measure.map_map hf (measurable_fst.add measurable_snd), Measure.map_prod_map μ ν hf hf,
    Measure.map_map (measurable_fst.add measurable_snd) (hf.prodMap hf)]
  congr 1
  funext z
  exact hadd z.1 z.2

/-- The true orthogonal marginal of the heat flow is the heat flow of the true
original marginal. This also proves preservation of every orthogonal symmetry. -/
theorem heatedLaw_map_orthonormal_rows
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (μ : Measure (I → ℝ)) [SFinite μ]
    (O : Matrix J I ℝ) (hO : O * O.transpose = 1) (t : ℝ) :
    Measure.map (fun x : I → ℝ => O.mulVec x) (heatedLaw μ t) =
      heatedLaw (Measure.map (fun x : I → ℝ => O.mulVec x) μ) t := by
  unfold heatedLaw
  rw [map_convolution_of_measurable_additive μ (heatGaussian I t)
    (fun x => O.mulVec x) (measurable_finiteMatrixAction O) (fun x y => Matrix.mulVec_add _ _ _),
    heatGaussian_map_orthonormal_rows O hO]

theorem heatedLaw_orthogonal_symmetry
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) [SFinite μ] (O : Matrix I I ℝ)
    (hO : O * O.transpose = 1) (hsym : Measure.map (fun x => O.mulVec x) μ = μ) (t : ℝ) :
    Measure.map (fun x => O.mulVec x) (heatedLaw μ t) = heatedLaw μ t := by
  rw [heatedLaw_map_orthonormal_rows μ O hO, hsym]

end GaussianWave.BS
