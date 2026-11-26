import GeneralizedBulk.Gaussian.Characteristic
import GeneralizedBulk.Gaussian.UniformIntegrability

/-! Actual finite standard Gaussian vectors and their orthogonal invariance. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Gaussian

def standardVector (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => standardNormal)

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (standardVector ι) := by
  unfold standardVector
  infer_instance

theorem standardVector_characteristic {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂standardVector ι) =
      Complex.exp (↑(-(1 / 2 : ℝ) * ∑ i, t i ^ 2) : ℂ) := by
  have hprod : (fun x : ι → ℝ => Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I)) =
      (fun x => ∏ i, Complex.exp ((↑(t i * x i) : ℂ) * Complex.I)) := by
    funext x
    simp only [finiteLinearForm, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  rw [hprod]
  have hfub : (∫ x, ∏ i, Complex.exp ((↑(t i * x i) : ℂ) * Complex.I) ∂standardVector ι) =
      ∏ i, ∫ a : ℝ, Complex.exp ((↑(t i * a) : ℂ) * Complex.I) ∂standardNormal := by
    letI : MeasureSpace ℝ := ⟨standardNormal⟩
    letI : IsProbabilityMeasure (volume : Measure ℝ) :=
      (inferInstance : IsProbabilityMeasure standardNormal)
    simpa only [standardVector, volume_pi] using integral_fintype_prod_eq_prod ι
      (fun i : ι => fun a : ℝ => Complex.exp ((↑(t i * a) : ℂ) * Complex.I))
  rw [hfub]
  simp_rw [scalar_characteristic]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem measurable_finiteMatrixAction {ι κ : Type*} [Fintype ι]
    (O : Matrix κ ι ℝ) : Measurable (fun x : ι → ℝ => O.mulVec x) := by
  apply measurable_pi_lambda
  intro i
  exact Finset.measurable_sum _ (fun j hj => measurable_const.mul (measurable_pi_apply j))

theorem finiteLinearForm_matrixAction {ι κ : Type*} [Fintype ι] [Fintype κ]
    (O : Matrix κ ι ℝ) (t : κ → ℝ) (x : ι → ℝ) :
    finiteLinearForm t (O.mulVec x) = finiteLinearForm (Matrix.vecMul t O) x :=
  Matrix.dotProduct_mulVec t O x

theorem vecMul_sq_sum_of_orthogonal {ι : Type*} [Fintype ι]
    (O : Matrix ι ι ℝ) (hO : O * O.transpose = 1) (t : ι → ℝ) :
    (∑ i, (Matrix.vecMul t O i) ^ 2) = ∑ i, t i ^ 2 := by
  calc
    _ = Matrix.vecMul t O ⬝ᵥ (O.transpose.mulVec t) := by
      rw [Matrix.mulVec_transpose]
      simp only [dotProduct, pow_two]
    _ = t ⬝ᵥ O.mulVec (O.transpose.mulVec t) := (Matrix.dotProduct_mulVec ..).symm
    _ = t ⬝ᵥ (O * O.transpose).mulVec t := by rw [Matrix.mulVec_mulVec]
    _ = _ := by rw [hO, Matrix.one_mulVec]; simp only [dotProduct, pow_two]

/-- Orthogonal invariance is proved for the actual finite independent normal
product law, and works in every finite dimension used by channel whitening. -/
theorem standardVector_orthogonal_invariant {ι : Type*} [Fintype ι]
    (O : Matrix ι ι ℝ) (hO : O * O.transpose = 1) :
    Measure.map (fun x : ι → ℝ => O.mulVec x) (standardVector ι) = standardVector ι := by
  letI : IsProbabilityMeasure (Measure.map (fun x : ι → ℝ => O.mulVec x) (standardVector ι)) :=
    MeasureTheory.isProbabilityMeasure_map (measurable_finiteMatrixAction O).aemeasurable
  apply measure_eq_of_linear_characteristic
  intro t
  change (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I)
    ∂Measure.map (fun x : ι → ℝ => O.mulVec x) (standardVector ι)) = _
  rw [integral_map (measurable_finiteMatrixAction O).aemeasurable]
  · simp_rw [finiteLinearForm_matrixAction]
    rw [standardVector_characteristic, vecMul_sq_sum_of_orthogonal O hO t,
      ← standardVector_characteristic]
    rfl
  · apply Measurable.aestronglyMeasurable
    exact Complex.continuous_exp.measurable.comp
      ((((continuous_finiteLinearForm t).measurable).complex_ofReal).mul measurable_const)

theorem standardVector_orthogonal_measurePreserving {ι : Type*} [Fintype ι]
    (O : Matrix ι ι ℝ) (hO : O * O.transpose = 1) :
    MeasurePreserving (fun x : ι → ℝ => O.mulVec x) (standardVector ι) (standardVector ι) :=
  ⟨measurable_finiteMatrixAction O, standardVector_orthogonal_invariant O hO⟩

theorem finiteCovarianceQuadratic_gram {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : Matrix κ ι ℝ) (t : κ → ℝ) :
    finiteCovarianceQuadratic (L * L.transpose) t = ∑ i, (Matrix.vecMul t L i) ^ 2 := by
  calc
    _ = t ⬝ᵥ (L * L.transpose).mulVec t := by
      simp only [finiteCovarianceQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    _ = t ⬝ᵥ L.mulVec (L.transpose.mulVec t) := by rw [Matrix.mulVec_mulVec]
    _ = Matrix.vecMul t L ⬝ᵥ (L.transpose.mulVec t) := Matrix.dotProduct_mulVec ..
    _ = _ := by rw [Matrix.mulVec_transpose]; simp only [dotProduct, pow_two]

def linearImageGaussian {ι κ : Type*} [Fintype ι] (L : Matrix κ ι ℝ) : Measure (κ → ℝ) :=
  Measure.map (fun x : ι → ℝ => L.mulVec x) (standardVector ι)

instance {ι κ : Type*} [Fintype ι] (L : Matrix κ ι ℝ) :
    IsProbabilityMeasure (linearImageGaussian L) :=
  MeasureTheory.isProbabilityMeasure_map (measurable_finiteMatrixAction L).aemeasurable

/-- Every finite rectangular linear image of actual independent standard
normals has its computed row-Gram characteristic function, even when singular. -/
theorem linearImageGaussian_characteristic {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : Matrix κ ι ℝ) (t : κ → ℝ) :
    (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂linearImageGaussian L) =
      Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic (L * L.transpose) t) : ℂ) := by
  rw [linearImageGaussian, integral_map (measurable_finiteMatrixAction L).aemeasurable]
  · simp_rw [finiteLinearForm_matrixAction]
    rw [standardVector_characteristic, finiteCovarianceQuadratic_gram]
  · exact Complex.continuous_exp.measurable.comp
      ((((continuous_finiteLinearForm t).measurable).complex_ofReal).mul measurable_const)
      |>.aestronglyMeasurable

end GeneralizedBulk.Gaussian
