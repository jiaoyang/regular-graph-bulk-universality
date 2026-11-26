import GeneralizedBulk.Gaussian.ProductWeakConvergence
import GeneralizedBulk.Gaussian.FiniteVector

/-! Computed Gaussian characteristic functions commute with products and linear restriction. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Gaussian

def GaussianCharacteristic {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) (C : Matrix ι ι ℝ) : Prop :=
  ∀ t : ι → ℝ,
    (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂μ) =
      Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic C t) : ℂ)

def sumCovariance {α β : Type*} (C : Matrix α α ℝ) (D : Matrix β β ℝ) :
    Matrix (Sum α β) (Sum α β) ℝ :=
  fun i j => match i, j with
    | .inl a, .inl b => C a b
    | .inr a, .inr b => D a b
    | _, _ => 0

theorem finiteCovarianceQuadratic_sum {α β : Type*} [Fintype α] [Fintype β]
    (C : Matrix α α ℝ) (D : Matrix β β ℝ) (t : Sum α β → ℝ) :
    finiteCovarianceQuadratic (sumCovariance C D) t =
      finiteCovarianceQuadratic C (t ∘ Sum.inl) + finiteCovarianceQuadratic D (t ∘ Sum.inr) := by
  simp only [finiteCovarianceQuadratic, Fintype.sum_sum_type, sumCovariance, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, Function.comp_apply]

theorem GaussianCharacteristic.vectorProductLaw {α β : Type*} [Fintype α] [Fintype β]
    {μ : Measure (α → ℝ)} {ν : Measure (β → ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {C : Matrix α α ℝ} {D : Matrix β β ℝ}
    (hμ : GaussianCharacteristic μ C) (hν : GaussianCharacteristic ν D) :
    GaussianCharacteristic (vectorProductLaw μ ν) (sumCovariance C D) := by
  intro t
  rw [vectorProductLaw_characteristic, hμ, hν, ← Complex.exp_add, finiteCovarianceQuadratic_sum]
  congr 1
  push_cast
  ring

theorem finiteCovarianceQuadratic_eq_dot {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (t : ι → ℝ) :
    finiteCovarianceQuadratic C t = t ⬝ᵥ C.mulVec t := by
  simp only [finiteCovarianceQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem finiteCovarianceQuadratic_conjugate {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : Matrix ι ι ℝ) (R : Matrix κ ι ℝ) (t : κ → ℝ) :
    finiteCovarianceQuadratic (R * C * R.transpose) t =
      finiteCovarianceQuadratic C (Matrix.vecMul t R) := by
  rw [finiteCovarianceQuadratic_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, ← finiteCovarianceQuadratic_eq_dot]

theorem GaussianCharacteristic.linearImage {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : Measure (ι → ℝ)} {C : Matrix ι ι ℝ} (hμ : GaussianCharacteristic μ C)
    (R : Matrix κ ι ℝ) :
    GaussianCharacteristic (Measure.map (fun x => R.mulVec x) μ) (R * C * R.transpose) := by
  intro t
  have hm : AEStronglyMeasurable
      (fun x => Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I))
      (Measure.map (fun x => R.mulVec x) μ) := (linearCharacteristic t).continuous.aestronglyMeasurable
  rw [integral_map (measurable_finiteMatrixAction R).aemeasurable hm]
  simp_rw [finiteLinearForm_matrixAction]
  rw [hμ, finiteCovarianceQuadratic_conjugate]

end GeneralizedBulk.Gaussian
