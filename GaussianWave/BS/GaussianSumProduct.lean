import GaussianWave.BS.InnovationNodeSplit

/-!
# Literal independent Gaussian products in sum-indexed coordinates
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def concatenateVector {I J : Type*} (z : (I → ℝ) × (J → ℝ)) : I ⊕ J → ℝ := Sum.elim z.1 z.2

theorem measurable_concatenateVector {I J : Type*} : Measurable (concatenateVector (I := I) (J := J)) := by
  apply measurable_pi_lambda
  intro j
  cases j with
  | inl i => exact (measurable_pi_apply i).comp measurable_fst
  | inr j => exact (measurable_pi_apply j).comp measurable_snd

theorem standardVector_sum_eq_product (I J : Type*) [Fintype I] [Fintype J] :
    standardVector (I ⊕ J) = Measure.map concatenateVector ((standardVector I).prod (standardVector J)) := by
  have h := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : I ⊕ J => ℝ)
    (fun _ => standardNormal)
  simpa only [standardVector, MeasurableEquiv.coe_sumPiEquivProdPi_symm, concatenateVector] using h.map_eq.symm

def sumVectorProductLaw {I J : Type*} (μ : Measure (I → ℝ)) (ν : Measure (J → ℝ)) :
    Measure (I ⊕ J → ℝ) := Measure.map concatenateVector (μ.prod ν)

theorem diagonalBlockFactor_mulVec {I J A B : Type*} [Fintype I] [Fintype J]
    (R : Matrix A I ℝ) (L : Matrix B J ℝ) (z : (I → ℝ) × (J → ℝ)) :
    (Matrix.fromBlocks R 0 0 L).mulVec (concatenateVector z) =
      concatenateVector (R.mulVec z.1, L.mulVec z.2) := by
  ext j
  cases j <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, concatenateVector]

/-- Exact product law for independent Gaussian factors on disjoint source
coordinates; this is an equality of actual measures. -/
theorem linearImageGaussian_diagonalBlocks {I J A B : Type*}
    [Fintype I] [Fintype J] (R : Matrix A I ℝ) (L : Matrix B J ℝ) :
    linearImageGaussian (Matrix.fromBlocks R 0 0 L) =
      sumVectorProductLaw (linearImageGaussian R) (linearImageGaussian L) := by
  unfold linearImageGaussian sumVectorProductLaw
  rw [standardVector_sum_eq_product, Measure.map_map (measurable_finiteMatrixAction _)
    measurable_concatenateVector]
  have hf : (fun z : (I → ℝ) × (J → ℝ) =>
      (Matrix.fromBlocks R 0 0 L).mulVec (concatenateVector z)) =
      concatenateVector ∘ Prod.map R.mulVec L.mulVec := funext (diagonalBlockFactor_mulVec R L)
  change Measure.map (fun z : (I → ℝ) × (J → ℝ) =>
    (Matrix.fromBlocks R 0 0 L).mulVec (concatenateVector z)) _ = _
  rw [hf, ← Measure.map_map measurable_concatenateVector
    ((measurable_finiteMatrixAction R).prodMap (measurable_finiteMatrixAction L)),
    ← Measure.map_prod_map _ _ (measurable_finiteMatrixAction R) (measurable_finiteMatrixAction L)]

end GaussianWave.BS
