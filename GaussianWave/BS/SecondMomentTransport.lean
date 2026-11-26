import GaussianWave.BS.WhiteSecondMoments

/-!
# Whitening actual second moments

Rectangular left inverses are allowed, so the source law may live on the
eigenrelation hyperplane inside a larger ambient space. Moment normalization
is derived from the source Gram covariance, not assumed after whitening.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def HasSecondMoments {I : Type*} [Fintype I] (μ : Measure (I → ℝ)) (C : Matrix I I ℝ) : Prop :=
  ∀ i j, (∫ x, x i * x j ∂μ) = C i j

theorem integrable_squareRadius_of_unitDiagonal_secondMoments
    {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) (C : Matrix I I ℝ)
    (hC : HasSecondMoments μ C) (hdiag : ∀ i, C i i = 1) :
    Integrable (squareRadius (I := I)) μ := by
  unfold squareRadius
  apply integrable_finset_sum
  intro i _
  apply integrable_of_integral_eq_one
  simpa only [pow_two, hdiag] using hC i i

theorem integral_linearForm_mul_of_secondMoments
    {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) (hμ : Integrable (squareRadius (I := I)) μ)
    (C : Matrix I I ℝ) (hC : HasSecondMoments μ C) (u v : I → ℝ) :
    (∫ x, finiteLinearForm u x * finiteLinearForm v x ∂μ) =
      ∑ i, ∑ j, u i * C i j * v j := by
  unfold HasSecondMoments at hC
  have heq : (fun x => finiteLinearForm u x * finiteLinearForm v x) =
      (fun x => ∑ i, ∑ j, (u i * v j) * (x i * x j)) := by
    funext x
    unfold finiteLinearForm
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, integral_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => (integrable_coordinate_mul_of_squareRadius μ hμ i j).const_mul _))]
  simp_rw [integral_finset_sum _ (fun j _ =>
    (integrable_coordinate_mul_of_squareRadius μ hμ _ j).const_mul _), integral_const_mul, hC]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem secondMoments_matrixImage
    {I J : Type*} [Fintype I] [Fintype J]
    (μ : Measure (I → ℝ)) (hμ : Integrable (squareRadius (I := I)) μ)
    (C : Matrix I I ℝ) (hC : HasSecondMoments μ C) (B : Matrix J I ℝ) :
    HasSecondMoments (Measure.map (fun x => B.mulVec x) μ) (B * C * B.transpose) := by
  intro p q
  rw [integral_map (measurable_finiteMatrixAction B).aemeasurable
    ((continuous_apply p).mul (continuous_apply q)).measurable.aestronglyMeasurable]
  change (∫ x, finiteLinearForm (B p) x * finiteLinearForm (B q) x ∂μ) = _
  rw [integral_linearForm_mul_of_secondMoments μ hμ C hC]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- A genuine left inverse whitens a law with the corresponding Gram second
moments, including a source law supported in a larger ambient space. -/
theorem identitySecondMoments_of_gram_leftInverse
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (μ : Measure (I → ℝ)) (hμ : Integrable (squareRadius (I := I)) μ)
    (L : Matrix I J ℝ) (B : Matrix J I ℝ)
    (hC : HasSecondMoments μ (L * L.transpose)) (hBL : B * L = 1) :
    HasIdentitySecondMoments (Measure.map (fun x => B.mulVec x) μ) := by
  have h := secondMoments_matrixImage μ hμ (L * L.transpose) hC B
  have heq : B * (L * L.transpose) * B.transpose = 1 := by
    calc
      _ = (B * L) * (B * L).transpose := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hBL]; simp
  rw [heq] at h
  intro i j
  simpa only [Matrix.one_apply] using h i j

end GaussianWave.BS
