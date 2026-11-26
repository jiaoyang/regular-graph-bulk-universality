import GaussianWave.BS.HeatEntropyFunctional

/-!
# Ordinary second-moment normalization in white coordinates

These computations turn the actual identity second moments into the trace
normalizations used by the large-noise entropy endpoint, for every actual
orthonormal-row edge projection.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def HasIdentitySecondMoments {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) : Prop :=
  ∀ i j, (∫ x, x i * x j ∂μ) = if i = j then 1 else 0

/-- Unit diagonal moments already imply genuine second-moment integrability:
a nonintegrable Bochner integral would be zero, so cannot equal one. -/
theorem integrable_squareRadius_of_identitySecondMoments
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) (hmom : HasIdentitySecondMoments μ) :
    Integrable (squareRadius (I := I)) μ := by
  unfold squareRadius
  apply integrable_finset_sum
  intro i _
  apply integrable_of_integral_eq_one
  simpa only [pow_two, if_pos rfl] using hmom i i

theorem abs_coordinate_mul_le_squareRadius
    {I : Type*} [Fintype I] (x : I → ℝ) (i j : I) : |x i * x j| ≤ squareRadius x := by
  have hi : (x i) ^ 2 ≤ squareRadius x :=
    Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_univ i)
  have hj : (x j) ^ 2 ≤ squareRadius x :=
    Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_univ j)
  rw [abs_mul]
  nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]

theorem integrable_coordinate_mul_of_squareRadius
    {I : Type*} [Fintype I] (μ : Measure (I → ℝ))
    (hμ : Integrable (squareRadius (I := I)) μ) (i j : I) :
    Integrable (fun x => x i * x j) μ := by
  refine hμ.mono' ((continuous_apply i).mul (continuous_apply j)).measurable.aestronglyMeasurable ?_
  exact ae_of_all _ (fun x => abs_coordinate_mul_le_squareRadius x i j)

theorem integral_linearForm_sq_of_identitySecondMoments
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) (hμ : Integrable (squareRadius (I := I)) μ)
    (hmom : HasIdentitySecondMoments μ) (v : I → ℝ) :
    (∫ x, finiteLinearForm v x ^ 2 ∂μ) = squareRadius v := by
  unfold HasIdentitySecondMoments at hmom
  have heq : (fun x => finiteLinearForm v x ^ 2) =
      (fun x => ∑ i, ∑ j, (v i * v j) * (x i * x j)) := by
    funext x
    unfold finiteLinearForm
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, integral_finset_sum _ (fun i _ =>
    integrable_finset_sum _ (fun j _ => (integrable_coordinate_mul_of_squareRadius μ hμ i j).const_mul _))]
  simp_rw [integral_finset_sum _ (fun j _ =>
    (integrable_coordinate_mul_of_squareRadius μ hμ _ j).const_mul _), integral_const_mul, hmom]
  simp [squareRadius, pow_two]

theorem integral_squareRadius_of_identitySecondMoments
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) (hμ : Integrable (squareRadius (I := I)) μ)
    (hmom : HasIdentitySecondMoments μ) :
    (∫ x, squareRadius x ∂μ) = (Fintype.card I : ℝ) := by
  have hi (i : I) : Integrable (fun x : I → ℝ => x i ^ 2) μ := by
    simpa only [pow_two] using integrable_coordinate_mul_of_squareRadius μ hμ i i
  unfold squareRadius
  rw [integral_finset_sum _ (fun i _ => hi i)]
  have hsq (i : I) : (∫ x, x i ^ 2 ∂μ) = 1 := by simpa [pow_two] using hmom i i
  simp_rw [hsq]
  simp

theorem integral_squareRadius_projection_of_identitySecondMoments
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) (hμ : Integrable (squareRadius (I := I)) μ)
    (hmom : HasIdentitySecondMoments μ) (O : Matrix J I ℝ) (hO : O * O.transpose = 1) :
    (∫ x, squareRadius x ∂Measure.map (fun y => O.mulVec y) μ) = (Fintype.card J : ℝ) := by
  rw [integral_map (measurable_finiteMatrixAction O).aemeasurable
    continuous_squareRadius.measurable.aestronglyMeasurable]
  have heq : (fun x => squareRadius (O.mulVec x)) =
      (fun x => ∑ j, finiteLinearForm (O j) x ^ 2) := rfl
  rw [heq]
  have hi (j : J) : Integrable (fun x => finiteLinearForm (O j) x ^ 2) μ := by
    have hf : Integrable (fun x => squareRadius (O.mulVec x)) μ :=
      (integrable_map_measure continuous_squareRadius.measurable.aestronglyMeasurable
        (measurable_finiteMatrixAction O).aemeasurable).mp
        (integrable_squareRadius_matrixImage μ hμ O)
    refine hf.mono' ((continuous_finiteLinearForm (O j)).pow 2).measurable.aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (fun k _ => sq_nonneg (O.mulVec x k)) (Finset.mem_univ j)
  rw [integral_finset_sum _ (fun j _ => hi j)]
  simp_rw [integral_linearForm_sq_of_identitySecondMoments μ hμ hmom]
  have hrow (j : J) : squareRadius (O j) = 1 := by
    have h := congrArg (fun M : Matrix J J ℝ => M j j) hO
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, squareRadius, pow_two] using h
  simp_rw [hrow]
  simp

end GaussianWave.BS
