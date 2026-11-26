import GeneralizedBulk.Exterior.Rotation
import GeneralizedBulk.Gaussian.Invariant

/-!
# Actual Gaussian invariance under the ordinary exterior rotation

This connects the constructed trigonometric matrix to the constructed real
Gaussian endpoint law; no Gaussian rotation-invariance assumption is used.
-/
noncomputable section
namespace GeneralizedBulk.Exterior

/-- The real ordinary rotation before switching conjugation. -/
def realOrdinaryRotation (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![Real.cos t, 0, 0, -Real.sin t;
     0, Real.cos t, -Real.sin t, 0;
     0, Real.sin t, Real.cos t, 0;
     Real.sin t, 0, 0, Real.cos t]

private theorem real_identity_eq : (1 : Matrix (Fin 4) (Fin 4) ℝ) =
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem realOrdinaryRotation_complex (t : ℝ) :
    (realOrdinaryRotation t).map Complex.ofReal = ordinaryRotation t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realOrdinaryRotation, ordinaryRotation, rotation,
      GeneralizedSwitching.endpointPermutation, Matrix.mul_apply, Fin.sum_univ_succ,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem realOrdinaryRotation_mul_transpose (t : ℝ) :
    realOrdinaryRotation t * (realOrdinaryRotation t).transpose = 1 := by
  rw [real_identity_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realOrdinaryRotation, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals nlinarith [Real.sin_sq_add_cos_sq t]

theorem realOrdinaryRotation_commutes_edge (t : ℝ) :
    realOrdinaryRotation t * GeneralizedSwitching.edgeMatrix =
      GeneralizedSwitching.edgeMatrix * realOrdinaryRotation t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realOrdinaryRotation, GeneralizedSwitching.edgeMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem realOrdinaryRotation_preserves_covariance (t p : ℝ) :
    realOrdinaryRotation t * covarianceMatrix p * (realOrdinaryRotation t).transpose = covarianceMatrix p := by
  simp only [covarianceMatrix, Matrix.mul_add, Matrix.add_mul, mul_one, Matrix.mul_smul,
    Matrix.smul_mul, realOrdinaryRotation_mul_transpose]
  rw [realOrdinaryRotation_commutes_edge]
  simp only [Matrix.mul_assoc, realOrdinaryRotation_mul_transpose, mul_one]

/-- The actual finite Gaussian mark law is invariant under the ordinary
rotation used by the exterior flow. -/
theorem gaussianMark_rotation_invariant (p : ℝ) (hp : |p| < 1) (t : ℝ) :
    MeasureTheory.Measure.map (fun y => (realOrdinaryRotation t).mulVec y)
      (Gaussian.markLaw p) = Gaussian.markLaw p := by
  exact Gaussian.markLaw_matrixAction_invariant p hp (realOrdinaryRotation t)
    (realOrdinaryRotation_preserves_covariance t p)

/-- Every independent endpoint mark is rotated simultaneously, preserving the
actual infinite Gaussian product measure. -/
theorem gaussianMarks_rotation_measurePreserving (p : ℝ) (hp : |p| < 1) (t : ℝ) (I : Type*) :
    MeasureTheory.MeasurePreserving
      (Gaussian.coordinateAction (fun y => (realOrdinaryRotation t).mulVec y) (I := I))
      (Gaussian.iidLaw (Gaussian.markLaw p) I) (Gaussian.iidLaw (Gaussian.markLaw p) I) :=
  Gaussian.markFamily_matrixAction_measurePreserving p hp (realOrdinaryRotation t)
    (realOrdinaryRotation_preserves_covariance t p) I

end GeneralizedBulk.Exterior
