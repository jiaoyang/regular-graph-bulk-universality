import GeneralizedBulk.MatrixGeometry

/-!
# Nondegeneracy of the real Gaussian endpoint covariance

The proof uses an explicit sum-of-squares decomposition of `xᵀ C x`.
These results contain no probabilistic or asymptotic assumptions.
-/

namespace GeneralizedBulk

open scoped BigOperators

/-- The Gaussian endpoint covariance is genuinely positive definite. -/
theorem covarianceMatrix_posDef (p : ℝ) (hp : |p| < 1) : (covarianceMatrix p).PosDef := by
  constructor
  · rw [covarianceMatrix_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply]
  · intro x hx
    have hp2 : 0 < 1 - p ^ 2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one p).2 hp)
    have hform : dotProduct (star x) (Matrix.mulVec (covarianceMatrix p) x) =
        (x 0 + p * x 1) ^ 2 + (1 - p ^ 2) * (x 1) ^ 2 +
        (x 2 + p * x 3) ^ 2 + (1 - p ^ 2) * (x 3) ^ 2 := by
      rw [covarianceMatrix_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
      ring
    rw [hform]
    have h0 := sq_nonneg (x 0 + p * x 1)
    have h1 := mul_nonneg hp2.le (sq_nonneg (x 1))
    have h2 := sq_nonneg (x 2 + p * x 3)
    have h3 := mul_nonneg hp2.le (sq_nonneg (x 3))
    by_contra hnot
    have hq : (x 0 + p * x 1) ^ 2 + (1 - p ^ 2) * (x 1) ^ 2 +
        (x 2 + p * x 3) ^ 2 + (1 - p ^ 2) * (x 3) ^ 2 ≤ 0 := le_of_not_gt hnot
    have hx1 : x 1 = 0 := by
      by_contra h
      have hs := mul_pos hp2 (sq_pos_of_ne_zero h)
      linarith
    have hx3 : x 3 = 0 := by
      by_contra h
      have hs := mul_pos hp2 (sq_pos_of_ne_zero h)
      linarith
    have hx0 : x 0 = 0 := by
      rw [hx1, hx3] at hq
      nlinarith [sq_nonneg (x 2)]
    have hx2 : x 2 = 0 := by
      rw [hx1, hx3] at hq
      nlinarith [sq_nonneg (x 0)]
    apply hx
    ext i
    fin_cases i <;> assumption

/-- Positive determinant, needed for a nondegenerate Gaussian density. -/
theorem covarianceMatrix_det_pos (p : ℝ) (hp : |p| < 1) :
    0 < Matrix.det (covarianceMatrix p) :=
  (covarianceMatrix_posDef p hp).det_pos

/-- Invertibility follows from positive definiteness, with no extra premise. -/
theorem covarianceMatrix_isUnit (p : ℝ) (hp : |p| < 1) :
    IsUnit (covarianceMatrix p) :=
  (covarianceMatrix_posDef p hp).isUnit

/-- The endpoint reversal is an orthogonal real permutation. -/
theorem endpointPermutation_transpose_mul :
    (GeneralizedSwitching.endpointPermutation : Matrix (Fin 4) (Fin 4) ℝ).transpose *
        GeneralizedSwitching.endpointPermutation = 1 := by
  rw [endpointPermutation_transpose, endpointPermutation_sq]

/-- The other orthogonality identity for endpoint reversal. -/
theorem endpointPermutation_mul_transpose :
    (GeneralizedSwitching.endpointPermutation : Matrix (Fin 4) (Fin 4) ℝ) *
        GeneralizedSwitching.endpointPermutation.transpose = 1 := by
  rw [endpointPermutation_transpose, endpointPermutation_sq]

end GeneralizedBulk
