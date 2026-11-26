import GeneralizedBulk.Matrix.CovarianceBounds

/-! Actual coordinate restrictions and their covariance lower bounds. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Covariance
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def coordinateSelection (e : J → I) : Matrix J I ℝ := (1 : Matrix I I ℝ).submatrix e id

@[simp] theorem coordinateSelection_mulVec (e : J → I) (x : I → ℝ) :
    (coordinateSelection e).mulVec x = x ∘ e := by
  funext j
  simp [coordinateSelection, Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem coordinateSelection_orthonormal (e : J → I) (he : Function.Injective e) :
    coordinateSelection e * (coordinateSelection e).transpose = 1 := by
  ext i j
  simp [coordinateSelection, Matrix.mul_apply, Matrix.one_apply, he.eq_iff]

theorem coordinateSelection_congruence (Q : Matrix I I ℝ) (e : J → I) :
    coordinateSelection e * Q * (coordinateSelection e).transpose = Q.submatrix e e := by
  ext i j
  simp [coordinateSelection, Matrix.mul_apply, Matrix.one_apply]

theorem coordinate_compression_bounds (Q : Matrix I I ℝ) (e : J → I) (he : Function.Injective e)
    (lo hi : ℝ) (hQ : ∀ x : I → ℝ,
      lo * (∑ i, x i ^ 2) ≤ dotProduct x (Q.mulVec x) ∧
      dotProduct x (Q.mulVec x) ≤ hi * (∑ i, x i ^ 2)) (x : J → ℝ) :
    lo * (∑ j, x j ^ 2) ≤ dotProduct x ((Q.submatrix e e).mulVec x) ∧
      dotProduct x ((Q.submatrix e e).mulVec x) ≤ hi * (∑ j, x j ^ 2) := by
  rw [← coordinateSelection_congruence Q e]
  exact compression_quadratic_bounds Q _ (coordinateSelection_orthonormal e he) lo hi hQ x

theorem coordinate_compression_posDef (Q : Matrix I I ℝ) (hQ : Q.IsHermitian)
    (e : J → I) (he : Function.Injective e) (lo : ℝ) (hlo : 0 < lo)
    (hbound : ∀ x : I → ℝ, lo * (∑ i, x i ^ 2) ≤ dotProduct x (Q.mulVec x)) :
    (Q.submatrix e e).PosDef := by
  refine posDef_of_quadratic_lower _ (hQ.submatrix e) lo hlo ?_
  intro x
  rw [← coordinateSelection_congruence Q e, quadratic_compression]
  simpa only [transpose_mulVec_sq_sum _ (coordinateSelection_orthonormal e he) x] using
    hbound ((coordinateSelection e).transpose.mulVec x)

end GeneralizedBulk.Covariance
