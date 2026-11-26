import GeneralizedBulk.Matrix.ProjectionRescale

/-! Exact covariance formulas for a literal rank-one normal projection. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Covariance
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem quadratic_smul (Q : Matrix I I ℝ) (r : ℝ) (x : I → ℝ) :
    dotProduct (r • x) (Q.mulVec (r • x)) = r ^ 2 * dotProduct x (Q.mulVec x) := by
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem unitNormalProjection_mul_entry (n : I → ℝ) (Q : Matrix I I ℝ) (i j : I) :
    (unitNormalProjection n * Q) i j = n i * ∑ k, n k * Q k j := by
  simp only [Matrix.mul_apply, unitNormalProjection, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem unitNormalProjection_covariance (n : I → ℝ) (Q : Matrix I I ℝ) :
    unitNormalProjection n * Q * unitNormalProjection n =
      dotProduct n (Q.mulVec n) • unitNormalProjection n := by
  ext i j
  simp only [Matrix.mul_apply, unitNormalProjection, Matrix.smul_apply, smul_eq_mul,
    dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem unitNormalProjection_mulVec (n x : I → ℝ) :
    (unitNormalProjection n).mulVec x = (∑ i, n i * x i) • n := by
  funext i
  simp only [Matrix.mulVec, dotProduct, unitNormalProjection, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem projectionRescale_fix (P : Matrix I I ℝ) (t : ℝ) (x : I → ℝ) (hx : P.mulVec x=0) :
    (projectionRescale P t).mulVec x=x := by
  rw [projectionRescale, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc, hx, smul_zero, add_zero]

end GeneralizedBulk.Covariance
