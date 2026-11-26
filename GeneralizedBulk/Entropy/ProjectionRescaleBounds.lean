import GeneralizedBulk.Entropy.MatrixEntryAlgebra
import GeneralizedBulk.Entropy.GaussianMixtureEntropyCoupling
import GeneralizedBulk.Matrix.ProjectionRescale

/-! Quantitative covariance control after the actual normal rescaling. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Covariance GeneralizedBulk.Entropy.Mehler
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem matrixEntryL1_unitNormalProjection (n : I → ℝ) :
    matrixEntryL1 (unitNormalProjection n) = coordinateL1 n ^ 2 := by
  unfold matrixEntryL1 unitNormalProjection coordinateL1
  simp only [abs_mul, pow_two, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem matrixEntryL1_unitNormalProjection_le (n : I → ℝ) (hn : ∑ i, n i ^ 2 = 1) :
    matrixEntryL1 (unitNormalProjection n) ≤ Fintype.card I := by
  rw [matrixEntryL1_unitNormalProjection]
  simpa only [hn, mul_one] using coordinateL1_sq_le_dimension_energy n

theorem matrixEntryL1_tangentProjection_le (n : I → ℝ) (hn : ∑ i, n i ^ 2 = 1) :
    matrixEntryL1 (1-unitNormalProjection n) ≤ 2 * Fintype.card I := by
  have hh := (matrixEntryL1_sub_le (1 : Matrix I I ℝ) (unitNormalProjection n)).trans
    (add_le_add_left (matrixEntryL1_unitNormalProjection_le n hn) (matrixEntryL1 (1 : Matrix I I ℝ)))
  rw [matrixEntryL1_one] at hh
  linarith

theorem projectionRescale_covariance_error_bound (P Q Sigma E : Matrix I I ℝ) (t q : ℝ)
    (hleft : P*Sigma=0) (hright : Sigma*P=0) (hNormal : P*Q*P=q • P+E) (htq : t^2*q=1) :
    matrixEntryL1 (projectionRescale P t * Q * projectionRescale P t - (Sigma+P)) ≤
      matrixEntryL1 (1-P) ^ 2 * matrixEntryL1 (Q-Sigma) +
        |t| * (matrixEntryL1 ((1-P)*Q*P) + matrixEntryL1 (P*Q*(1-P))) + t ^ 2 * matrixEntryL1 E := by
  rw [projectionRescale_covariance_error P Q Sigma E t q hleft hright hNormal htq]
  refine ((matrixEntryL1_add_le _ _).trans (add_le_add_right (matrixEntryL1_add_le _ _) _)).trans ?_
  rw [matrixEntryL1_smul, matrixEntryL1_smul, abs_of_nonneg (sq_nonneg t)]
  have htan := (matrixEntryL1_mul_le ((1-P)*(Q-Sigma)) (1-P)).trans
    (mul_le_mul_of_nonneg_right (matrixEntryL1_mul_le (1-P) (Q-Sigma)) (matrixEntryL1_nonneg _))
  have hcross := mul_le_mul_of_nonneg_left
    (matrixEntryL1_add_le ((1-P)*Q*P) (P*Q*(1-P))) (abs_nonneg t)
  nlinarith

theorem projectionRescale_covariance_entry_bound (P Q Sigma E : Matrix I I ℝ) (t q : ℝ)
    (hleft : P*Sigma=0) (hright : Sigma*P=0) (hNormal : P*Q*P=q • P+E) (htq : t^2*q=1)
    (i j : I) :
    |(projectionRescale P t * Q * projectionRescale P t - (Sigma+P)) i j| ≤
      matrixEntryL1 (1-P) ^ 2 * matrixEntryL1 (Q-Sigma) +
        |t| * (matrixEntryL1 ((1-P)*Q*P) + matrixEntryL1 (P*Q*(1-P))) + t ^ 2 * matrixEntryL1 E :=
  (abs_matrix_entry_le_matrixEntryL1 _ i j).trans
    (projectionRescale_covariance_error_bound P Q Sigma E t q hleft hright hNormal htq)


theorem projection_cross_matrixEntryL1_bound (P Q : Matrix I I ℝ)
    (hP : P.transpose=P) (hQ : Q.transpose=Q) :
    matrixEntryL1 ((1-P)*Q*P)+matrixEntryL1 (P*Q*(1-P)) ≤
      2*matrixEntryL1 (1-P)*matrixEntryL1 (P*Q) := by
  have ht : Q*P=(P*Q).transpose := by rw [Matrix.transpose_mul,hP,hQ]
  have h1 := matrixEntryL1_mul_le (1-P) (Q*P)
  rw [← Matrix.mul_assoc,ht,matrixEntryL1_transpose] at h1
  have h2 := matrixEntryL1_mul_le (P*Q) (1-P)
  nlinarith

end GeneralizedBulk.Entropy
