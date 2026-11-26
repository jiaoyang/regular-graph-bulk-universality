import Mathlib

/-! An invertible rescaling of a normal projection, with its exact covariance decomposition. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Covariance
variable {I : Type*} [Fintype I] [DecidableEq I]

def projectionRescale (P : Matrix I I ℝ) (t : ℝ) : Matrix I I ℝ := 1 + (t-1) • P

theorem projectionRescale_mul (P : Matrix I I ℝ) (hP : P*P=P) (t u : ℝ) :
    projectionRescale P t * projectionRescale P u = projectionRescale P (t*u) := by
  unfold projectionRescale
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem projectionRescale_one (P : Matrix I I ℝ) : projectionRescale P 1 = 1 := by simp [projectionRescale]

theorem projectionRescale_inverse (P : Matrix I I ℝ) (hP : P*P=P) (t : ℝ) (ht : t ≠ 0) :
    projectionRescale P t * projectionRescale P t⁻¹ = 1 := by
  rw [projectionRescale_mul P hP, mul_inv_cancel₀ ht, projectionRescale_one]

theorem projectionRescale_det_ne_zero (P : Matrix I I ℝ) (hP : P*P=P) (t : ℝ) (ht : t ≠ 0) :
    (projectionRescale P t).det ≠ 0 := by
  have hh := congrArg Matrix.det (projectionRescale_inverse P hP t ht)
  rw [Matrix.det_mul, Matrix.det_one] at hh
  exact left_ne_zero_of_mul_eq_one hh

theorem projectionRescale_split (P : Matrix I I ℝ) (t : ℝ) :
    projectionRescale P t = (1-P) + t • P := by
  ext i j
  simp only [projectionRescale, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem projectionRescale_covariance_decomposition (P Q : Matrix I I ℝ) (t : ℝ) :
    projectionRescale P t * Q * projectionRescale P t =
      (1-P)*Q*(1-P) + t • ((1-P)*Q*P + P*Q*(1-P)) + t^2 • (P*Q*P) := by
  rw [projectionRescale_split]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem tangent_covariance_identity (P Sigma : Matrix I I ℝ) (hleft : P*Sigma=0) (hright : Sigma*P=0) :
    (1-P)*Sigma*(1-P)=Sigma := by
  rw [Matrix.sub_mul, Matrix.one_mul, hleft, sub_zero, Matrix.mul_sub, Matrix.mul_one, hright, sub_zero]

theorem projectionRescale_covariance_error (P Q Sigma E : Matrix I I ℝ) (t q : ℝ)
    (hleft : P*Sigma=0) (hright : Sigma*P=0) (hNormal : P*Q*P=q • P+E) (htq : t^2*q=1) :
    projectionRescale P t * Q * projectionRescale P t - (Sigma+P) =
      (1-P)*(Q-Sigma)*(1-P) + t • ((1-P)*Q*P + P*Q*(1-P)) + t^2 • E := by
  rw [projectionRescale_covariance_decomposition, hNormal]
  have htan : (1-P)*(Q-Sigma)*(1-P) = (1-P)*Q*(1-P)-Sigma := by
    rw [Matrix.mul_sub (1-P) Q Sigma, Matrix.sub_mul ((1-P)*Q) ((1-P)*Sigma) (1-P),
      tangent_covariance_identity P Sigma hleft hright]
  rw [htan]
  simp only [smul_add, smul_smul, htq, one_smul]
  abel

def unitNormalProjection (n : I → ℝ) : Matrix I I ℝ := fun i j => n i * n j

theorem unitNormalProjection_idempotent (n : I → ℝ) (hn : ∑ i, n i ^ 2 = 1) :
    unitNormalProjection n * unitNormalProjection n = unitNormalProjection n := by
  ext i j
  simp only [Matrix.mul_apply, unitNormalProjection]
  calc
    _ = n i * (∑ k, n k ^ 2) * n j := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = _ := by rw [hn]; ring

theorem projectionRescale_unitNormal_det (n : I → ℝ) (hn : ∑ i, n i ^ 2 = 1) (t : ℝ) :
    (projectionRescale (unitNormalProjection n) t).det=t := by
  have he : projectionRescale (unitNormalProjection n) t = 1 +
      Matrix.replicateCol Unit n * Matrix.replicateRow Unit (fun i => (t-1)*n i) := by
    ext i j
    simp only [projectionRescale, unitNormalProjection, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply,
      Fintype.sum_unique]
    ring
  rw [he, Matrix.det_one_add_replicateCol_mul_replicateRow]
  change 1 + (∑ i, ((t-1)*n i)*n i) = t
  have hh : (∑ i, ((t-1)*n i)*n i) = (t-1) * ∑ i, n i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hh, hn]
  ring

end GeneralizedBulk.Covariance
