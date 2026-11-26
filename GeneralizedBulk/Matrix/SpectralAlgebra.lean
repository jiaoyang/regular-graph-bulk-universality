import GeneralizedBulk.Matrix.CovarianceBounds

/-! Exact multiplication and inversion in a displayed real orthogonal basis. -/
noncomputable section
open scoped Matrix
namespace GeneralizedBulk.Covariance
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem spectralCovariance_mul (U : Matrix I I ℝ) (hU : U.transpose * U = 1)
    (q r : I → ℝ) :
    spectralCovariance U q * spectralCovariance U r = spectralCovariance U (fun i => q i * r i) := by
  unfold spectralCovariance
  calc
    _ = U * (Matrix.diagonal q * (U.transpose * U) * Matrix.diagonal r) * U.transpose := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one, Matrix.diagonal_mul_diagonal]

theorem spectralCovariance_one (U : Matrix I I ℝ) (hU : U.transpose * U = 1) :
    spectralCovariance U (fun _ => 1) = 1 := by
  simp only [spectralCovariance, Matrix.diagonal_one, Matrix.mul_one,
    Matrix.mul_eq_one_comm.mpr hU]

theorem spectralCovariance_inv (U : Matrix I I ℝ) (hU : U.transpose * U = 1)
    (q : I → ℝ) (hq : ∀ i, q i ≠ 0) :
    (spectralCovariance U q)⁻¹ = spectralCovariance U (fun i => (q i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [spectralCovariance_mul U hU]
  simp only [mul_inv_cancel₀ (hq _)]
  exact spectralCovariance_one U hU

theorem spectralCovariance_sub (U : Matrix I I ℝ) (q r : I → ℝ) :
    spectralCovariance U (q - r) = spectralCovariance U q - spectralCovariance U r := by
  unfold spectralCovariance
  change U * Matrix.diagonal (fun i => q i - r i) * U.transpose = _
  rw [← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem spectralCovariance_smul (U : Matrix I I ℝ) (c : ℝ) (q : I → ℝ) :
    spectralCovariance U (c • q) = c • spectralCovariance U q := by
  unfold spectralCovariance
  rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem spectralCovariance_const (U : Matrix I I ℝ) (hU : U.transpose * U = 1) (c : ℝ) :
    spectralCovariance U (fun _ => c) = c • 1 := by
  have heq : (fun _ : I => c) = c • (fun _ : I => (1 : ℝ)) := by funext i; simp
  rw [heq, spectralCovariance_smul, spectralCovariance_one U hU]

end GeneralizedBulk.Covariance
