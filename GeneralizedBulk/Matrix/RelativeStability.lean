import GeneralizedBulk.Matrix.RelativeFactor
import GeneralizedBulk.Matrix.SpectralAlgebra

/-! Inverse and determinant stability for actual finite covariance matrices. -/
noncomputable section
open scoped BigOperators Matrix
namespace GeneralizedBulk.Covariance
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem abs_inv_sub_one_le {x e : ℝ} (he : 0 ≤ e) (he' : e ≤ 1 / 2)
    (hc : |x - 1| ≤ e) : |x⁻¹ - 1| ≤ 2 * e := by
  have hx : 0 < x := by linarith [(abs_le.mp hc).1]
  have hid : x⁻¹ - 1 = (1 - x) / x := by field_simp
  rw [hid, abs_div, abs_of_pos hx, abs_sub_comm]
  apply (div_le_iff₀ hx).mpr
  have hlo : 1 - e ≤ x := by linarith [(abs_le.mp hc).1]
  have hm := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 2 * e)
  nlinarith [mul_nonneg he (sub_nonneg.mpr he')]

/-- The inverse is quantitatively close to identity in its actual action on
every vector, by diagonalizing the original covariance. -/
theorem inverse_coupling_bound (A : Matrix I I ℝ) (hA : A.PosDef)
    (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1 / 2)
    (hc : ∀ x : I → ℝ,
      (1 - e) * (∑ i, x i ^ 2) ≤ dotProduct x (A *ᵥ x) ∧
      dotProduct x (A *ᵥ x) ≤ (1 + e) * (∑ i, x i ^ 2)) (x : I → ℝ) :
    (∑ i, ((A⁻¹ - 1) *ᵥ x) i ^ 2) ≤ (2 * e) ^ 2 * ∑ i, x i ^ 2 := by
  let U : Matrix I I ℝ := hA.isHermitian.eigenvectorUnitary
  have hU : U.transpose * U = 1 := by
    simpa only [U, star, Matrix.conjTranspose_eq_transpose_of_trivial] using
      unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hspec : A = spectralCovariance U hA.isHermitian.eigenvalues := by
    simpa only [spectralCovariance, U, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def,
      RCLike.ofReal_real_eq_id, id_eq] using hA.isHermitian.spectral_theorem
  have hq (i : I) : |(hA.isHermitian.eigenvalues i)⁻¹ - 1| ≤ 2 * e := by
    apply abs_inv_sub_one_le he he'
    have hh := eigenvalue_bounds_of_quadratic A hA.isHermitian (1 - e) (1 + e) hc i
    exact abs_le.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩
  rw [hspec, spectralCovariance_inv U hU _ (fun i => (hA.eigenvalues_pos i).ne'),
    spectralCovariance_sub_one U hU, spectralCovariance_action_sq U hU]
  have hn := transpose_mulVec_sq_sum U (Matrix.mul_eq_one_comm.mpr hU) x
  rw [← hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * e)).mpr (hq i)

/-- The reference factor cancels exactly from a difference of log-determinants. -/
theorem logdet_congruence_difference (M A : Matrix I I ℝ) (hM : M.det ≠ 0)
    (hA : A.PosDef) :
    Real.log (M * A * M.transpose).det - Real.log (M * M.transpose).det = Real.log A.det := by
  simp only [Matrix.det_mul, Matrix.det_transpose]
  rw [Real.log_mul (mul_ne_zero hM hA.det_pos.ne') hM,
    Real.log_mul hM hA.det_pos.ne', Real.log_mul hM hM]
  ring

theorem relative_logdet_stability (M A : Matrix I I ℝ) (hM : M.det ≠ 0)
    (hA : A.PosDef) (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1 / 2)
    (hc : ∀ x : I → ℝ,
      (1 - e) * (∑ i, x i ^ 2) ≤ dotProduct x (A *ᵥ x) ∧
      dotProduct x (A *ᵥ x) ≤ (1 + e) * (∑ i, x i ^ 2)) :
    |Real.log (M * A * M.transpose).det - Real.log (M * M.transpose).det| ≤
      2 * Fintype.card I * e := by
  rw [logdet_congruence_difference M A hM hA]
  exact logdet_stability_of_quadratic A hA e he he' hc

end GeneralizedBulk.Covariance
