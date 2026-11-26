import GeneralizedBulk.Matrix.RelativeNormalization

/-! Inverse-factor and determinant bounds for the actual common-Gaussian
relative covariance coupling. -/
noncomputable section
open scoped BigOperators Matrix
namespace GeneralizedBulk.Covariance
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem identityFactor_det_ne_zero (A : Matrix I I ℝ) (hA : A.PosDef) :
    (identityFactor A hA).det ≠ 0 := by
  have hh := hA.det_pos
  rw [← identityFactor_covariance A hA, Matrix.det_mul, Matrix.det_transpose] at hh
  intro hz
  simp only [hz, zero_mul, lt_self_iff_false] at hh

/-- The inverse of the actual positive square root is close to identity.
This is the factor-inverse estimate needed by the Gaussian mixture coupling. -/
theorem identityFactor_inv_coupling_bound (A : Matrix I I ℝ) (hA : A.PosDef)
    (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1 / 2)
    (hc : ∀ x : I → ℝ,
      (1 - e) * (∑ i, x i ^ 2) ≤ dotProduct x (A *ᵥ x) ∧
      dotProduct x (A *ᵥ x) ≤ (1 + e) * (∑ i, x i ^ 2)) (x : I → ℝ) :
    (∑ i, (((identityFactor A hA)⁻¹ - 1) *ᵥ x) i ^ 2) ≤ (2 * e) ^ 2 * ∑ i, x i ^ 2 := by
  let U : Matrix I I ℝ := hA.isHermitian.eigenvectorUnitary
  have hU : U.transpose * U = 1 := by
    simpa only [U, star, Matrix.conjTranspose_eq_transpose_of_trivial] using
      unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hS : identityFactor A hA = spectralCovariance U (fun i => Real.sqrt (hA.isHermitian.eigenvalues i)) := by
    simp only [identityFactor, Matrix.PosSemidef.sqrt, spectralCovariance, U,
      Function.comp_apply, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hq (i : I) : |(Real.sqrt (hA.isHermitian.eigenvalues i))⁻¹ - 1| ≤ 2 * e := by
    apply abs_inv_sub_one_le he he'
    apply abs_sqrt_sub_one_le (hA.eigenvalues_pos i).le he (by linarith)
    have hh := eigenvalue_bounds_of_quadratic A hA.isHermitian (1 - e) (1 + e) hc i
    exact abs_le.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩
  rw [hS, spectralCovariance_inv U hU _ (fun i => (Real.sqrt_pos.mpr (hA.eigenvalues_pos i)).ne'),
    spectralCovariance_sub_one U hU, spectralCovariance_action_sq U hU]
  have hn := transpose_mulVec_sq_sum U (Matrix.mul_eq_one_comm.mpr hU) x
  rw [← hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * e)).mpr (hq i)

/-- The literal inverse-factor coupling for a general reference factor. -/
theorem referenceFactor_inv_coupling_bound (M A : Matrix I I ℝ) (hA : A.PosDef)
    (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1 / 2)
    (hc : ∀ x : I → ℝ,
      (1 - e) * (∑ i, x i ^ 2) ≤ dotProduct x (A *ᵥ x) ∧
      dotProduct x (A *ᵥ x) ≤ (1 + e) * (∑ i, x i ^ 2)) (x : I → ℝ) :
    (∑ i, (((referenceFactor M A hA)⁻¹ - M⁻¹) *ᵥ x) i ^ 2) ≤
      (2 * e) ^ 2 * (∑ i, ∑ j, M⁻¹ i j ^ 2) * ∑ i, x i ^ 2 := by
  have hid : (referenceFactor M A hA)⁻¹ - M⁻¹ = ((identityFactor A hA)⁻¹ - 1) * M⁻¹ := by
    rw [referenceFactor, Matrix.mul_inv_rev, Matrix.sub_mul, Matrix.one_mul]
  rw [hid, ← Matrix.mulVec_mulVec]
  calc
    _ ≤ (2 * e) ^ 2 * ∑ i, (M⁻¹ *ᵥ x) i ^ 2 := identityFactor_inv_coupling_bound A hA e he he' hc _
    _ ≤ (2 * e) ^ 2 * ((∑ i, ∑ j, M⁻¹ i j ^ 2) * ∑ i, x i ^ 2) :=
      mul_le_mul_of_nonneg_left (matrix_action_sq_le_frobenius M⁻¹ x) (sq_nonneg _)
    _ = _ := by ring

/-- The true factor is nonsingular whenever the reference is. -/
theorem referenceFactor_det_ne_zero (M A : Matrix I I ℝ) (hM : M.det ≠ 0) (hA : A.PosDef) :
    (referenceFactor M A hA).det ≠ 0 := by
  rw [referenceFactor, Matrix.det_mul]
  exact mul_ne_zero hM (identityFactor_det_ne_zero A hA)

/-- A factor log-determinant difference is half the relative covariance
log-determinant, with the actual signs handled by absolute determinants. -/
theorem referenceFactor_logabsdet_difference (M A : Matrix I I ℝ) (hM : M.det ≠ 0) (hA : A.PosDef) :
    Real.log |(referenceFactor M A hA).det| - Real.log |M.det| = Real.log A.det / 2 := by
  have hs := identityFactor_det_ne_zero A hA
  have hc := congrArg (fun B : Matrix I I ℝ => Real.log B.det) (identityFactor_covariance A hA)
  change Real.log ((identityFactor A hA * (identityFactor A hA).transpose).det) = Real.log A.det at hc
  rw [Matrix.det_mul, Matrix.det_transpose, Real.log_mul hs hs] at hc
  rw [referenceFactor, Matrix.det_mul, abs_mul, Real.log_mul (abs_ne_zero.mpr hM) (abs_ne_zero.mpr hs)]
  simp only [Real.log_abs]
  linarith

/-- Relative quadratic error controls the actual factor log-determinant. -/
theorem referenceFactor_logabsdet_bound (M A : Matrix I I ℝ) (hM : M.det ≠ 0) (hA : A.PosDef)
    (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1 / 2)
    (hc : ∀ x : I → ℝ,
      (1 - e) * (∑ i, x i ^ 2) ≤ dotProduct x (A *ᵥ x) ∧
      dotProduct x (A *ᵥ x) ≤ (1 + e) * (∑ i, x i ^ 2)) :
    |Real.log (|(referenceFactor M A hA).det|) - Real.log (|M.det|)| ≤ Fintype.card I * e := by
  rw [referenceFactor_logabsdet_difference M A hM hA, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  convert logdet_stability_of_quadratic A hA e he he' hc using 1 <;> ring

end GeneralizedBulk.Covariance
