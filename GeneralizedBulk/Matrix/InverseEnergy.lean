import GeneralizedBulk.Matrix.CovarianceBounds

/-! Uniform inverse-factor energy from the actual lower covariance bound. -/
noncomputable section
open scoped BigOperators Matrix
namespace GeneralizedBulk.Covariance
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem covariance_factor_quadratic (M : Matrix I I ℝ) (x : I → ℝ) :
    dotProduct x ((M * M.transpose) *ᵥ x) = ∑ i, ((M.transpose *ᵥ x) i) ^ 2 := by
  have hh := quadratic_compression (1 : Matrix I I ℝ) M x
  simpa only [Matrix.mul_one, Matrix.one_mulVec, dotProduct, pow_two] using hh

/-- A genuine lower covariance bound controls every actual inverse-factor row. -/
theorem inverse_row_energy_le (M : Matrix I I ℝ) (hM : M.det ≠ 0) (lo : ℝ) (hlo : 0 < lo)
    (hbound : ∀ x : I → ℝ, lo * (∑ i, x i ^ 2) ≤ dotProduct x ((M * M.transpose) *ᵥ x)) (j : I) :
    (∑ i, M⁻¹ j i ^ 2) ≤ 1 / lo := by
  have hm := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM)
  let e : I → ℝ := Pi.single j 1
  have hx : M.transpose *ᵥ (M⁻¹.transpose *ᵥ e) = e := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hm, Matrix.transpose_one, Matrix.one_mulVec]
  have hh := hbound (M⁻¹.transpose *ᵥ e)
  rw [covariance_factor_quadratic, hx] at hh
  have he : (∑ i, e i ^ 2) = 1 := by simp [e, Pi.single_apply]
  rw [he] at hh
  have hrow : (∑ i, ((M⁻¹.transpose *ᵥ e) i) ^ 2) = ∑ i, M⁻¹ j i ^ 2 := by
    simp only [e, Matrix.mulVec_single_one, Matrix.transpose_apply]
  rw [hrow] at hh
  exact (le_div_iff₀ hlo).mpr (by simpa only [mul_comm] using hh)

/-- The true squared Frobenius norm of the inverse factor is at most m/lo.
This applies to any nonsingular factor, including non-symmetric factors. -/
theorem inverse_frobenius_energy_le (M : Matrix I I ℝ) (hM : M.det ≠ 0) (lo : ℝ) (hlo : 0 < lo)
    (hbound : ∀ x : I → ℝ, lo * (∑ i, x i ^ 2) ≤ dotProduct x ((M * M.transpose) *ᵥ x)) :
    (∑ j, ∑ i, M⁻¹ j i ^ 2) ≤ (Fintype.card I : ℝ) / lo := by
  calc
    _ ≤ ∑ _j : I, 1 / lo := Finset.sum_le_sum (fun j _ => inverse_row_energy_le M hM lo hlo hbound j)
    _ = _ := by simp [div_eq_mul_inv]

end GeneralizedBulk.Covariance
