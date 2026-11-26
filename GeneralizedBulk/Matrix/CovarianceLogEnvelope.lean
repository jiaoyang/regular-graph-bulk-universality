import GeneralizedBulk.Entropy.CovarianceFactorUniformBounds

/-! A genuine covariance floor and trace bound control the absolute
logarithmic determinant of every covariance factor. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Covariance
open GeneralizedBulk.Entropy
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem covariance_factor_logabsdet_le (M : Matrix I I ℝ) (hM : M.det ≠ 0)
    (kappa U : ℝ) (hkappa : 0 < kappa) (hU : 0 < U)
    (hfloor : ∀ x : I → ℝ,kappa*(∑ i,x i^2) ≤ dotProduct x ((M*M.transpose).mulVec x))
    (htrace : Matrix.trace (M*M.transpose) ≤ U) :
    |Real.log (|M.det|)| ≤ (Fintype.card I : ℝ)/2*(|Real.log kappa|+|Real.log U|) := by
  have hherm : (M*M.transpose).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.isHermitian_mul_conjTranspose_self M
  have hpos := posDef_of_quadratic_lower _ hherm kappa hkappa hfloor
  have hu (x : I → ℝ) : dotProduct x ((M*M.transpose).mulVec x) ≤ U*(∑ i,x i^2) := by
    rw [covariance_factor_quadratic]
    have hh := matrix_action_sq_le_frobenius M.transpose x
    change (∑ i,M.transpose.mulVec x i^2) ≤ matrixSquareEnergy M.transpose*(∑ i,x i^2) at hh
    rw [matrixSquareEnergy_transpose,matrixSquareEnergy_eq_covariance_trace] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right htrace (Finset.sum_nonneg (fun i _ => sq_nonneg _)))
  have heig (i : I) := eigenvalue_bounds_of_quadratic _ hherm kappa U (fun x => ⟨hfloor x,hu x⟩) i
  have hl (i : I) : |Real.log (hherm.eigenvalues i)| ≤ |Real.log kappa|+|Real.log U| := by
    have hlo := Real.log_le_log hkappa (heig i).1
    have hhi := Real.log_le_log (hpos.eigenvalues_pos i) (heig i).2
    exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log kappa),abs_nonneg (Real.log U)],
      by linarith [le_abs_self (Real.log U),abs_nonneg (Real.log kappa)]⟩
  have hh : |Real.log (M*M.transpose).det| ≤ (Fintype.card I : ℝ)*(|Real.log kappa|+|Real.log U|) := by
    rw [posDef_logdet _ hpos]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hl i))
  rw [Matrix.det_mul,Matrix.det_transpose,Real.log_mul hM hM,← Real.log_abs M.det,
    ← two_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  linarith

end GeneralizedBulk.Covariance
