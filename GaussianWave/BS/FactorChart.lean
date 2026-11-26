import GaussianWave.BS.GaussianIntrinsicDensity

/-! An actual isometric intrinsic chart from any full-column real factor.
The construction uses the positive square root of the column Gram. -/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

theorem exists_isometric_factor_chart {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (M : Matrix I J ℝ)
    (hdet : (M.transpose * M).det ≠ 0) :
    ∃ O : Matrix J I ℝ, O * O.transpose = 1 ∧ O.transpose * O * M = M := by
  have hP : (M.transpose * M).PosSemidef := by
    simpa only [Matrix.conjTranspose, star_trivial, Matrix.map_id] using
      Matrix.posSemidef_conjTranspose_mul_self M
  let S := hP.sqrt
  have hSS : S*S = M.transpose*M := hP.sqrt_mul_self
  have hSt : S.transpose = S := by
    simpa only [Matrix.conjTranspose, star_trivial, Matrix.map_id] using hP.posSemidef_sqrt.1
  have hSdet : S.det ≠ 0 := by
    intro hzero
    have hh := congrArg Matrix.det hSS
    rw [Matrix.det_mul,hzero,zero_mul] at hh
    exact hdet hh.symm
  have hleft : S⁻¹*S = 1 := Matrix.nonsing_inv_mul S (isUnit_iff_ne_zero.mpr hSdet)
  have hright : S*S⁻¹ = 1 := Matrix.mul_nonsing_inv S (isUnit_iff_ne_zero.mpr hSdet)
  have hSit : (S⁻¹).transpose = S⁻¹ := by
    rw [Matrix.transpose_nonsing_inv,hSt]
  let O : Matrix J I ℝ := S⁻¹ * M.transpose
  have hOt : O.transpose = M * S⁻¹ := by
    dsimp only [O]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose,hSit]
  refine ⟨O, ?_, ?_⟩
  · rw [hOt]
    change (S⁻¹*M.transpose)*(M*S⁻¹) = 1
    calc
      _ = S⁻¹*(M.transpose*M)*S⁻¹ := by simp only [Matrix.mul_assoc]
      _ = S⁻¹*(S*S)*S⁻¹ := by rw [hSS]
      _ = 1 := by rw [← Matrix.mul_assoc S⁻¹ S S,hleft,Matrix.one_mul,hright]
  · rw [hOt]
    change (M*S⁻¹)*(S⁻¹*M.transpose)*M = M
    calc
      _ = M*(S⁻¹*(S⁻¹*(M.transpose*M))) := by simp only [Matrix.mul_assoc]
      _ = M*(S⁻¹*(S⁻¹*(S*S))) := by rw [hSS]
      _ = M := by rw [← Matrix.mul_assoc S⁻¹ S S,hleft,Matrix.one_mul,hleft,Matrix.mul_one]

end GaussianWave.BS
