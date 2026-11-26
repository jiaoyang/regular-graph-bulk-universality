import GeneralizedBulk.Matrix.CovarianceDeterminant

/-! Finite covariance bounds are preserved by orthonormal compression. -/
noncomputable section
open scoped BigOperators Matrix
namespace GeneralizedBulk.Covariance
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem transpose_mulVec_sq_sum (B : Matrix J I ℝ) (hB : B * B.transpose = 1) (x : J → ℝ) :
    (∑ i, ((B.transpose *ᵥ x) i) ^ 2) = ∑ j, x j ^ 2 := by
  simp only [pow_two]
  change dotProduct (B.transpose *ᵥ x) (B.transpose *ᵥ x) = dotProduct x x
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.transpose_transpose,
    hB, Matrix.vecMul_one]

theorem quadratic_compression (A : Matrix I I ℝ) (B : Matrix J I ℝ) (x : J → ℝ) :
    dotProduct x ((B * A * B.transpose) *ᵥ x) =
      dotProduct (B.transpose *ᵥ x) (A *ᵥ (B.transpose *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose]

theorem spectralCovariance_quadratic (U : Matrix I I ℝ) (q : I → ℝ) (x : I → ℝ) :
    dotProduct x (spectralCovariance U q *ᵥ x) =
      ∑ i, q i * ((U.transpose *ᵥ x) i) ^ 2 := by
  rw [spectralCovariance, quadratic_compression]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem spectralCovariance_quadratic_bounds (U : Matrix I I ℝ) (hU : U.transpose * U = 1)
    (q : I → ℝ) (lo hi : ℝ) (hq : ∀ i, lo ≤ q i ∧ q i ≤ hi) (x : I → ℝ) :
    lo * (∑ i, x i ^ 2) ≤ dotProduct x (spectralCovariance U q *ᵥ x) ∧
    dotProduct x (spectralCovariance U q *ᵥ x) ≤ hi * (∑ i, x i ^ 2) := by
  have hn := transpose_mulVec_sq_sum U (Matrix.mul_eq_one_comm.mpr hU) x
  rw [spectralCovariance_quadratic, ← hn]
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hq i).1 (sq_nonneg _))
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hq i).2 (sq_nonneg _))

/-- Every orthonormal compression inherits the same lower and upper covariance
bounds; in particular this applies to coordinate restrictions. -/
theorem compression_quadratic_bounds (A : Matrix I I ℝ) (B : Matrix J I ℝ)
    (hB : B * B.transpose = 1) (lo hi : ℝ)
    (hA : ∀ x : I → ℝ,
      lo * (∑ i, x i ^ 2) ≤ dotProduct x (A *ᵥ x) ∧
      dotProduct x (A *ᵥ x) ≤ hi * (∑ i, x i ^ 2)) (x : J → ℝ) :
    lo * (∑ j, x j ^ 2) ≤ dotProduct x ((B * A * B.transpose) *ᵥ x) ∧
    dotProduct x ((B * A * B.transpose) *ᵥ x) ≤ hi * (∑ j, x j ^ 2) := by
  rw [quadratic_compression]
  simpa only [transpose_mulVec_sq_sum B hB x] using hA (B.transpose *ᵥ x)

/-- A positive lower quadratic bound proves strict positivity of the actual
symmetric covariance; no eigenvalue premise is needed. -/
theorem posDef_of_quadratic_lower (A : Matrix I I ℝ) (hA : A.IsHermitian)
    (lo : ℝ) (hlo : 0 < lo)
    (hbound : ∀ x : I → ℝ, lo * (∑ i, x i ^ 2) ≤ dotProduct x (A *ᵥ x)) : A.PosDef := by
  refine ⟨hA, fun x hx => ?_⟩
  have hn : 0 < ∑ i, x i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Finset.sum_pos' (fun j _ => sq_nonneg (x j)) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  simpa only [star_trivial] using (mul_pos hlo hn).trans_le (hbound x)

end GeneralizedBulk.Covariance
