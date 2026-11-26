import GeneralizedBulk.Matrix.CoordinateCompression

/-! Positive definiteness passes to actual injective coordinate restrictions. -/
noncomputable section
namespace GeneralizedBulk.Covariance
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem posDef_submatrix_of_injective (Q : Matrix I I ℝ) (hQ : Q.PosDef)
    (e : J → I) (he : Function.Injective e) : (Q.submatrix e e).PosDef := by
  have hinj : Function.Injective (fun x : J → ℝ => Matrix.vecMul x (coordinateSelection e)) := by
    intro x y h
    have hh := congrArg (fun z => Matrix.vecMul z (coordinateSelection e).transpose) h
    simpa only [Matrix.vecMul_vecMul,coordinateSelection_orthonormal e he,Matrix.vecMul_one] using hh
  have hh := hQ.mul_mul_conjTranspose_same hinj
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,coordinateSelection_congruence] using hh

end GeneralizedBulk.Covariance
