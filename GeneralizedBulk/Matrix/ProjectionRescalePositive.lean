import GeneralizedBulk.Matrix.ProjectionRescale

/-! Actual normal rescaling preserves strict covariance positivity. -/
noncomputable section
namespace GeneralizedBulk.Covariance
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem projectionRescale_transpose (P : Matrix I I ℝ) (hP : P.transpose=P) (t : ℝ) :
    (projectionRescale P t).transpose=projectionRescale P t := by
  simp only [projectionRescale, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, hP]

theorem projectionRescale_congruence_posDef (P Q : Matrix I I ℝ)
    (hP : P*P=P) (hPt : P.transpose=P) (hQ : Q.PosDef) (t : ℝ) (ht : t ≠ 0) :
    (projectionRescale P t * Q * projectionRescale P t).PosDef := by
  have hu : IsUnit (projectionRescale P t) :=
    ⟨⟨projectionRescale P t, projectionRescale P t⁻¹,
      projectionRescale_inverse P hP t ht,
      by rw [projectionRescale_mul P hP, inv_mul_cancel₀ ht, projectionRescale_one]⟩,rfl⟩
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, projectionRescale_transpose P hPt t] using
    hQ.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hu)

end GeneralizedBulk.Covariance
