import GeneralizedBulk.Entropy.ConstructedCovarianceStability
import GeneralizedBulk.Matrix.InverseEnergy

/-! Reference covariance floors and trace bounds control every constructed entropy constant. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Covariance
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem matrixSquareEnergy_transpose (M : Matrix I I ℝ) : matrixSquareEnergy M.transpose=matrixSquareEnergy M :=
  Finset.sum_comm

theorem matrixSquareEnergy_eq_covariance_trace (M : Matrix I I ℝ) :
    matrixSquareEnergy M=Matrix.trace (M*M.transpose) := by
  simp only [matrixSquareEnergy, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]

theorem matrixEntryL1_le_of_squareEnergy (M : Matrix I I ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hbound : matrixSquareEnergy M ≤ U) : matrixEntryL1 M ≤ (Fintype.card I : ℝ)^2*Real.sqrt U := by
  apply matrixEntryL1_le_of_action_energy M (Real.sqrt U) (Real.sqrt_nonneg U)
  intro x
  rw [Real.sq_sqrt hU]
  exact (matrix_action_sq_le_frobenius M x).trans
    (mul_le_mul_of_nonneg_right hbound (Finset.sum_nonneg (fun i _ => sq_nonneg _)))

theorem covariance_reference_uniform_bounds (M : Matrix I I ℝ) (hM : M.det ≠ 0)
    (kappa U : ℝ) (hkappa : 0 < kappa) (hU : 0 ≤ U)
    (hfloor : ∀ x : I → ℝ, kappa*(∑ i, x i^2) ≤ dotProduct x ((M*M.transpose).mulVec x))
    (htrace : Matrix.trace (M*M.transpose) ≤ U) :
    matrixSquareEnergy M ≤ U ∧ matrixSquareEnergy M⁻¹ ≤ Fintype.card I/kappa ∧
    matrixEntryL1 M ≤ (Fintype.card I : ℝ)^2*Real.sqrt U ∧
    matrixEntryL1 M⁻¹ ≤ (Fintype.card I : ℝ)^2*Real.sqrt (Fintype.card I/kappa) ∧
    normalizationLoss M 1 ≤ (Fintype.card I : ℝ)^2/kappa := by
  have hm : matrixSquareEnergy M ≤ U := by rwa [matrixSquareEnergy_eq_covariance_trace]
  have hi : matrixSquareEnergy M⁻¹ ≤ Fintype.card I/kappa := inverse_frobenius_energy_le M hM kappa hkappa hfloor
  refine ⟨hm,hi,matrixEntryL1_le_of_squareEnergy M U hU hm,
    matrixEntryL1_le_of_squareEnergy M⁻¹ _ (by positivity) hi,?_⟩
  have he : normalizationLoss M 1=(Fintype.card I : ℝ)*matrixSquareEnergy M⁻¹ := by
    unfold normalizationLoss
    rw [← matrixSquareEnergy, matrixSquareEnergy_transpose]
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg (Fintype.card I))
  convert hh using 1
  ring

end GeneralizedBulk.Entropy
