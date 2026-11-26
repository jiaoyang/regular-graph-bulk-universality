import GeneralizedBulk.Matrix.ColorBlocks
import GeneralizedBulk.Matrix.PositiveCompression

noncomputable section
namespace GeneralizedBulk.Covariance
variable {C I : Type*} [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]

theorem colorBlock_eq_blockDiagonal (A : C → Matrix I I ℝ) :
    colorBlock A=(Matrix.blockDiagonal A).submatrix (Equiv.prodComm C I) (Equiv.prodComm C I) := by
  ext p q
  rfl

theorem colorBlock_posDef (A : C → Matrix I I ℝ) (hA : ∀ c,(A c).PosDef) : (colorBlock A).PosDef := by
  rw [colorBlock_eq_blockDiagonal]
  exact posDef_submatrix_of_injective _ (blockDiagonal_posDef A hA) _ (Equiv.prodComm C I).injective

end GeneralizedBulk.Covariance
