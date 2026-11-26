import GeneralizedBulk.Gaussian.WindowStateLaw

/-! Explicit finite complex coordinates avoid imposing a matrix norm convention. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped Topology
namespace GeneralizedBulk.Gaussian
variable (V : Type*)

abbrev FieldCoordinate := V × Fin 4 × Fin 4

def matrixFamilyCoordinates : (V → EndpointMatrix) ≃ₜ (FieldCoordinate V → ℂ) where
  toFun f k := f k.1 k.2.1 k.2.2
  invFun f v i j := f (v,i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply continuous_pi
    rintro ⟨v,i,j⟩
    exact (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply v))
  continuous_invFun := by
    apply continuous_pi
    intro v
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_apply (v,i,j)

def windowStateCoordinates : WindowFieldState V ≃ₜ AnchoredCountingState × (FieldCoordinate V → ℂ) :=
  (Homeomorph.refl AnchoredCountingState).prodCongr (matrixFamilyCoordinates V)

end GeneralizedBulk.Gaussian
