import GeneralizedBulk.Matrix.PositiveColorBlocks

noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Covariance
variable {C I : Type*} [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]

theorem colorBlock_det (A : C → Matrix I I ℝ) : (colorBlock A).det=∏ c,(A c).det := by
  rw [colorBlock_eq_blockDiagonal,Matrix.det_submatrix_equiv_self,Matrix.det_blockDiagonal]

theorem colorBlock_logabsdet (A : C → Matrix I I ℝ) (hA : ∀ c,(A c).det ≠ 0) :
    Real.log (|(colorBlock A).det|)=∑ c,Real.log (|(A c).det|) := by
  rw [colorBlock_det,Finset.abs_prod]
  exact Real.log_prod _ _ (fun c _ => abs_ne_zero.mpr (hA c))

end GeneralizedBulk.Covariance
