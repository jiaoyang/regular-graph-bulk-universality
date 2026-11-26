import Mathlib

/-! Exact covariance and determinant identities for independent Gaussian color blocks. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Covariance
variable {C I : Type*} [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]

theorem blockDiagonal_quadratic (A : C → Matrix I I ℝ) (x : I × C → ℝ) :
    dotProduct x ((Matrix.blockDiagonal A).mulVec x) =
      ∑ c, dotProduct (fun i => x (i,c)) ((A c).mulVec (fun i => x (i,c))) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.blockDiagonal_apply, Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]

theorem blockDiagonal_isHermitian (A : C → Matrix I I ℝ) (hA : ∀ c, (A c).IsHermitian) :
    (Matrix.blockDiagonal A).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.blockDiagonal_conjTranspose]
  exact congrArg Matrix.blockDiagonal (funext (fun c => (hA c).eq))

theorem blockDiagonal_posDef (A : C → Matrix I I ℝ) (hA : ∀ c, (A c).PosDef) :
    (Matrix.blockDiagonal A).PosDef := by
  refine ⟨blockDiagonal_isHermitian A (fun c => (hA c).isHermitian),fun x hx => ?_⟩
  simp only [star_trivial]
  rw [blockDiagonal_quadratic]
  obtain ⟨p,hp⟩ := Function.ne_iff.mp hx
  have hrow : (fun i => x (i,p.2)) ≠ 0 := by
    intro h
    exact hp (congrFun h p.1)
  have hs : 0 < dotProduct (fun i => x (i,p.2)) ((A p.2).mulVec (fun i => x (i,p.2))) := by
    simpa only [star_trivial] using (hA p.2).2 (fun i => x (i,p.2)) hrow
  have hn (c : C) : 0 ≤ dotProduct (fun i => x (i,c)) ((A c).mulVec (fun i => x (i,c))) := by
    simpa only [star_trivial] using (hA c).posSemidef.2 (fun i => x (i,c))
  exact Finset.sum_pos' (fun c _ => hn c) ⟨p.2,Finset.mem_univ _,hs⟩

theorem blockDiagonal_quadratic_floor (A : C → Matrix I I ℝ) (lo : ℝ)
    (hA : ∀ c (x : I → ℝ), lo*(∑ i, x i^2) ≤ dotProduct x ((A c).mulVec x)) (x : I × C → ℝ) :
    lo*(∑ p, x p^2) ≤ dotProduct x ((Matrix.blockDiagonal A).mulVec x) := by
  rw [blockDiagonal_quadratic, Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum (fun c _ => hA c (fun i => x (i,c)))

theorem blockDiagonal_factor_covariance (A : C → Matrix I I ℝ) :
    Matrix.blockDiagonal A*(Matrix.blockDiagonal A).transpose = Matrix.blockDiagonal (fun c => A c*(A c).transpose) := by
  rw [Matrix.blockDiagonal_transpose, Matrix.blockDiagonal_mul]

theorem blockDiagonal_logabsdet (A : C → Matrix I I ℝ) (hA : ∀ c, (A c).det ≠ 0) :
    Real.log (|(Matrix.blockDiagonal A).det|) = ∑ c, Real.log (|(A c).det|) := by
  rw [Matrix.det_blockDiagonal, Finset.abs_prod]
  exact Real.log_prod _ _ (fun c _ => abs_ne_zero.mpr (hA c))

end GeneralizedBulk.Covariance
