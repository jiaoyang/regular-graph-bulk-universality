import GeneralizedBulk.Matrix.BlockCovariance
import GeneralizedBulk.Entropy.MatrixEntryAlgebra

/-! Independent covariance blocks indexed with the color first. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Covariance
variable {C I : Type*} [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]

def colorBlock (A : C → Matrix I I ℝ) : Matrix (C × I) (C × I) ℝ :=
  fun p q => if p.1=q.1 then A p.1 p.2 q.2 else 0

theorem colorBlock_quadratic (A : C → Matrix I I ℝ) (x : C × I → ℝ) :
    dotProduct x ((colorBlock A).mulVec x)=
      ∑ c,dotProduct (fun i => x (c,i)) ((A c).mulVec (fun i => x (c,i))) := by
  simp only [dotProduct,Matrix.mulVec,colorBlock,Fintype.sum_prod_type,ite_mul,zero_mul,
    Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]

theorem colorBlock_quadratic_floor (A : C → Matrix I I ℝ) (lo : ℝ)
    (hA : ∀ c x,lo*(∑ i,x i^2) ≤ dotProduct x ((A c).mulVec x)) (x : C × I → ℝ) :
    lo*(∑ p,x p^2) ≤ dotProduct x ((colorBlock A).mulVec x) := by
  rw [colorBlock_quadratic,Fintype.sum_prod_type,Finset.mul_sum]
  exact Finset.sum_le_sum (fun c _ => hA c (fun i => x (c,i)))

theorem colorBlock_quadratic_upper (A : C → Matrix I I ℝ) (hi : ℝ)
    (hA : ∀ c x,dotProduct x ((A c).mulVec x) ≤ hi*(∑ i,x i^2)) (x : C × I → ℝ) :
    dotProduct x ((colorBlock A).mulVec x) ≤ hi*(∑ p,x p^2) := by
  rw [colorBlock_quadratic,Fintype.sum_prod_type,Finset.mul_sum]
  exact Finset.sum_le_sum (fun c _ => hA c (fun i => x (c,i)))

theorem colorBlock_trace (A : C → Matrix I I ℝ) :
    Matrix.trace (colorBlock A)=∑ c,Matrix.trace (A c) := by
  simp [Matrix.trace,Matrix.diag,colorBlock,Fintype.sum_prod_type]

theorem colorBlock_transpose (A : C → Matrix I I ℝ) :
    (colorBlock A).transpose=colorBlock (fun c => (A c).transpose) := by
  ext p q
  by_cases h : p.1=q.1
  · simp only [Matrix.transpose_apply,colorBlock,if_pos h,if_pos h.symm]
    rw [h]
  · simp only [Matrix.transpose_apply,colorBlock,if_neg h,if_neg (Ne.symm h)]

theorem colorBlock_mul (A B : C → Matrix I I ℝ) : colorBlock A*colorBlock B=colorBlock (fun c => A c*B c) := by
  ext p q
  simp only [Matrix.mul_apply,colorBlock,Fintype.sum_prod_type]
  by_cases h : p.1=q.1
  · simp [h,ite_mul,mul_ite,Finset.sum_ite_irrel]
  · have hh (c : C) : ¬(p.1=c ∧ c=q.1) := by rintro ⟨hp,hq⟩; exact h (hp.trans hq)
    simp only [if_neg h]
    apply Finset.sum_eq_zero
    intro c hc
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hp : p.1=c <;> by_cases hq : c=q.1 <;> simp_all

theorem colorBlock_sub (A B : C → Matrix I I ℝ) : colorBlock A-colorBlock B=colorBlock (fun c => A c-B c) := by
  ext p q
  by_cases h : p.1=q.1 <;> simp [colorBlock,h]

theorem colorBlock_entry_error (A B : C → Matrix I I ℝ) (e : ℝ) (he : 0 ≤ e)
    (hclose : ∀ c i j,|(A c-B c) i j| ≤ e) (p q : C × I) :
    |(colorBlock A-colorBlock B) p q| ≤ e := by
  rw [colorBlock_sub]
  by_cases h : p.1=q.1
  · simpa [colorBlock,h] using hclose p.1 p.2 q.2
  · simpa [colorBlock,h] using he

end GeneralizedBulk.Covariance
