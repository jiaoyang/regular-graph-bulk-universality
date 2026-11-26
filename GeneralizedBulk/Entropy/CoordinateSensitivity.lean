import Mathlib

/-! Coordinate Fréchet derivatives from a genuine finite ℓ¹ sensitivity bound. -/
noncomputable section
open scoped BigOperators Classical Topology

namespace GeneralizedBulk.Entropy

theorem coordinate_fderiv_le_of_l1_sensitivity {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℝ) → ℝ) (x : I → ℝ) (hf : DifferentiableAt ℝ f x)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y z,|f y-f z| ≤ C*∑ i,|y i-z i|) (i : I) :
    |fderiv ℝ f x (Pi.single i 1)| ≤ C := by
  let e : I → ℝ := Pi.single i 1
  let path : ℝ → I → ℝ := fun t => x+t • e
  have hp : HasDerivAt path e 0 := by
    simpa only [path,one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  have hcurve := hf.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hp (by simp [path])
  have hsum (t : ℝ) : (∑ j : I,|path t j-x j|) = |t| := by
    dsimp only [path,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    simp only [add_sub_cancel_left]
    rw [Finset.sum_eq_single i]
    · simp [e]
    · intro j hj hji
      simp [e,Pi.single_apply,hji,hji.symm]
    · simp
  have hb (t : ℝ) : ‖(f ∘ path) t-(f ∘ path) 0‖ ≤ C*‖t-(0 : ℝ)‖ := by
    simp only [Function.comp_apply,path,zero_smul,add_zero,sub_zero,Real.norm_eq_abs]
    have h := hbound (path t) x
    rw [hsum] at h
    exact h
  simpa only [Real.norm_eq_abs,e] using hcurve.le_of_lip' hC (Filter.Eventually.of_forall hb)

end GeneralizedBulk.Entropy
