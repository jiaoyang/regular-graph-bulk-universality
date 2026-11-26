import GeneralizedBulk.Entropy.DifferentialKernel

/-! Actual directional cancellation implies the mixed third-derivative kernel. -/
noncomputable section
open scoped ContDiff

namespace GeneralizedBulk.Entropy.Tensor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Equality of tensor evaluations as functions can be differentiated. -/
theorem iteratedFDeriv_cons_eq (n : ℕ) (f g : E → ℝ)
    (hf : ContDiff ℝ ω f) (hg : ContDiff ℝ ω g) (m : Fin n → E)
    (heq : ∀ y, iteratedFDeriv ℝ n f y m = iteratedFDeriv ℝ n g y m) (x v : E) :
    iteratedFDeriv ℝ (n + 1) f x (Fin.cons v m) =
      iteratedFDeriv ℝ (n + 1) g x (Fin.cons v m) := by
  let ev := multilinearEvalCLM n m
  have hdf : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    ContDiff.differentiable_iteratedFDeriv (by simp) hf
  have hdg : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
    ContDiff.differentiable_iteratedFDeriv (by simp) hg
  have hhf := ev.hasFDerivAt.comp x (hdf x).hasFDerivAt
  have hhg := ev.hasFDerivAt.comp x (hdg x).hasFDerivAt
  have hfun : (fun y => ev (iteratedFDeriv ℝ n f y)) =
      (fun y => ev (iteratedFDeriv ℝ n g y)) := funext heq
  change HasFDerivAt (fun y => ev (iteratedFDeriv ℝ n f y))
    (ev.comp (fderiv ℝ (iteratedFDeriv ℝ n f) x)) x at hhf
  change HasFDerivAt (fun y => ev (iteratedFDeriv ℝ n g y))
    (ev.comp (fderiv ℝ (iteratedFDeriv ℝ n g) x)) x at hhg
  rw [hfun] at hhf
  have h := congrArg (fun L : E →L[ℝ] ℝ => L v) (hhf.unique hhg)
  simpa only [ContinuousLinearMap.comp_apply, multilinearEvalCLM_apply,
    iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons] using h

/-- The retained derivative of `f` agrees with that of the conditional
polynomial `g`; `g` has zero discarded derivative. Two genuine
 differentiations and symmetry give the source mixed-kernel identity. -/
theorem thirdDifferential_zero_of_directional_cancellation (f g : E → ℝ)
    (hf : ContDiff ℝ ω f) (hg : ContDiff ℝ ω g) (u v : E)
    (hret : ∀ x, fderiv ℝ f x v = fderiv ℝ g x v)
    (hdiscard : ∀ x, fderiv ℝ g x u = 0) (x w : E) :
    thirdDifferential f x u v w = 0 := by
  have h2 : ∀ y, iteratedFDeriv ℝ 2 f y ![w, v] =
      iteratedFDeriv ℝ 2 g y ![w, v] := by
    intro y
    simpa only [Fin.cons_zero, Fin.tail_cons] using
      iteratedFDeriv_cons_eq 1 f g hf hg ![v]
        (fun y => by simpa only [iteratedFDeriv_one_apply, Matrix.cons_val_zero] using hret y) y w
  have h3 : thirdDifferential f x u w v = thirdDifferential g x u w v := by
    exact iteratedFDeriv_cons_eq 2 f g hf hg ![w, v] h2 x u
  have hg2 : ∀ y, iteratedFDeriv ℝ 2 g y ![v, u] = 0 := by
    intro y
    exact iteratedFDeriv_cons_eq_zero 1 g hg ![u]
      (fun y => by simpa only [iteratedFDeriv_one_apply, Matrix.cons_val_zero] using hdiscard y) y v
  have hg3 : thirdDifferential g x w v u = 0 :=
    iteratedFDeriv_cons_eq_zero 2 g hg ![v, u] hg2 x w
  calc
    thirdDifferential f x u v w = thirdDifferential f x u w v := thirdDifferential_swap23 f hf x u v w
    _ = thirdDifferential g x u w v := h3
    _ = thirdDifferential g x w u v := thirdDifferential_swap12 g hg x u w v
    _ = thirdDifferential g x w v u := thirdDifferential_swap23 g hg x w u v
    _ = 0 := hg3

theorem mixedThird_zero_of_derivative_projection (f g : E → ℝ)
    (hf : ContDiff ℝ ω f) (hg : ContDiff ℝ ω g) (P : E →L[ℝ] E)
    (hret : ∀ x v, fderiv ℝ f x (P v) = fderiv ℝ g x (P v))
    (hdiscard : ∀ x u, fderiv ℝ g x (u - P u) = 0) (x u v w : E) :
    thirdDifferential f x (u - P u) (P v) w = 0 :=
  thirdDifferential_zero_of_directional_cancellation f g hf hg (u - P u) (P v)
    (fun x => hret x v) (fun x => hdiscard x u) x w

end GeneralizedBulk.Entropy.Tensor
