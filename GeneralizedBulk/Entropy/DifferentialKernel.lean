import GeneralizedBulk.Entropy.DirectionalCalculus

/-! The concrete mixed tensor kernel applied to actual analytic derivatives. -/
noncomputable section
open Filter
open scoped BigOperators Topology ContDiff

namespace GeneralizedBulk.Entropy.Tensor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def thirdDifferential (f : E → ℝ) (x : E) : Trilinear E :=
  curryThree (iteratedFDeriv ℝ 3 f x).toMultilinearMap

@[simp] theorem thirdDifferential_apply (f : E → ℝ) (x u v w : E) :
    thirdDifferential f x u v w = iteratedFDeriv ℝ 3 f x ![u, v, w] := rfl

theorem thirdDifferential_swap12 (f : E → ℝ) (hf : ContDiff ℝ ω f) (x u v w : E) :
    thirdDifferential f x u v w = thirdDifferential f x v u w := by
  have hx : ContDiffAt ℝ ω f x := hf.contDiffAt
  have h := hx.iteratedFDeriv_comp_perm ![u, v, w] (Equiv.swap 0 1)
  have he : ![u, v, w] ∘ Equiv.swap 0 1 = ![v, u, w] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  rw [he] at h
  exact h.symm

theorem thirdDifferential_swap23 (f : E → ℝ) (hf : ContDiff ℝ ω f) (x u v w : E) :
    thirdDifferential f x u v w = thirdDifferential f x u w v := by
  have hx : ContDiffAt ℝ ω f x := hf.contDiffAt
  have h := hx.iteratedFDeriv_comp_perm ![u, v, w] (Equiv.swap 1 2)
  have he : ![u, v, w] ∘ Equiv.swap 1 2 = ![u, w, v] := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  rw [he] at h
  exact h.symm

def multilinearEvalCLM (n : ℕ) (m : Fin n → E) :
    (E [×n]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  (show (E [×n]→L[ℝ] ℝ) →ₗ[ℝ] ℝ from
    { toFun := fun M => M m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).mkContinuous (∏ i, ‖m i‖)
      (fun M => by simpa only [mul_comm] using M.le_opNorm m)

@[simp] theorem multilinearEvalCLM_apply (n : ℕ) (m : Fin n → E) (M : E [×n]→L[ℝ] ℝ) :
    multilinearEvalCLM n m M = M m := rfl

/-- Differentiating an identically zero tensor evaluation supplies a true
next-order derivative zero, without a formal higher-derivative premise. -/
theorem iteratedFDeriv_cons_eq_zero (n : ℕ) (f : E → ℝ) (hf : ContDiff ℝ ω f)
    (m : Fin n → E) (hzero : ∀ y, iteratedFDeriv ℝ n f y m = 0) (x v : E) :
    iteratedFDeriv ℝ (n + 1) f x (Fin.cons v m) = 0 := by
  let ev := multilinearEvalCLM n m
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    ContDiff.differentiable_iteratedFDeriv (by simp) hf
  have hh := ev.hasFDerivAt.comp x (hd x).hasFDerivAt
  have hfun : (fun y => ev (iteratedFDeriv ℝ n f y)) = fun _ => (0 : ℝ) := by
    funext y
    exact hzero y
  change HasFDerivAt (fun y => ev (iteratedFDeriv ℝ n f y))
    (ev.comp (fderiv ℝ (iteratedFDeriv ℝ n f) x)) x at hh
  rw [hfun] at hh
  have he := congrArg (fun L : E →L[ℝ] ℝ => L v) (hh.unique (hasFDerivAt_const (0 : ℝ) x))
  simpa only [ContinuousLinearMap.comp_apply, multilinearEvalCLM_apply,
    ContinuousLinearMap.zero_apply, iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons] using he

end GeneralizedBulk.Entropy.Tensor

namespace GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Entropy.Tensor

theorem thirdDifferential_transverse_zero (d k : ℕ) (hd : 3 ≤ d)
    (f : ColoredStar d k → ℝ) (hf : ContDiff ℝ ω f)
    (hmixed : ∀ x, ∀ i : Fin d, ∀ u v w,
      thirdDifferential f x (u - coloredEdgeProjection d k (by omega) i u)
        (coloredEdgeProjection d k (by omega) i v) w = 0)
    (x u v w : ColoredStar d k) : thirdDifferential f x (transversePart d k u) v w = 0 := by
  exact trilinear_transverse_first_zero d k hd (thirdDifferential f x)
    (thirdDifferential_swap12 f hf x) (hmixed x) (thirdDifferential_swap23 f hf x) u v w

theorem fourthDifferential_transverse_zero (d k : ℕ) (hd : 3 ≤ d)
    (f : ColoredStar d k → ℝ) (hf : ContDiff ℝ ω f)
    (hmixed : ∀ x, ∀ i : Fin d, ∀ u v w,
      thirdDifferential f x (u - coloredEdgeProjection d k (by omega) i u)
        (coloredEdgeProjection d k (by omega) i v) w = 0)
    (x a u v w : ColoredStar d k) :
    iteratedFDeriv ℝ 4 f x ![a, transversePart d k u, v, w] = 0 := by
  exact iteratedFDeriv_cons_eq_zero 3 f hf ![transversePart d k u, v, w]
    (fun y => thirdDifferential_transverse_zero d k hd f hf hmixed y u v w) x a

theorem fourthDifferential_last_transverse_zero (d k : ℕ) (hd : 3 ≤ d)
    (f : ColoredStar d k → ℝ) (hf : ContDiff ℝ ω f)
    (hmixed : ∀ x, ∀ i : Fin d, ∀ u v w,
      thirdDifferential f x (u - coloredEdgeProjection d k (by omega) i u)
        (coloredEdgeProjection d k (by omega) i v) w = 0)
    (x : ColoredStar d k) (m : Fin 3 → ColoredStar d k) (t : ColoredStar d k)
    (ht : transversePart d k t = t) :
    iteratedFDeriv ℝ 4 f x (Fin.snoc m t) = 0 := by
  have hx : ContDiffAt ℝ ω f x := hf.contDiffAt
  have hp := hx.iteratedFDeriv_comp_perm (Fin.snoc m t) (Equiv.swap 1 3)
  have he : Fin.snoc m t ∘ Equiv.swap 1 3 = ![m 0, t, m 2, m 1] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at hp
  rw [← hp]
  simpa only [ht] using fourthDifferential_transverse_zero d k hd f hf hmixed
    x (m 0) t (m 2) (m 1)

end GeneralizedBulk.Entropy.Channel
