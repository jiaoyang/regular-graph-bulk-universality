import GeneralizedBulk.Entropy.DifferentialKernel

/-! Relating literal iterated coordinate derivatives to Fréchet tensors. -/
noncomputable section
open scoped BigOperators Topology ContDiff

namespace GeneralizedBulk.Entropy.Hermite
variable {I : Type*} [Fintype I] [DecidableEq I]

def linearEvalCLM (v : I → ℝ) : ((I → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (show ((I → ℝ) →L[ℝ] ℝ) →ₗ[ℝ] ℝ from
    { toFun := fun L => L v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).mkContinuous ‖v‖
      (fun L => by simpa only [mul_comm] using L.le_opNorm v)

@[simp] theorem linearEvalCLM_apply (v : I → ℝ) (L : (I → ℝ) →L[ℝ] ℝ) :
    linearEvalCLM v L = L v := rfl

theorem coordinateDerivative_eq_fderiv (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ ω f) (i : I) :
    coordinateDerivative f i = linearEvalCLM (Pi.single i 1) ∘ fderiv ℝ f := by
  funext x
  exact (fderiv_apply_basis_eq_coordinateDerivative f x
    (hf.differentiable le_top).differentiableAt i).symm

theorem contDiff_coordinateDerivative (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ ω f) (i : I) :
    ContDiff ℝ ω (coordinateDerivative f i) := by
  rw [coordinateDerivative_eq_fderiv f hf i]
  exact (linearEvalCLM (Pi.single i 1)).contDiff.comp (hf.fderiv_right le_top)

theorem iteratedFDeriv_coordinateDerivative (n : ℕ) (f : (I → ℝ) → ℝ)
    (hf : ContDiff ℝ ω f) (i : I) (x : I → ℝ) (m : Fin n → (I → ℝ)) :
    iteratedFDeriv ℝ n (coordinateDerivative f i) x m =
      iteratedFDeriv ℝ (n + 1) f x (Fin.snoc m (Pi.single i 1)) := by
  rw [coordinateDerivative_eq_fderiv f hf i,
    (linearEvalCLM (Pi.single i 1)).iteratedFDeriv_comp_left
      (hf.fderiv_right le_top).contDiffAt le_top]
  simp only [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  rfl

def coordinateDirections : (indices : List I) → Fin indices.length → (I → ℝ)
  | [] => fun i => Fin.elim0 i
  | i :: tail => Fin.snoc (coordinateDirections tail) (Pi.single i 1)

/-- The order of the tensor directions matches successive actual coordinate
derivatives. Analytic symmetry permits any subsequent reordering. -/
theorem iteratedCoordinateDerivative_eq_iteratedFDeriv (indices : List I)
    (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ ω f) (x : I → ℝ) :
    iteratedCoordinateDerivative indices f x =
      iteratedFDeriv ℝ indices.length f x (coordinateDirections indices) := by
  induction indices generalizing f with
  | nil => rfl
  | cons i tail ih =>
    change iteratedCoordinateDerivative tail (coordinateDerivative f i) x =
      iteratedFDeriv ℝ (tail.length + 1) f x
        (Fin.snoc (coordinateDirections tail) (Pi.single i 1))
    rw [ih _ (contDiff_coordinateDerivative f hf i), coordinateDerivative_eq_fderiv f hf i]
    rw [(linearEvalCLM (Pi.single i 1)).iteratedFDeriv_comp_left
      (hf.fderiv_right le_top).contDiffAt le_top]
    simp only [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
    rfl

/-- Vanishing of the actual top differential determines a finite homogeneous
Gaussian chaos. The proof uses the all-order energy identity, not an assumed
leading-monomial correspondence. -/
theorem chaosLp_eq_zero_of_iteratedFDeriv_zero {K : Type*} [Fintype K]
    (a : K → I → ℕ) (ha : Function.Injective a) (coeff : K → ℝ)
    (degree r : ℕ) (hdegree : ∀ k, ∑ j, a k j = degree) (hr : r ≤ degree)
    (hzero : ∀ x, ∀ m : Fin r → (I → ℝ), iteratedFDeriv ℝ r (chaosFunction a coeff) x m = 0) :
    chaosLp a coeff = 0 := by
  apply chaosLp_eq_zero_of_derivatives_zero r a ha coeff degree hdegree hr
  intro indices hlength x
  rw [iteratedCoordinateDerivative_eq_iteratedFDeriv indices _ (contDiff_chaosFunction a coeff) x]
  subst r
  exact hzero x (coordinateDirections indices)

end GeneralizedBulk.Entropy.Hermite
