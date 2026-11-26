import GeneralizedBulk.Entropy.HermiteJetEnergy
import GeneralizedBulk.Entropy.TensorKernel
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-! Actual directional and higher differential tensors of Gaussian polynomials. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace GeneralizedBulk.Entropy.Hermite

theorem contDiff_polynomial_eval (p : Polynomial ℝ) : ContDiff ℝ ω (fun t : ℝ => p.eval t) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n c => simpa only [Polynomial.eval_monomial] using contDiff_const.mul (contDiff_id.pow n)

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem contDiff_multiHermite (a : I → ℕ) : ContDiff ℝ ω (multiHermite I a) := by
  unfold multiHermite
  apply contDiff_prod
  intro i hi
  exact (contDiff_polynomial_eval (hermite (a i))).comp
    (ContinuousLinearMap.proj i : (I → ℝ) →L[ℝ] ℝ).contDiff

theorem contDiff_chaosFunction {K : Type*} [Fintype K] (a : K → I → ℕ) (coeff : K → ℝ) :
    ContDiff ℝ ω (chaosFunction a coeff) := by
  unfold chaosFunction
  apply ContDiff.sum
  intro k hk
  exact contDiff_const.mul (contDiff_multiHermite (a k))

theorem hasDerivAt_coordinateLine (x : I → ℝ) (i : I) :
    HasDerivAt (fun t : ℝ => Function.update x i (x i + t)) (Pi.single i 1) 0 := by
  apply hasDerivAt_pi.mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self, Pi.single_eq_same] using
      (hasDerivAt_id (0 : ℝ)).const_add (x i)
  · simpa only [Function.update_of_ne hji, Pi.single_eq_of_ne hji] using
      hasDerivAt_const (0 : ℝ) (x j)

theorem fderiv_apply_basis_eq_coordinateDerivative (f : (I → ℝ) → ℝ)
    (x : I → ℝ) (hf : DifferentiableAt ℝ f x) (i : I) :
    fderiv ℝ f x (Pi.single i 1) = coordinateDerivative f i x := by
  have hh : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i + 0)) := by
    simpa only [add_zero, Function.update_eq_self] using hf.hasFDerivAt
  exact (hh.comp_hasDerivAt 0 (hasDerivAt_coordinateLine x i)).deriv.symm

theorem fderiv_chaosFunction_basis {K : Type*} [Fintype K]
    (a : K → I → ℕ) (coeff : K → ℝ) (x : I → ℝ) (i : I) :
    fderiv ℝ (chaosFunction a coeff) x (Pi.single i 1) = chaosDerivativeFunction a coeff i x := by
  have hf : DifferentiableAt ℝ (chaosFunction a coeff) x :=
    ((contDiff_chaosFunction a coeff).differentiable (show (1 : WithTop ℕ∞) ≤ ⊤ from le_top)).differentiableAt
  rw [fderiv_apply_basis_eq_coordinateDerivative _ x hf i]
  exact (hasDerivAt_chaosFunction_coordinate a coeff i x).deriv

/-- Directional differentiation is the actual Fréchet derivative, with its
explicit finite Hermite lowering formula. -/
theorem fderiv_chaosFunction_apply {K : Type*} [Fintype K]
    (a : K → I → ℕ) (coeff : K → ℝ) (x v : I → ℝ) :
    fderiv ℝ (chaosFunction a coeff) x v = ∑ i, v i * chaosDerivativeFunction a coeff i x := by
  have hv : v = ∑ i, v i • (Pi.single i (1 : ℝ) : I → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [map_smul, smul_eq_mul, fderiv_chaosFunction_basis]

end GeneralizedBulk.Entropy.Hermite

namespace GeneralizedBulk.Entropy.Tensor
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def curryThree (M : MultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) : Trilinear E where
  toFun x := {
    toFun y := {
      toFun z := M ![x, y, z]
      map_add' z w := ((M.curryLeft x).curryLeft y).cons_add ![] z w
      map_smul' c z := ((M.curryLeft x).curryLeft y).cons_smul ![] c z }
    map_add' y v := by
      ext z
      exact (M.curryLeft x).cons_add ![z] y v
    map_smul' c y := by
      ext z
      exact (M.curryLeft x).cons_smul ![z] c y }
  map_add' x u := by
    ext y z
    exact M.cons_add ![y, z] x u
  map_smul' c x := by
    ext y z
    exact M.cons_smul ![y, z] c x

@[simp] theorem curryThree_apply (M : MultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (x y z : E) :
    curryThree M x y z = M ![x, y, z] := rfl

end GeneralizedBulk.Entropy.Tensor
