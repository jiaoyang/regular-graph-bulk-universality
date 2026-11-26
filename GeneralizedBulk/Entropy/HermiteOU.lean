import GeneralizedBulk.Entropy.HermiteMultivariate

/-! Exact Ornstein--Uhlenbeck scaling of actual Gaussian Hermite polynomials,
proved by Gaussian integration by parts. -/
noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite
open GeneralizedBulk.Gaussian

def affinePolynomial (u v : ℝ) : ℝ[X] := C u + C v * X

@[simp] theorem affinePolynomial_eval (u v x : ℝ) : (affinePolynomial u v).eval x = u + v * x := by
  simp [affinePolynomial]

theorem integrable_polynomial_affine (P : ℝ[X]) (u v : ℝ) :
    Integrable (fun x => P.eval (u + v * x)) standardNormal := by
  simpa only [Polynomial.eval_comp, affinePolynomial_eval] using integrable_polynomial (P.comp (affinePolynomial u v))

/-- The true averaged Gaussian creation operator. -/
theorem integral_affine_creation (P : ℝ[X]) (a b y : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (∫ z : ℝ, (X * P - P.derivative).eval (a * y + b * z) ∂standardNormal) =
      a * y * (∫ z : ℝ, P.eval (a * y + b * z) ∂standardNormal) -
        a ^ 2 * ∫ z : ℝ, P.derivative.eval (a * y + b * z) ∂standardNormal := by
  have hp := integrable_polynomial_affine P (a * y) b
  have hd := integrable_polynomial_affine P.derivative (a * y) b
  have hz : Integrable (fun z : ℝ => z * P.eval (a * y + b * z)) standardNormal := by
    convert integrable_polynomial (X * P.comp (affinePolynomial (a * y) b)) using 1
    funext z
    simp [affinePolynomial]
  have hs := gaussian_stein (P.comp (affinePolynomial (a * y) b))
  have hde (z : ℝ) : ((P.comp (affinePolynomial (a * y) b)).derivative).eval z =
      b * P.derivative.eval (a * y + b * z) := by
    simp only [Polynomial.derivative_comp, Polynomial.eval_mul, Polynomial.eval_comp,
      affinePolynomial_eval, affinePolynomial, Polynomial.derivative_add, Polynomial.derivative_C,
      Polynomial.derivative_mul, Polynomial.derivative_X, mul_one, zero_mul, zero_add,
      Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_X]

  simp only [Polynomial.eval_comp, affinePolynomial_eval] at hs
  simp_rw [hde] at hs
  rw [integral_const_mul] at hs
  have he (z : ℝ) : (X * P - P.derivative).eval (a * y + b * z) =
      a * y * P.eval (a * y + b * z) + b * (z * P.eval (a * y + b * z)) -
        P.derivative.eval (a * y + b * z) := by
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
    ring
  simp_rw [he]
  rw [integral_sub (f := fun z => a * y * P.eval (a * y + b * z) + b * (z * P.eval (a * y + b * z)))
    (g := fun z => P.derivative.eval (a * y + b * z)) ((hp.const_mul _).add (hz.const_mul _)) hd,
    integral_add (f := fun z => a * y * P.eval (a * y + b * z))
      (g := fun z => b * (z * P.eval (a * y + b * z))) (hp.const_mul _) (hz.const_mul _),
    integral_const_mul, integral_const_mul, hs]
  have hcoeff : b * b - 1 = -(a ^ 2) := by nlinarith [hab]
  calc
    _ = a * y * (∫ z : ℝ, P.eval (a * y + b * z) ∂standardNormal) +
        (b * b - 1) * ∫ z : ℝ, P.derivative.eval (a * y + b * z) ∂standardNormal := by ring
    _ = _ := by rw [hcoeff]; ring

/-- Actual Gaussian affine smoothing scales the nth Hermite polynomial by
exactly the nth power of the signal coefficient. -/
theorem integral_hermite_affine (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (n : ℕ) (y : ℝ) :
    (∫ z : ℝ, (hermite n).eval (a * y + b * z) ∂standardNormal) = a ^ n * (hermite n).eval y := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [hermite_succ, integral_affine_creation _ a b y hab, ih n (by omega)]
      cases n with
      | zero => simp [hermite, Polynomial.derivative_one]
      | succ n =>
        simp only [derivative_hermite_succ, Polynomial.eval_smul, smul_eq_mul]
        rw [integral_const_mul, ih n (by omega)]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_smul, smul_eq_mul]
        simp only [pow_succ]
        ring


/-- Exact degree scaling for the actual multivariate affine Gaussian law. -/
theorem integral_multiHermite_affine {I : Type*} [Fintype I] (a b : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) (α : I → ℕ) (y : I → ℝ) :
    (∫ z, multiHermite I α (fun i => a * y i + b * z i) ∂standardGaussian I) =
      a ^ (∑ i, α i) * multiHermite I α y := by
  letI : MeasureSpace ℝ := ⟨standardNormal⟩
  letI : IsProbabilityMeasure (volume : Measure ℝ) := inferInstanceAs (IsProbabilityMeasure standardNormal)
  have hfub : (∫ z : I → ℝ, ∏ i : I, (hermite (α i)).eval (a * y i + b * z i) ∂standardGaussian I) =
      ∏ i : I, ∫ z : ℝ, (hermite (α i)).eval (a * y i + b * z) ∂standardNormal := by
    simpa only [standardGaussian, volume_pi] using integral_fintype_prod_eq_prod I
      (fun i : I => fun z : ℝ => (hermite (α i)).eval (a * y i + b * z))
  change (∫ z : I → ℝ, ∏ i : I, (hermite (α i)).eval (a * y i + b * z i) ∂standardGaussian I) = _
  rw [hfub]
  simp_rw [integral_hermite_affine a b hab]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rfl


theorem integrable_multiHermite_affine {I : Type*} [Fintype I] (a b : ℝ)
    (α : I → ℕ) (y : I → ℝ) :
    Integrable (fun z => multiHermite I α (fun i => a * y i + b * z i)) (standardGaussian I) := by
  letI : MeasureSpace ℝ := ⟨standardNormal⟩
  letI : IsProbabilityMeasure (volume : Measure ℝ) := inferInstanceAs (IsProbabilityMeasure standardNormal)
  have hp := Integrable.fintype_prod (fun i : I => integrable_polynomial_affine (hermite (α i)) (a * y i) b)
  simpa only [standardGaussian, volume_pi, multiHermite] using hp

end GeneralizedBulk.Entropy.Hermite
