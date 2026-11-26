import GeneralizedBulk.Gaussian.Scalar

/-! Actual Gaussian polynomial integration by parts and Hermite energy inputs. -/
noncomputable section
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators NNReal
namespace GeneralizedBulk.Entropy.Hermite
open GeneralizedBulk.Gaussian

/-- Every univariate polynomial is integrable for the actual standard normal. -/
theorem integrable_polynomial (P : ℝ[X]) : Integrable (fun x => P.eval x) standardNormal := by
  induction P using Polynomial.induction_on' with
  | monomial n a => simpa using (standardNormal_integrable_pow n).const_mul a
  | add P Q hP hQ => simpa only [Polynomial.eval_add] using hP.add hQ

/-- Conversion of actual Gaussian integrability to its Lebesgue density. -/
theorem integrable_pdf_mul {f : ℝ → ℝ} (hf : Integrable f standardNormal) :
    Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  have hh : Integrable f (volume.withDensity (gaussianPDF 0 1)) := by
    simpa only [standardNormal, gaussianReal, one_ne_zero, ↓reduceIte] using hf
  have h := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (Eventually.of_forall (fun x => gaussianPDF_lt_top (μ := 0) (v := 1) (x := x)))).1 hh
  simpa only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _), smul_eq_mul] using h

/-- The actual standard Gaussian density satisfies its score differential equation. -/
theorem hasDerivAt_pdf (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := (((((hasDerivAt_id x).pow 2).neg).div_const 2).exp).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  convert h using 1
  · funext y
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, id_eq]
  · simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, id_eq,
      Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring

/-- Gaussian integration by parts is proved from the density and ordinary
FTC, with both the primitive and its derivative explicitly integrable. -/
theorem gaussian_stein (P : ℝ[X]) :
    (∫ x : ℝ, x * P.eval x ∂standardNormal) = ∫ x : ℝ, P.derivative.eval x ∂standardNormal := by
  have hP := integrable_pdf_mul (integrable_polynomial P)
  have hD := integrable_pdf_mul (integrable_polynomial (P.derivative - X * P))
  have hd (x : ℝ) : HasDerivAt (fun y => gaussianPDFReal 0 1 y * P.eval y)
      (gaussianPDFReal 0 1 x * (P.derivative - X * P).eval x) x := by
    convert (hasDerivAt_pdf x).mul (P.hasDerivAt x) using 1
    simp only [eval_sub, eval_mul, eval_X]
    ring
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hd hD hP
  have hg : (∫ x : ℝ, (P.derivative - X * P).eval x ∂standardNormal) = 0 := by
    rw [standardNormal, integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
    exact hz
  simp only [eval_sub, eval_mul, eval_X] at hg
  rw [integral_sub (integrable_polynomial P.derivative)
    (by
      convert integrable_polynomial (X * P) using 1
      funext x
      simp)] at hg
  linarith

/-- Real probabilists' Hermite polynomials, normalized to have leading coefficient one. -/
def hermite : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X * hermite n - (hermite n).derivative

@[simp] theorem hermite_zero : hermite 0 = 1 := rfl
@[simp] theorem hermite_succ (n : ℕ) : hermite (n + 1) = X * hermite n - (hermite n).derivative := rfl

/-- This is the standard mathlib probabilists' normalization, over the reals. -/
theorem hermite_eq_map (n : ℕ) : hermite n = (Polynomial.hermite n).map (Int.castRingHom ℝ) := by
  induction n with
  | zero => simp [hermite]
  | succ n ih => simp only [hermite_succ, Polynomial.hermite_succ, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_X, ← derivative_map, ← ih]

/-- The lowering identity used by the Hermite derivative-energy calculation. -/
theorem derivative_hermite_succ (n : ℕ) : (hermite (n + 1)).derivative = (n + 1 : ℝ) • hermite n := by
  induction n with
  | zero => simp [hermite]
  | succ n ih =>
    rw [hermite_succ (n + 1), derivative_sub, derivative_mul, derivative_X, one_mul, ih,
      derivative_smul]
    have hh : X * hermite n - (hermite n).derivative = hermite (n + 1) := (hermite_succ n).symm
    calc
      hermite (n + 1) + X * ((n + 1 : ℝ) • hermite n) - (n + 1 : ℝ) • (hermite n).derivative =
          hermite (n + 1) + (n + 1 : ℝ) • (X * hermite n - (hermite n).derivative) := by
        simp only [smul_eq_C_mul]
        ring
      _ = _ := by rw [hh]; simp only [Nat.cast_add, Nat.cast_one, smul_eq_C_mul, map_add, map_one]; ring

theorem integrable_product (P Q : ℝ[X]) :
    Integrable (fun x => P.eval x * Q.eval x) standardNormal := by
  convert integrable_polynomial (P * Q) using 1
  funext x
  simp

/-- The creation operator is the actual Gaussian adjoint of differentiation. -/
theorem creation_adjoint (n : ℕ) (Q : ℝ[X]) :
    (∫ x : ℝ, (hermite (n + 1)).eval x * Q.eval x ∂standardNormal) =
      ∫ x : ℝ, (hermite n).eval x * Q.derivative.eval x ∂standardNormal := by
  have hX : Integrable (fun x => x * (hermite n).eval x * Q.eval x) standardNormal := by
    convert integrable_polynomial (X * hermite n * Q) using 1
    funext x
    simp
  have hD := integrable_product (hermite n).derivative Q
  have hQ := integrable_product (hermite n) Q.derivative
  have hs := gaussian_stein (hermite n * Q)
  simp only [derivative_mul, eval_add, eval_mul] at hs
  rw [integral_add hD hQ] at hs
  have he (x : ℝ) : (hermite (n + 1)).eval x * Q.eval x =
      x * (hermite n).eval x * Q.eval x - (hermite n).derivative.eval x * Q.eval x := by
    rw [hermite_succ]
    simp only [eval_sub, eval_mul, eval_X]
    ring
  rw [integral_congr_ae (Eventually.of_forall he), integral_sub hX hD]
  have hs' : (∫ x : ℝ, x * (hermite n).eval x * Q.eval x ∂standardNormal) =
      (∫ x : ℝ, (hermite n).derivative.eval x * Q.eval x ∂standardNormal) +
        ∫ x : ℝ, (hermite n).eval x * Q.derivative.eval x ∂standardNormal := by
    calc
      _ = ∫ x : ℝ, x * ((hermite n).eval x * Q.eval x) ∂standardNormal := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := hs
  rw [hs']
  ring

@[simp] theorem integral_hermite_zero : (∫ x : ℝ, (hermite 0).eval x ∂standardNormal) = 1 := by simp

@[simp] theorem integral_hermite_succ (n : ℕ) :
    (∫ x : ℝ, (hermite (n + 1)).eval x ∂standardNormal) = 0 := by
  simpa using creation_adjoint n 1

/-- The actual Hermite pairing recursion, proved by Gaussian integration by parts. -/
theorem integral_hermite_pair_succ (n m : ℕ) :
    (∫ x : ℝ, (hermite (n + 1)).eval x * (hermite (m + 1)).eval x ∂standardNormal) =
      (m + 1 : ℝ) * ∫ x : ℝ, (hermite n).eval x * (hermite m).eval x ∂standardNormal := by
  rw [creation_adjoint, derivative_hermite_succ]
  calc
    _ = ∫ x : ℝ, (m + 1 : ℝ) * ((hermite n).eval x * (hermite m).eval x) ∂standardNormal := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [eval_smul, smul_eq_mul]
      ring
    _ = _ := integral_const_mul _ _

/-- Probabilists' Hermite polynomials are orthogonal for the actual Gaussian
measure and have exactly factorial squared norms. -/
theorem integral_hermite_pair (n m : ℕ) :
    (∫ x : ℝ, (hermite n).eval x * (hermite m).eval x ∂standardNormal) =
      if n = m then (n.factorial : ℝ) else 0 := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simp
    | succ m =>
      simpa only [hermite_zero, eval_one, one_mul, Nat.zero_ne_add_one, ↓reduceIte] using integral_hermite_succ m
  | succ n ih =>
    cases m with
    | zero =>
      simpa only [hermite_zero, eval_one, mul_one, Nat.add_one_ne_zero, ↓reduceIte] using integral_hermite_succ n
    | succ m =>
      rw [integral_hermite_pair_succ, ih]
      by_cases hnm : n = m
      · subst m
        simp [Nat.factorial_succ]
      · simp [hnm]

end GeneralizedBulk.Entropy.Hermite
