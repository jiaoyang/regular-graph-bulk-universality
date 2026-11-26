import Mathlib.Data.Real.Sqrt
import BourgadeHuang.NevanlinnaLocalEstimates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pointwise Nevanlinna inequalities and scalar local-law absorption

These lemmas prove the elementary complex norm inequalities and the final
real-variable absorption step. Derivation of the moment inequality from the
loop hierarchy, and the requisite integrability and Hölder inequalities,
are proved in subsequent modules. In particular no local law is an assumption
hidden in an admissibility structure.
-/

namespace BourgadeHuang

/-- The bulk quadratic factors with the signs of the Stieltjes convention. -/
theorem bulk_quadratic_factorization (z : ℂ) :
    (z - Complex.I) * (z + Complex.I) = z ^ 2 + 1 := by
  calc
    _ = z ^ 2 - Complex.I ^ 2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- In the closed upper half-plane, the distance to `I` is no larger than
the distance to `-I`. -/
theorem nevanlinna_norm_sub_I_le_add_I (z : ℂ) (hz : 0 ≤ z.im) :
    ‖z - Complex.I‖ ≤ ‖z + Complex.I‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
  nlinarith

/-- The distance from an upper-half-plane value to `-I` is at least one. -/
theorem nevanlinna_one_le_norm_add_I (z : ℂ) (hz : 0 ≤ z.im) :
    1 ≤ ‖z + Complex.I‖ := by
  apply (sq_le_sq₀ (zero_le_one : (0 : ℝ) ≤ 1) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im, one_pow]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

/-- First of the two pointwise Nevanlinna bounds used in the moment bootstrap. -/
theorem nevanlinna_norm_sub_I_sq_le (z : ℂ) (hz : 0 ≤ z.im) :
    ‖z - Complex.I‖ ^ 2 ≤ ‖z ^ 2 + 1‖ := by
  calc
    _ = ‖z - Complex.I‖ * ‖z - Complex.I‖ := pow_two _
    _ ≤ ‖z - Complex.I‖ * ‖z + Complex.I‖ :=
      mul_le_mul_of_nonneg_left (nevanlinna_norm_sub_I_le_add_I z hz) (norm_nonneg _)
    _ = _ := by rw [← Complex.norm_mul, bulk_quadratic_factorization]

/-- Second of the two pointwise Nevanlinna bounds used in the moment bootstrap. -/
theorem nevanlinna_norm_sub_I_le (z : ℂ) (hz : 0 ≤ z.im) :
    ‖z - Complex.I‖ ≤ ‖z ^ 2 + 1‖ := by
  calc
    _ = ‖z - Complex.I‖ * 1 := by ring
    _ ≤ ‖z - Complex.I‖ * ‖z + Complex.I‖ :=
      mul_le_mul_of_nonneg_left (nevanlinna_one_le_norm_add_I z hz) (norm_nonneg _)
    _ = _ := by rw [← Complex.norm_mul, bulk_quadratic_factorization]

/-- A bound for the uncentered value in terms of the bulk quadratic. -/
theorem nevanlinna_norm_sq_le (z : ℂ) (hz : 0 ≤ z.im) :
    ‖z‖ ^ 2 ≤ 2 * (1 + ‖z ^ 2 + 1‖) := by
  have htriangle : ‖z‖ ≤ ‖z - Complex.I‖ + 1 := by
    simpa using norm_add_le (z - Complex.I) Complex.I
  have htriangle_sq : ‖z‖ ^ 2 ≤ (‖z - Complex.I‖ + 1) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg z) (add_nonneg (norm_nonneg _) zero_le_one)).mpr htriangle
  have hsq := nevanlinna_norm_sub_I_sq_le z hz
  nlinarith [norm_nonneg z, norm_nonneg (z - Complex.I),
    sq_nonneg (‖z - Complex.I‖ - 1)]

/-- The small-norm case of the scalar moment bootstrap. -/
theorem localLaw_absorption_small {R a : ℝ} (ha : 0 ≤ a)
    (hR : R ≤ 1) (hboot : R ^ 2 ≤ a * (1 + R)) :
    R ^ 2 ≤ 2 * a := by
  have hprod := mul_nonneg ha (sub_nonneg.mpr hR)
  nlinarith

/-- The large-norm case of the scalar moment bootstrap. -/
theorem localLaw_absorption_large {R a : ℝ} (ha : 0 ≤ a)
    (hR : 1 ≤ R) (hboot : R ^ 2 ≤ a * (1 + R)) :
    R ≤ 2 * a := by
  have hprod := mul_nonneg ha (sub_nonneg.mpr hR)
  have hquad : R ^ 2 ≤ 2 * a * R := by nlinarith
  by_contra h
  have hgap : 0 < R - 2 * a := by linarith
  have hpos : 0 < R := by linarith
  have := mul_pos hpos hgap
  nlinarith

/-- Absorption for a prospective norm `X` satisfying both Nevanlinna bounds.

In the intended application `R = ‖s(w)^2+1‖_(2q)`,
`X = ‖s(w)-I‖_(2q)`, and `a = 8*q/η^2`.  Those identifications
and the assumptions below have not been proved here from stochastic inputs.
-/
theorem localLaw_scalar_absorption {R a X : ℝ} (hR : 0 ≤ R)
    (ha : 0 ≤ a) (hX : 0 ≤ X) (hboot : R ^ 2 ≤ a * (1 + R))
    (hXR : X ≤ R) (hXsq : X ^ 2 ≤ R) : X ^ 2 ≤ 2 * a := by
  by_cases hsmall : R ≤ 1
  · have hsq := localLaw_absorption_small ha hsmall hboot
    have hprod := mul_nonneg (sub_nonneg.mpr hXR) (add_nonneg hR hX)
    nlinarith
  · exact hXsq.trans (localLaw_absorption_large ha (le_of_not_ge hsmall) hboot)

/-- Equivalent explicit minimum form of scalar absorption. -/
theorem localLaw_min_sq_bound {R a : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a)
    (hboot : R ^ 2 ≤ a * (1 + R)) :
    min R (Real.sqrt R) ^ 2 ≤ 2 * a := by
  have hmin : 0 ≤ min R (Real.sqrt R) := le_min hR (Real.sqrt_nonneg R)
  have hupper : min R (Real.sqrt R) ≤ Real.sqrt R := min_le_right _ _
  have hprod := mul_nonneg (sub_nonneg.mpr hupper)
    (add_nonneg (Real.sqrt_nonneg R) hmin)
  have hsqrt := Real.sq_sqrt hR
  exact localLaw_scalar_absorption hR ha hmin hboot (min_le_left _ _) (by nlinarith)

/-- Raising the squared norm estimate to the integer moment bound.
No probability-theoretic identification of `X` is assumed by this lemma. -/
theorem localLaw_power_bound (q : ℕ) {X η : ℝ} (_hη : 0 < η)
    (hXsq : X ^ 2 ≤ 16 * (q : ℝ) / η ^ 2) :
    X ^ (2 * q) ≤ (16 * (q : ℝ)) ^ q / η ^ (2 * q) := by
  calc
    X ^ (2 * q) = (X ^ 2) ^ q := by rw [pow_mul]
    _ ≤ (16 * (q : ℝ) / η ^ 2) ^ q := pow_le_pow_left₀ (sq_nonneg X) hXsq q
    _ = (16 * (q : ℝ)) ^ q / η ^ (2 * q) := by rw [div_pow, pow_mul]

/-- A natural-power Young bound with an elementary two-case proof. -/
theorem localLaw_young_nat (n : ℕ) {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    a*b^n ≤ b^(n+1)/2 + (2*a)^(n+1) := by
  by_cases h : b≤2*a
  · have hh : a*b^n ≤ (2*a)^(n+1) := by
      calc
        _ ≤ (2*a)*(2*a)^n := mul_le_mul (by linarith) (pow_le_pow_left₀ hb h n)
          (pow_nonneg hb _) (by positivity)
        _ = _ := by rw [pow_succ]; ring
    have hz : 0≤b^(n+1)/2 := by positivity
    linarith
  · have hab : a≤b/2 := by linarith
    have hh := mul_le_mul_of_nonneg_right hab (pow_nonneg hb n)
    have heq : (b/2)*b^n = b^(n+1)/2 := by rw [pow_succ]; ring
    rw [heq] at hh
    exact hh.trans (le_add_of_nonneg_right (by positivity))

/-- Uncentered moments reduced to moments of the bulk quadratic. -/
theorem nevanlinna_norm_pow_le (z : ℂ) (hz : 0≤z.im) (q : ℕ) :
    ‖z‖^(2*q) ≤ 4^q*(1+‖z^2+1‖^q) := by
  calc
    _ = (‖z‖^2)^q := by rw [pow_mul]
    _ ≤ (2*(1+‖z^2+1‖))^q := pow_le_pow_left₀ (sq_nonneg _) (nevanlinna_norm_sq_le z hz) q
    _ = 2^q*(1+‖z^2+1‖)^q := mul_pow _ _ _
    _ ≤ 2^q*(2^(q-1)*(1+‖z^2+1‖^q)) := by
      gcongr
      simpa only [one_pow] using add_pow_le (show (0:ℝ)≤1 by norm_num) (norm_nonneg (z^2+1)) q
    _ ≤ 2^q*(2^q*(1+‖z^2+1‖^q)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (Nat.sub_le q 1)) (by positivity)) (by positivity)
    _ = _ := by rw [← mul_assoc,← mul_pow]; norm_num

end BourgadeHuang
