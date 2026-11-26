import BourgadeHuang.Limits
import BourgadeHuang.Counting
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Moment absorption for the loop hierarchy

These lemmas implement the non-circular Young absorption in Lemma 4.9.
All finite-size moments must be integrable before applying the integral estimates.
-/

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter

namespace BourgadeHuang

theorem lower_pow_le_one_add {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n ≤ 1 + x ^ (n + 1) := by
  by_cases h : x ≤ 1
  · have hp : x ^ n ≤ 1 := pow_le_one₀ hx h
    linarith [pow_nonneg hx (n + 1)]
  · have hp : x ^ n ≤ x ^ (n + 1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hx n) (le_of_not_ge h)
    linarith

theorem young_adjacent_powers {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) (n : ℕ) :
    x ^ n ≤ ε * x ^ (n + 1) + ε⁻¹ ^ n := by
  by_cases h : x ≤ ε⁻¹
  · exact (pow_le_pow_left₀ hx h n).trans
      (le_add_of_nonneg_left (mul_nonneg hε.le (pow_nonneg hx _)))
  · have he : 1 ≤ ε * x := by
      have hh : ε⁻¹ ≤ x := le_of_lt (lt_of_not_ge h)
      have hh' := mul_le_mul_of_nonneg_left hh hε.le
      simpa [ne_of_gt hε] using hh'
    have hp : x ^ n ≤ ε * x ^ (n + 1) := by
      calc
        x ^ n ≤ x ^ n * (ε * x) := le_mul_of_one_le_right (pow_nonneg hx _) he
        _ = ε * x ^ (n + 1) := by ring
    exact hp.trans (le_add_of_nonneg_right (by positivity))

/-- The exact complex cancellation used when the auxiliary parameters comprise `r`
copies of `w` and `r+2` copies of its conjugate. -/
theorem balanced_power_identity (s : ℂ) (r : ℕ) :
    s ^ 2 * (s ^ r * star s ^ (r + 2)) = (‖s‖ ^ (2 * r + 4) : ℝ) := by
  have hh : s * star s = (‖s‖ ^ 2 : ℝ) := by
    rw [Complex.sq_norm]
    exact Complex.mul_conj s
  calc
    s ^ 2 * (s ^ r * star s ^ (r + 2)) = (s * star s) ^ (r + 2) := by
      rw [mul_pow]
      ring
    _ = ((‖s‖ ^ 2 : ℝ) : ℂ) ^ (r + 2) := by rw [hh]
    _ = (‖s‖ ^ (2 * r + 4) : ℝ) := by
      rw [← Complex.ofReal_pow, ← pow_mul]
      congr 2

def momentAux (r : ℕ) (w : ℂ) : Fin (r + (r + 2)) → ℂ :=
  Fin.addCases (fun _ => w) (fun _ => star w)

theorem momentAux_eq_or (r : ℕ) (w : ℂ) (a : Fin (r + (r + 2))) :
    momentAux r w a = w ∨ momentAux r w a = star w := by
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) a
  · exact Or.inl (by simp [momentAux])
  · exact Or.inr (by simp [momentAux])

theorem momentAux_product {N : ℕ} (x : Fin N → ℝ) (center : ℝ) (r : ℕ) (w : ℂ) :
    (∏ a, microscopicResolvent x center (momentAux r w a)) =
      microscopicResolvent x center w ^ r *
        star (microscopicResolvent x center w) ^ (r + 2) := by
  rw [Fin.prod_univ_add]
  simp only [momentAux, Fin.addCases_left, Fin.addCases_right]
  rw [microscopicResolvent_reflection]
  simp

theorem momentAux_leading {N : ℕ} (x : Fin N → ℝ) (center : ℝ) (r : ℕ) (w : ℂ) :
    microscopicResolvent x center w ^ 2 *
        (∏ a, microscopicResolvent x center (momentAux r w a)) =
      (‖microscopicResolvent x center w‖ ^ (2 * r + 4) : ℝ) := by
  rw [momentAux_product, balanced_power_identity]

/-- An explicit absorption bound for a nonnegative random variable.  The hypothesis
is an integral inequality, not a uniform-moment assumption. -/
theorem integral_moment_absorption {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : ∀ ω, 0 ≤ X ω) (n : ℕ) {C A : ℝ} (hC : 0 < C)
    (hn : Integrable (fun ω => X ω ^ n) μ)
    (hn1 : Integrable (fun ω => X ω ^ (n + 1)) μ)
    (h : (∫ ω, X ω ^ (n + 1) ∂μ) ≤ A + C * (1 + ∫ ω, X ω ^ n ∂μ)) :
    (∫ ω, X ω ^ (n + 1) ∂μ) ≤ 2 * A + 2 * C * (1 + (2 * C) ^ n) := by
  have he : 0 < (2 * C)⁻¹ := by positivity
  have hy : (∫ ω, X ω ^ n ∂μ) ≤
      (2 * C)⁻¹ * (∫ ω, X ω ^ (n + 1) ∂μ) + (2 * C) ^ n := by
    calc
      (∫ ω, X ω ^ n ∂μ) ≤
          ∫ ω, (2 * C)⁻¹ * X ω ^ (n + 1) + ((2 * C)⁻¹)⁻¹ ^ n ∂μ :=
        integral_mono hn ((hn1.const_mul _).add (integrable_const _))
          (fun ω => young_adjacent_powers (hX ω) he n)
      _ = _ := by rw [integral_add (hn1.const_mul _) (integrable_const _)]
                  simp [integral_const_mul]
  have hc : C * (2 * C)⁻¹ = (1 / 2 : ℝ) := by field_simp; ring
  have hh := mul_le_mul_of_nonneg_left hy hC.le
  rw [mul_add, ← mul_assoc, hc] at hh
  linarith

/-- A complex loop equation controls a real moment once its leading term is real
and nonnegative. The remainder estimate is integrated before Young absorption. -/
theorem integral_moment_bound_of_loop {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (F : Ω → ℂ)
    (hX : ∀ ω, 0 ≤ X ω) (n : ℕ) {C A : ℝ} (hC : 0 < C)
    (hn : Integrable (fun ω => X ω ^ n) μ)
    (hn1 : Integrable (fun ω => X ω ^ (n + 1)) μ)
    (hF : Integrable F μ) (hsmall : ‖∫ ω, F ω ∂μ‖ ≤ A)
    (hrem : ∀ ω, ‖F ω - ((X ω ^ (n + 1) : ℝ) : ℂ)‖ ≤ C * (1 + X ω ^ n)) :
    (∫ ω, X ω ^ (n + 1) ∂μ) ≤ 2 * A + 2 * C * (1 + (2 * C) ^ n) := by
  apply integral_moment_absorption μ X hX n hC hn hn1
  let R : Ω → ℂ := fun ω => F ω - (X ω ^ (n + 1) : ℝ)
  have hR : Integrable R μ := hF.sub hn1.ofReal
  have hid : (∫ ω, F ω ∂μ) - (∫ ω, R ω ∂μ) =
      ((∫ ω, X ω ^ (n + 1) ∂μ : ℝ) : ℂ) := by
    rw [show (∫ ω, R ω ∂μ) = (∫ ω, F ω ∂μ) -
        ((∫ ω, X ω ^ (n + 1) ∂μ : ℝ) : ℂ) by
      change (∫ ω, F ω - ((X ω ^ (n + 1) : ℝ) : ℂ) ∂μ) = _
      calc
        _ = (∫ ω, F ω ∂μ) - ∫ ω, ((X ω ^ (n + 1) : ℝ) : ℂ) ∂μ :=
          integral_sub hF hn1.ofReal
        _ = _ := by rw [integral_complex_ofReal]]
    ring
  calc
    (∫ ω, X ω ^ (n + 1) ∂μ) = ‖(∫ ω, F ω ∂μ) - (∫ ω, R ω ∂μ)‖ := by
      rw [hid, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact integral_nonneg fun ω => pow_nonneg (hX ω) _
    _ ≤ ‖∫ ω, F ω ∂μ‖ + ‖∫ ω, R ω ∂μ‖ := norm_sub_le _ _
    _ ≤ A + ∫ ω, ‖R ω‖ ∂μ := add_le_add hsmall (norm_integral_le_integral_norm _)
    _ ≤ A + ∫ ω, C * (1 + X ω ^ n) ∂μ := by
      apply add_le_add_left
      exact integral_mono hR.norm (((integrable_const 1).add hn).const_mul C) hrem
    _ = A + C * (1 + ∫ ω, X ω ^ n ∂μ) := by
      rw [integral_const_mul, integral_add (integrable_const 1) hn]
      simp

end BourgadeHuang
