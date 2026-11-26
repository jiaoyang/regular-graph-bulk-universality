import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Deterministic stability of the edge quadratic equation. The statements are
branch independent: the intended root is specified by its positive imaginary
part, together with an explicit sector ratio. -/
noncomputable section
namespace BourgadeHuang.RationalEdge

/-- Factorization of the edge residual, at an arbitrary square root. -/
theorem edge_residual_norm (z r w : ℂ) (hr : r ^ 2 = w) :
    ‖z ^ 2 - w‖ = ‖z - r‖ * ‖z + r‖ := by
  rw [← norm_mul, ← hr]
  congr 1
  ring

/-- The upper-half-plane root cannot be confused with the opposite root. -/
theorem edge_root_im_le_sum_norm {z r : ℂ} (hz : 0 ≤ z.im) :
    r.im ≤ ‖z + r‖ := by
  calc
    r.im ≤ (z + r).im := by simp only [Complex.add_im]; linarith
    _ ≤ |(z + r).im| := le_abs_self _
    _ ≤ ‖z + r‖ := Complex.abs_im_le_norm _

/-- Linear stability, with an explicit imaginary-part denominator. -/
theorem edge_linear_stability {z r w : ℂ} (hz : 0 ≤ z.im)
    (hr : 0 < r.im) (hsq : r ^ 2 = w) :
    ‖z - r‖ ≤ ‖z ^ 2 - w‖ / r.im := by
  apply (le_div_iff₀ hr).2
  rw [edge_residual_norm z r w hsq]
  exact mul_le_mul_of_nonneg_left (edge_root_im_le_sum_norm hz) (norm_nonneg _)

/-- A sector bound gives quadratic stability even when the residual is large. -/
theorem edge_quadratic_stability {z r w : ℂ} {K : ℝ}
    (hz : 0 ≤ z.im) (hK : 0 ≤ K) (hsector : ‖r‖ ≤ K * r.im)
    (hsq : r ^ 2 = w) :
    ‖z - r‖ ^ 2 ≤ (1 + 2 * K) * ‖z ^ 2 - w‖ := by
  have hden := edge_root_im_le_sum_norm (r := r) hz
  have htri : ‖z - r‖ ≤ ‖z + r‖ + 2 * ‖r‖ := by
    have heq : z - r = (z + r) - (2 : ℂ) * r := by ring
    rw [heq]
    simpa only [norm_mul, Complex.norm_ofNat] using norm_sub_le (z + r) ((2 : ℂ) * r)
  have hroot : ‖r‖ ≤ K * ‖z + r‖ :=
    hsector.trans (mul_le_mul_of_nonneg_left hden hK)
  have hlin : ‖z - r‖ ≤ (1 + 2 * K) * ‖z + r‖ := by linarith
  rw [edge_residual_norm z r w hsq]
  have hmul := mul_le_mul_of_nonneg_left hlin (norm_nonneg (z - r))
  nlinarith only [hmul]

/-- Norms of the root and the spectral parameter have their expected relation. -/
theorem edge_root_norm_sq {r w : ℂ} (hr : r ^ 2 = w) :
    ‖w‖ = ‖r‖ ^ 2 := by rw [← hr, norm_pow]

/-- Elementary growth bound used when absorbing the mixed quadratic moments. -/
theorem edge_resolvent_even_power_le (z w : ℂ) (q : ℕ) :
    ‖z‖ ^ (2 * q) ≤ (4 : ℝ) ^ q * (‖w‖ ^ q + ‖z ^ 2 - w‖ ^ q) := by
  have hbase : ‖z‖ ^ 2 ≤ ‖w‖ + ‖z ^ 2 - w‖ := by
    calc
      ‖z‖ ^ 2 = ‖z ^ 2‖ := (norm_pow z 2).symm
      _ = ‖w + (z ^ 2 - w)‖ := by congr 1; ring
      _ ≤ ‖w‖ + ‖z ^ 2 - w‖ := norm_add_le _ _
  calc
    ‖z‖ ^ (2 * q) = (‖z‖ ^ 2) ^ q := by rw [pow_mul]
    _ ≤ (‖w‖ + ‖z ^ 2 - w‖) ^ q :=
      pow_le_pow_left₀ (sq_nonneg _) hbase q
    _ ≤ (2 : ℝ) ^ (q - 1) * (‖w‖ ^ q + ‖z ^ 2 - w‖ ^ q) :=
      add_pow_le (norm_nonneg _) (norm_nonneg _) q
    _ ≤ (4 : ℝ) ^ q * (‖w‖ ^ q + ‖z ^ 2 - w‖ ^ q) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le q 1)).trans
        (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 4) q)

/-- The two cases used to absorb the square-root term in the edge moment bound. -/
theorem edge_scalar_absorption {A D R : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hR : 0 < R) (h : A ≤ D * (R + Real.sqrt A)) :
    A ≤ 2 * D * R ∨ Real.sqrt A ≤ 2 * D := by
  by_cases hs : Real.sqrt A ≤ R
  · left
    have hm := mul_le_mul_of_nonneg_left hs hD
    nlinarith
  · right
    have hs' : R < Real.sqrt A := lt_of_not_ge hs
    have hspos : 0 < Real.sqrt A := hR.trans hs'
    have hm := mul_le_mul_of_nonneg_left hs'.le hD
    have hsq := Real.sq_sqrt hA
    nlinarith

end BourgadeHuang.RationalEdge
