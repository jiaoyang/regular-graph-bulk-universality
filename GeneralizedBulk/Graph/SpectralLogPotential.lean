import GeneralizedBulk.Graph.ResolventEntropy
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Rigidity comparison for the genuine regularized logarithmic potential. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Spectral

def regularizedLog (E eta t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((t - E) ^ 2 + eta ^ 2)

theorem regularizedLog_hasDerivAt (E eta : ℝ) (heta : 0 < eta) (t : ℝ) :
    HasDerivAt (regularizedLog E eta) ((t - E) / ((t - E) ^ 2 + eta ^ 2)) t := by
  have hd : 0 < (t - E) ^ 2 + eta ^ 2 := by nlinarith [sq_nonneg (t - E)]
  have hh := (((hasDerivAt_id t).sub_const E).pow 2 |>.add_const (eta ^ 2)).log hd.ne'
  convert hh.const_mul (1 / 2 : ℝ) using 1 <;> dsimp [regularizedLog] <;> ring

theorem regularizedLog_derivative_bound (E eta : ℝ) (heta : 0 < eta) (t : ℝ) :
    |(t - E) / ((t - E) ^ 2 + eta ^ 2)| ≤ eta⁻¹ := by
  have hd : 0 < (t - E) ^ 2 + eta ^ 2 := by nlinarith [sq_nonneg (t - E)]
  rw [abs_div, abs_of_pos hd, inv_eq_one_div]
  apply (div_le_div_iff₀ hd heta).mpr
  nlinarith [sq_nonneg (|t - E| - eta), sq_abs (t - E)]

/-- Global Lipschitz control, including across the spectral energy E. -/
theorem regularizedLog_lipschitz (E eta : ℝ) (heta : 0 < eta) (x y : ℝ) :
    |regularizedLog E eta x - regularizedLog E eta y| ≤ eta⁻¹ * |x - y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := regularizedLog E eta)
    (f' := fun t => (t - E) / ((t - E) ^ 2 + eta ^ 2))
    (C := eta⁻¹)
    (fun t _ => (regularizedLog_hasDerivAt E eta heta t).hasDerivWithinAt)
    (fun t _ => by simpa only [Real.norm_eq_abs] using regularizedLog_derivative_bound E eta heta t)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

/-- Finite eigenvalue replacement with a genuine Lipschitz comparison, before
any quantile Riemann-sum approximation. -/
theorem regularizedLog_sum_comparison {I : Type*} [Fintype I] (s : Finset I)
    (lambda gamma : I → ℝ) (E eta r : ℝ) (heta : 0 < eta)
    (hclose : ∀ i ∈ s, |lambda i - gamma i| ≤ r) :
    |(∑ i ∈ s, regularizedLog E eta (lambda i)) -
        ∑ i ∈ s, regularizedLog E eta (gamma i)| ≤ (s.card : ℝ) * (r / eta) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, |regularizedLog E eta (lambda i) - regularizedLog E eta (gamma i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, eta⁻¹ * r := by
      apply Finset.sum_le_sum
      intro i hi
      exact (regularizedLog_lipschitz E eta heta _ _).trans
        (mul_le_mul_of_nonneg_left (hclose i hi) (inv_nonneg.mpr heta.le))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end GeneralizedBulk.Spectral
