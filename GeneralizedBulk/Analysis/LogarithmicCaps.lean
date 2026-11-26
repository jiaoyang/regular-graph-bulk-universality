import GeneralizedBulk.Analysis.CappedTail
import GeneralizedBulk.Graph.ReciprocalRates

/-!
# Logarithmic caps retain finite-size errors until they vanish

Polynomial exceptional probabilities times every fixed capped moment error
tend to zero. The cap is a literal integer floor of log N, not an uncapped
finite-model integration.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Analysis

def logarithmicCap (N : ℕ) : ℕ := ⌊Real.log (N : ℝ)⌋₊

theorem logarithmicCap_tendsto_atTop (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => logarithmicCap (N n)) atTop atTop :=
  tendsto_nat_floor_atTop.comp (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp hN))

/-- The complete finite cap error vanishes for every fixed moment order. -/
theorem logarithmic_cap_error_tendsto_zero
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (epsilon : ℕ → ℝ)
    (hepsilon : ∀ n, 0 ≤ epsilon n) (C beta : ℝ) (hC : 0 ≤ C) (hbeta : 0 < beta)
    (hbound : ∀ᶠ n in atTop, epsilon n ≤ C * (N n : ℝ) ^ (-beta)) (q : ℕ) :
    Tendsto (fun n => epsilon n * (logarithmicCap (N n) : ℝ) *
      (((logarithmicCap (N n) + 1 : ℕ) : ℝ) ^ q)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun n => (N n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hlog := (isLittleO_log_rpow_rpow_atTop (q + 1 : ℕ) hbeta).tendsto_div_nhds_zero
  have hlim : Tendsto (fun n => C * (2 : ℝ) ^ q *
      (Real.log (N n : ℝ) ^ (q + 1) / (N n : ℝ) ^ beta)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, mul_zero] using (hlog.comp hreal).const_mul (C * (2 : ℝ) ^ q)
  apply squeeze_zero' (Eventually.of_forall (fun n => by have := hepsilon n; positivity)) _ hlim
  filter_upwards [hbound, (Real.tendsto_log_atTop.comp hreal).eventually (eventually_ge_atTop 1),
    hN.eventually (eventually_ge_atTop 1)] with n hn hlogn hsize
  dsimp only [Function.comp_def] at hlogn
  have hNR : 0 < (N n : ℝ) := by exact_mod_cast hsize
  have hm : (logarithmicCap (N n) : ℝ) ≤ Real.log (N n : ℝ) :=
    Nat.floor_le (Real.log_natCast_nonneg _)
  have hm1 : (((logarithmicCap (N n) + 1 : ℕ) : ℝ)) ≤ 2 * Real.log (N n : ℝ) := by
    push_cast
    linarith
  have hprod : (logarithmicCap (N n) : ℝ) *
      (((logarithmicCap (N n) + 1 : ℕ) : ℝ) ^ q) ≤
      (2 : ℝ) ^ q * Real.log (N n : ℝ) ^ (q + 1) := by
    have hp := mul_le_mul hm (pow_le_pow_left₀ (by positivity) hm1 q)
      (by positivity : 0 ≤ (((logarithmicCap (N n) + 1 : ℕ) : ℝ) ^ q)) (by linarith : 0 ≤ Real.log (N n : ℝ))
    convert hp using 1 <;> rw [mul_pow, pow_succ] <;> ring
  calc
    _ = epsilon n * ((logarithmicCap (N n) : ℝ) *
        (((logarithmicCap (N n) + 1 : ℕ) : ℝ) ^ q)) := by ring
    _ ≤ (C * (N n : ℝ) ^ (-beta)) * ((2 : ℝ) ^ q * Real.log (N n : ℝ) ^ (q + 1)) :=
      mul_le_mul hn hprod (by positivity) (by positivity)
    _ = _ := by rw [Real.rpow_neg hNR.le]; ring

/-- The literal capped recursion bounds have a finite limit at every order. -/
theorem logarithmic_capped_moment_bound_tendsto
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (epsilon : ℕ → ℝ)
    (hepsilon : ∀ n, 0 ≤ epsilon n) (C beta A : ℝ) (hC : 0 ≤ C) (hbeta : 0 < beta)
    (hbound : ∀ᶠ n in atTop, epsilon n ≤ C * (N n : ℝ) ^ (-beta)) (q : ℕ) :
    Tendsto (fun n => A ^ q * (geometricMomentConstant q +
      2 * epsilon n * (logarithmicCap (N n) : ℝ) *
        (((logarithmicCap (N n) + 1 : ℕ) : ℝ) ^ q))) atTop
      (𝓝 (A ^ q * geometricMomentConstant q)) := by
  have h := logarithmic_cap_error_tendsto_zero N hN epsilon hepsilon C beta hC hbeta hbound q
  have heq (n) : 2 * epsilon n * (logarithmicCap (N n) : ℝ) *
      (((logarithmicCap (N n) + 1 : ℕ) : ℝ) ^ q) =
      2 * (epsilon n * (logarithmicCap (N n) : ℝ) *
        (((logarithmicCap (N n) + 1 : ℕ) : ℝ) ^ q)) := by ring
  simpa only [heq, mul_zero, add_zero] using
    (tendsto_const_nhds.add (h.const_mul 2)).const_mul (A ^ q)

end GeneralizedBulk.Analysis
