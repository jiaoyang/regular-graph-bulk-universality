import GeneralizedBulk.Analysis.CappedScalarRates

/-! The literal rejection plus exceptional-event error is polynomial and
therefore disappears from every actual affine logarithmically capped bound. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Analysis

theorem nonnegative_tendsto_zero_of_polynomial (N : ℕ → ℕ) (hNt : Tendsto N atTop atTop)
    (bad : ℕ → ℝ) (hbad : ∀ n,0 ≤ bad n) (C beta : ℝ) (hbeta : 0 < beta)
    (hbound : ∀ᶠ n in atTop,bad n ≤ C*(N n : ℝ)^(-beta)) :
    Tendsto bad atTop (nhds 0) := by
  have hpow := (tendsto_rpow_neg_atTop hbeta).comp (tendsto_natCast_atTop_atTop.comp hNt)
  exact squeeze_zero' (Eventually.of_forall hbad) hbound (by simpa only [mul_zero] using hpow.const_mul C)

theorem scalar_tail_error_nonneg (N : ℕ → ℕ) (bad : ℕ → ℝ)
    (A : ℝ) (hA : 0 ≤ A) (hbad : ∀ n,0 ≤ bad n) (n : ℕ) :
    0 ≤ A/(N n : ℝ)+bad n :=
  add_nonneg (div_nonneg hA (Nat.cast_nonneg _)) (hbad n)

theorem scalar_tail_error_tendsto_zero (N : ℕ → ℕ)
    (hN : ∀ n,0 < N n) (hNt : Tendsto N atTop atTop)
    (bad : ℕ → ℝ) (hbad : ∀ n,0 ≤ bad n)
    (A C beta : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hbeta : 0 < beta)
    (hbound : ∀ᶠ n in atTop,bad n ≤ C*(N n : ℝ)^(-beta)) :
    Tendsto (fun n => A/(N n : ℝ)+bad n) atTop (nhds 0) := by
  exact nonnegative_tendsto_zero_of_polynomial N hNt _ (scalar_tail_error_nonneg N bad A hA hbad)
    (A+C) (min 1 beta) (lt_min (by norm_num) hbeta)
    (scalar_tail_error_polynomial N hN bad A C beta hA hC hbound)

theorem affineScalarMomentBound_rejection_bad_tendsto (N : ℕ → ℕ)
    (hN : ∀ n,0 < N n) (hNt : Tendsto N atTop atTop)
    (bad : ℕ → ℝ) (hbad : ∀ n,0 ≤ bad n)
    (A C beta a b B step : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hbeta : 0 < beta)
    (hbound : ∀ᶠ n in atTop,bad n ≤ C*(N n : ℝ)^(-beta)) (q : ℕ) :
    Tendsto (fun n => affineScalarMomentBound a b B step (A/(N n : ℝ)+bad n) (N n) q) atTop
      (nhds (affineScalarMomentLimit a b B step q)) := by
  exact affineScalarMomentBound_tendsto N hNt _
    (fun n => add_nonneg (div_nonneg hA (Nat.cast_nonneg _)) (hbad n)) (A+C) (min 1 beta)
    a b B step (add_nonneg hA hC) (lt_min (by norm_num) hbeta)
    (scalar_tail_error_polynomial N hN bad A C beta hA hC hbound) q

theorem affineScalarMomentBound_rejection_bad_eventually_le (N : ℕ → ℕ)
    (hN : ∀ n,0 < N n) (hNt : Tendsto N atTop atTop)
    (bad : ℕ → ℝ) (hbad : ∀ n,0 ≤ bad n)
    (A C beta a b B step : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hbeta : 0 < beta)
    (hbound : ∀ᶠ n in atTop,bad n ≤ C*(N n : ℝ)^(-beta)) (q : ℕ) :
    ∀ᶠ n in atTop,affineScalarMomentBound a b B step (A/(N n : ℝ)+bad n) (N n) q ≤
      |affineScalarMomentLimit a b B step q|+1 := by
  exact affineScalarMomentBound_eventually_le N hNt _
    (fun n => add_nonneg (div_nonneg hA (Nat.cast_nonneg _)) (hbad n)) (A+C) (min 1 beta)
    a b B step (add_nonneg hA hC) (lt_min (by norm_num) hbeta)
    (scalar_tail_error_polynomial N hN bad A C beta hA hC hbound) q

end GeneralizedBulk.Analysis
