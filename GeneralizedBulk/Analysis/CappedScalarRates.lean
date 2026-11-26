import GeneralizedBulk.Analysis.ScalarCapBounds

/-! Actual affine logarithmic caps diverge, and the finite capped moment
bounds have finite limits after retaining the polynomial rejection/bad-event
error. No uncapped finite-model moment integration is used. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Analysis

theorem scalar_tail_error_polynomial (N : ℕ → ℕ) (hN : ∀ n,0 < N n)
    (bad : ℕ → ℝ) (A C beta : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hbound : ∀ᶠ n in atTop,bad n ≤ C*(N n : ℝ)^(-beta)) :
    ∀ᶠ n in atTop,A/(N n : ℝ)+bad n ≤ (A+C)*(N n : ℝ)^(-min (1 : ℝ) beta) := by
  filter_upwards [hbound] with n hn
  have hN1 : (1 : ℝ) ≤ N n := by exact_mod_cast hN n
  have h1 := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1
    (show -(1 : ℝ) ≤ -min 1 beta by linarith [min_le_left (1 : ℝ) beta])) hA
  have hb := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1
    (show -beta ≤ -min 1 beta by linarith [min_le_right (1 : ℝ) beta])) hC
  have heq : A/(N n : ℝ) = A*(N n : ℝ)^(-(1 : ℝ)) := by rw [Real.rpow_neg_one,div_eq_mul_inv]
  rw [heq]
  exact (add_le_add h1 (hn.trans hb)).trans_eq (by ring)

theorem affineScalarCap_nonneg (a b B step : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : 0 ≤ B) (hstep : 0 ≤ step) (N : ℕ) : 0 ≤ affineScalarCap a b B step N := by
  unfold affineScalarCap
  positivity

theorem affineScalarCap_tendsto_atTop (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (a b B step : ℝ) (hb : 0 < b) (hstep : 0 < step) :
    Tendsto (fun n => affineScalarCap a b B step (N n)) atTop atTop := by
  have hlog : Tendsto (fun n => (logarithmicCap (N n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (logarithmicCap_tendsto_atTop N hN)
  exact tendsto_atTop_add_const_left atTop a ((tendsto_atTop_add_const_left atTop B (hlog.const_mul_atTop hstep)).const_mul_atTop hb)

theorem affineScalarMomentLimit_nonneg (a b B step : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : 0 ≤ B) (hstep : 0 ≤ step) (q : ℕ) : 0 ≤ affineScalarMomentLimit a b B step q := by
  unfold affineScalarMomentLimit geometricMomentConstant
  positivity

theorem affineScalarMomentBound_tendsto (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n,0 ≤ epsilon n) (C beta a b B step : ℝ)
    (hC : 0 ≤ C) (hbeta : 0 < beta)
    (hbound : ∀ᶠ n in atTop,epsilon n ≤ C*(N n : ℝ)^(-beta)) (q : ℕ) :
    Tendsto (fun n => affineScalarMomentBound a b B step (epsilon n) (N n) q) atTop
      (nhds (affineScalarMomentLimit a b B step q)) := by
  have h := logarithmic_capped_moment_bound_tendsto N hN epsilon hepsilon C beta step hC hbeta hbound q
  have hc : Tendsto (fun _n : ℕ => (a+b*B)^q) atTop (nhds ((a+b*B)^q)) := tendsto_const_nhds
  have hh := (hc.add (h.const_mul (b^q))).const_mul ((2 : ℝ)^(q-1))
  convert hh using 1
  · funext n
    unfold affineScalarMomentBound
    ring
  · congr 1
    unfold affineScalarMomentLimit
    ring

theorem affineScalarMomentBound_eventually_le (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n,0 ≤ epsilon n) (C beta a b B step : ℝ)
    (hC : 0 ≤ C) (hbeta : 0 < beta)
    (hbound : ∀ᶠ n in atTop,epsilon n ≤ C*(N n : ℝ)^(-beta)) (q : ℕ) :
    ∀ᶠ n in atTop,affineScalarMomentBound a b B step (epsilon n) (N n) q ≤
      |affineScalarMomentLimit a b B step q|+1 := by
  have h := affineScalarMomentBound_tendsto N hN epsilon hepsilon C beta a b B step hC hbeta hbound q
  exact (h.eventually (eventually_lt_nhds
    (show affineScalarMomentLimit a b B step q < |affineScalarMomentLimit a b B step q|+1 by
      linarith [le_abs_self (affineScalarMomentLimit a b B step q)]))).mono (fun _ hn => hn.le)

end GeneralizedBulk.Analysis
