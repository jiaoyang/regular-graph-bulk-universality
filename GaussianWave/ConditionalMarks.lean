import GaussianWave.Foundation

/-!
# From quenched convergence to stable bounded graph tests

A real measurable function `q n ω` represents the conditional expectation of
one fixed bounded mark test, after averaging the auxiliary edge sampling on
the graph `ω`. The graph measure is an actual probability measure. The main
input is mathlib's convergence in measure (convergence in probability here),
not convergence of expectations. The latter is proved by splitting into the
event where the error is small and its complement.

No independence in a limiting joint law is postulated. The final result is
the bounded product-test factorization from which such independence follows
when a joint limit and a separating class of mark tests are supplied.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GaussianWave
namespace ConditionalMarks

lemma integrable_abs_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (q : Ω → ℝ) (hq : Measurable q)
    (c B : ℝ) (hB : ∀ ω, |q ω| ≤ B) (hc : |c| ≤ B) :
    Integrable (fun ω => |q ω - c|) μ := by
  apply (integrable_const (2 * B)).mono' (hq.sub_const c).abs.aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_abs]
  exact (abs_sub (q ω) c).trans (by linarith [hB ω, hc])

/-- The explicit small-error / exceptional-event estimate. -/
theorem integral_abs_error_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (q : Ω → ℝ) (hq : Measurable q)
    (c B : ℝ) (hB : ∀ ω, |q ω| ≤ B) (hc : |c| ≤ B)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (∫ ω, |q ω - c| ∂μ) ≤
      ε + 2 * B * (μ {ω | ε ≤ |q ω - c|}).toReal := by
  let bad : Set Ω := {ω | ε ≤ |q ω - c|}
  have hbad : MeasurableSet bad :=
    measurableSet_le measurable_const (hq.sub_const c).abs
  have hi := integrable_abs_error μ q hq c B hB hc
  have hiBad : Integrable (bad.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const _).indicator hbad
  have hb (ω : Ω) : |q ω - c| ≤
      ε + 2 * B * bad.indicator (fun _ : Ω => (1 : ℝ)) ω := by
    by_cases hω : ω ∈ bad
    · rw [Set.indicator_of_mem hω]
      have h := (abs_sub (q ω) c).trans (add_le_add (hB ω) hc)
      linarith
    · rw [Set.indicator_of_not_mem hω]
      have hsmall : |q ω - c| < ε := lt_of_not_ge hω
      simpa using hsmall.le
  calc
    _ ≤ ∫ ω, ε + 2 * B * bad.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ :=
      integral_mono hi ((integrable_const _).add (hiBad.const_mul _)) hb
    _ = _ := by
      rw [integral_add (integrable_const _) (hiBad.const_mul _), integral_const_mul,
        integral_indicator hbad]
      simp [bad, measureReal_def]

/-- Bounded convergence in probability gives actual convergence in L1. -/
theorem integral_abs_error_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ → Ω → ℝ) (hq : ∀ n, Measurable (q n)) (c B : ℝ)
    (hB : ∀ n ω, |q n ω| ≤ B) (hc : |c| ≤ B)
    (hprob : TendstoInMeasure μ q atTop (fun _ => c)) :
    Tendsto (fun n => ∫ ω, |q n ω - c| ∂μ) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (integral_nonneg (fun ω => abs_nonneg _)))
  · intro b hb
    have hbad : Tendsto
        (fun n => (μ {ω | b / 2 ≤ |q n ω - c|}).toReal) atTop (𝓝 0) := by
      have hm := hprob (b / 2) (by linarith)
      have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hm
      simpa only [Real.dist_eq, ENNReal.toReal_zero] using ht
    have htail : ∀ᶠ n in atTop,
        2 * B * (μ {ω | b / 2 ≤ |q n ω - c|}).toReal < b / 2 := by
      apply (tendsto_order.mp (show Tendsto
        (fun n => 2 * B * (μ {ω | b / 2 ≤ |q n ω - c|}).toReal) atTop (𝓝 0) from
        by simpa only [mul_zero] using hbad.const_mul (2 * B))).2
      linarith
    filter_upwards [htail] with n hn
    have he := integral_abs_error_event_bound μ (q n) (hq n) c B (hB n) hc
      (b / 2) (by linarith)
    linarith

/-- The error is small against every bounded graph-state test, even when the
state test changes with the graph size. Complex tests include characteristic
functions of an entire graph-derived state. -/
theorem bounded_graph_test_error_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Ω → ℝ) (hq : Measurable q) (c B : ℝ)
    (hB : ∀ ω, |q ω| ≤ B) (hc : |c| ≤ B)
    (H : Ω → ℂ) (hH : Measurable H) (C : ℝ) (hC : ∀ ω, ‖H ω‖ ≤ C) :
    ‖(∫ ω, H ω * (q ω : ℂ) ∂μ) - (∫ ω, H ω ∂μ) * (c : ℂ)‖ ≤
      C * ∫ ω, |q ω - c| ∂μ := by
  have hiH : Integrable H μ :=
    (integrable_const C).mono' hH.aestronglyMeasurable (Eventually.of_forall hC)
  have hiP : Integrable (fun ω => H ω * (q ω : ℂ)) μ := by
    apply (integrable_const (C * B)).mono' (hH.mul hq.complex_ofReal).aestronglyMeasurable
    filter_upwards [] with ω
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hC ω) (hB ω) (abs_nonneg _) ((norm_nonneg _).trans (hC ω))
  have hiE := integrable_abs_error μ q hq c B hB hc
  have heq : (∫ ω, H ω * (q ω : ℂ) ∂μ) - (∫ ω, H ω ∂μ) * (c : ℂ) =
      ∫ ω, H ω * ((q ω - c : ℝ) : ℂ) ∂μ := by
    rw [← integral_mul_const, ← integral_sub hiP (hiH.mul_const (c : ℂ))]
    apply integral_congr_ae
    filter_upwards [] with ω
    push_cast
    ring
  rw [heq]
  have hiG : Integrable (fun ω => H ω * ((q ω - c : ℝ) : ℂ)) μ := by
    convert hiP.sub (hiH.mul_const (c : ℂ)) using 1
    funext ω
    simp only [Pi.sub_apply]
    push_cast
    ring
  calc
    _ ≤ ∫ ω, ‖H ω * ((q ω - c : ℝ) : ℂ)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, C * |q ω - c| ∂μ := integral_mono hiG.norm (hiE.const_mul C) (fun ω => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC ω) (abs_nonneg _))
    _ = _ := integral_const_mul _ _

/-- Quenched convergence in probability and boundedness imply stable product
factorization against arbitrary uniformly bounded measurable graph tests. -/
theorem quenched_mark_factorization {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ → Ω → ℝ) (hq : ∀ n, Measurable (q n)) (c B : ℝ)
    (hB : ∀ n ω, |q n ω| ≤ B) (hc : |c| ≤ B)
    (hprob : TendstoInMeasure μ q atTop (fun _ => c))
    (H : ℕ → Ω → ℂ) (hH : ∀ n, Measurable (H n)) (C : ℝ)
    (hC : ∀ n ω, ‖H n ω‖ ≤ C) :
    Tendsto
      (fun n => (∫ ω, H n ω * (q n ω : ℂ) ∂μ) -
        (∫ ω, H n ω ∂μ) * (c : ℂ)) atTop (𝓝 0) := by
  have hL1 := integral_abs_error_tendsto_zero μ q hq c B hB hc hprob
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => bounded_graph_test_error_bound μ (q n) (hq n) c B (hB n) hc
      (H n) (hH n) C (hC n))
  simpa only [mul_zero] using hL1.const_mul C

/-- Averaging a bounded mark test against an actual probability law preserves
its uniform bound. This applies to the finite empirical edge law as well as
any probability kernel evaluated at a fixed graph. -/
lemma abs_mark_expectation_le {Y : Type*} [MeasurableSpace Y]
    (κ : ProbabilityMeasure Y) (f : Y → ℝ) (B : ℝ) (hB : ∀ y, |f y| ≤ B) :
    |∫ y, f y ∂(κ : Measure Y)| ≤ B := by
  have h := norm_integral_le_of_norm_le_const
    (μ := (κ : Measure Y)) (f := f)
    (Eventually.of_forall (fun y => show ‖f y‖ ≤ B by simpa only [Real.norm_eq_abs] using hB y))
  simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using h

/-- A concrete conditional-mark-law version: `κ n ω` is the edge-sampling
probability law on a fixed graph and `ν` is the target Gaussian mark law.
Only measurability of this particular conditional test is required. -/
theorem conditional_mark_law_factorization
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : ℕ → Ω → ProbabilityMeasure Y) (ν : ProbabilityMeasure Y)
    (f : Y → ℝ) (B : ℝ) (hB : ∀ y, |f y| ≤ B)
    (hq : ∀ n, Measurable (fun ω => ∫ y, f y ∂(κ n ω : Measure Y)))
    (hprob : TendstoInMeasure μ (fun n ω => ∫ y, f y ∂(κ n ω : Measure Y))
      atTop (fun _ => ∫ y, f y ∂(ν : Measure Y)))
    (H : ℕ → Ω → ℂ) (hH : ∀ n, Measurable (H n)) (C : ℝ)
    (hC : ∀ n ω, ‖H n ω‖ ≤ C) :
    Tendsto (fun n =>
      (∫ ω, H n ω * Complex.ofReal (∫ y, f y ∂(κ n ω : Measure Y)) ∂μ) -
        (∫ ω, H n ω ∂μ) * Complex.ofReal (∫ y, f y ∂(ν : Measure Y))) atTop (𝓝 0) := by
  exact quenched_mark_factorization μ _ hq _ B
    (fun n ω => abs_mark_expectation_le (κ n ω) f B hB)
    (abs_mark_expectation_le ν f B hB) hprob H hH C hC

/-- Whenever the graph-state and joint product tests have limits, the stable
bound identifies their limiting product. No joint-limit independence is used
as a hypothesis. -/
theorem limit_product_test_factorization
    {u v : ℕ → ℂ} {a b c : ℂ}
    (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b))
    (hstable : Tendsto (fun n => u n - v n * c) atTop (𝓝 0)) :
    a = b * c := by
  have heq : a - b * c = 0 := tendsto_nhds_unique (hu.sub (hv.mul_const c)) hstable
  exact sub_eq_zero.mp heq

end ConditionalMarks
end GaussianWave
