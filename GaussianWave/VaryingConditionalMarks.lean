import GaussianWave.ConditionalMarks

/-!
# Stable conditional mark tests on size-dependent graph spaces

The graph sample space and its probability measure may change with the graph
size. Explicit exceptional-event convergence is enough: bounded conditional
test errors converge in L1, and their products with uniformly bounded complex
graph-state tests factorize. Both conclusions are proved by the event split.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GaussianWave.VaryingConditionalMarks

/-- Convergence in probability on varying probability spaces, expressed by
actual positive-threshold exceptional-event probabilities. -/
def ErrorInProbability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (q : ∀ n, Ω n → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun n => (P n {ω | ε ≤ |q n ω - c|}).toReal) atTop (𝓝 0)

/-- Bounded errors converging in probability converge in actual L1, even
though neither the graph spaces nor the graph laws are fixed. -/
theorem integral_abs_error_tendsto_zero
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (q : ∀ n, Ω n → ℝ) (hq : ∀ n, Measurable (q n)) (c B : ℝ)
    (hB : ∀ n ω, |q n ω| ≤ B) (hc : |c| ≤ B)
    (hprob : ErrorInProbability P q c) :
    Tendsto (fun n => ∫ ω, |q n ω - c| ∂P n) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n =>
      ha.trans_le (integral_nonneg (fun ω => abs_nonneg _))
  · intro b hb
    have hbad := hprob (b / 2) (by linarith)
    have htail : ∀ᶠ n in atTop,
        2 * B * (P n {ω | b / 2 ≤ |q n ω - c|}).toReal < b / 2 := by
      apply (tendsto_order.mp (show Tendsto
        (fun n => 2 * B * (P n {ω | b / 2 ≤ |q n ω - c|}).toReal)
          atTop (𝓝 0) from
        by simpa only [mul_zero] using hbad.const_mul (2 * B))).2
      linarith
    filter_upwards [htail] with n hn
    have he := ConditionalMarks.integral_abs_error_event_bound (P n) (q n) (hq n)
      c B (hB n) hc (b / 2) (by linarith)
    linarith

/-- Stable product-test factorization against arbitrary measurable uniformly
bounded complex functions of the graph, with size-dependent graph spaces. -/
theorem bounded_graph_test_factorization
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (q : ∀ n, Ω n → ℝ) (hq : ∀ n, Measurable (q n)) (c B : ℝ)
    (hB : ∀ n ω, |q n ω| ≤ B) (hc : |c| ≤ B)
    (hprob : ErrorInProbability P q c)
    (H : ∀ n, Ω n → ℂ) (hH : ∀ n, Measurable (H n))
    (C : ℝ) (hC : ∀ n ω, ‖H n ω‖ ≤ C) :
    Tendsto (fun n =>
      (∫ ω, H n ω * (q n ω : ℂ) ∂P n) -
        (∫ ω, H n ω ∂P n) * (c : ℂ)) atTop (𝓝 0) := by
  have hL1 := integral_abs_error_tendsto_zero P q hq c B hB hc hprob
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => ConditionalMarks.bounded_graph_test_error_bound (P n) (q n) (hq n)
      c B (hB n) hc (H n) (hH n) C (hC n))
  simpa only [mul_zero] using hL1.const_mul C

/-- Actual conditional mark probability laws on a changing graph space give
L1 convergence of bounded mark-test expectations. -/
theorem conditional_mark_law_L1
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {Y : Type*} [MeasurableSpace Y]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (κ : ∀ n, Ω n → ProbabilityMeasure Y) (ν : ProbabilityMeasure Y)
    (f : Y → ℝ) (B : ℝ) (hB : ∀ y, |f y| ≤ B)
    (hq : ∀ n, Measurable (fun ω => ∫ y, f y ∂(κ n ω : Measure Y)))
    (hprob : ErrorInProbability P (fun n ω => ∫ y, f y ∂(κ n ω : Measure Y))
      (∫ y, f y ∂(ν : Measure Y))) :
    Tendsto (fun n => ∫ ω,
      |(∫ y, f y ∂(κ n ω : Measure Y)) - ∫ y, f y ∂(ν : Measure Y)| ∂P n)
      atTop (𝓝 0) := by
  exact integral_abs_error_tendsto_zero P _ hq _ B
    (fun n ω => ConditionalMarks.abs_mark_expectation_le (κ n ω) f B hB)
    (ConditionalMarks.abs_mark_expectation_le ν f B hB) hprob

/-- Conditional expectation product tests factorize on actual varying graph
spaces. This supplies the stable marked-limit interface without putting the
graphs of every size on one artificial common probability space. -/
theorem conditional_mark_law_factorization
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {Y : Type*} [MeasurableSpace Y]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (κ : ∀ n, Ω n → ProbabilityMeasure Y) (ν : ProbabilityMeasure Y)
    (f : Y → ℝ) (B : ℝ) (hB : ∀ y, |f y| ≤ B)
    (hq : ∀ n, Measurable (fun ω => ∫ y, f y ∂(κ n ω : Measure Y)))
    (hprob : ErrorInProbability P (fun n ω => ∫ y, f y ∂(κ n ω : Measure Y))
      (∫ y, f y ∂(ν : Measure Y)))
    (H : ∀ n, Ω n → ℂ) (hH : ∀ n, Measurable (H n))
    (C : ℝ) (hC : ∀ n ω, ‖H n ω‖ ≤ C) :
    Tendsto (fun n =>
      (∫ ω, H n ω * Complex.ofReal (∫ y, f y ∂(κ n ω : Measure Y)) ∂P n) -
        (∫ ω, H n ω ∂P n) * Complex.ofReal (∫ y, f y ∂(ν : Measure Y)))
      atTop (𝓝 0) := by
  exact bounded_graph_test_factorization P _ hq _ B
    (fun n ω => ConditionalMarks.abs_mark_expectation_le (κ n ω) f B hB)
    (ConditionalMarks.abs_mark_expectation_le ν f B hB) hprob H hH C hC

/-- Once the marginal graph-state and joint test expectations have limits,
stable factorization identifies their limiting product. -/
theorem limit_product_test_factorization
    {u v : ℕ → ℂ} {a b c : ℂ}
    (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b))
    (hstable : Tendsto (fun n => u n - v n * c) atTop (𝓝 0)) : a = b * c :=
  ConditionalMarks.limit_product_test_factorization hu hv hstable

end GaussianWave.VaryingConditionalMarks
