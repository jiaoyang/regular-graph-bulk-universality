import GeneralizedBulk.Gaussian.WeakCharacteristic

/-!
# Uniform good-graph convergence and full scalar-state factorization

Convergence for every admissible deterministic graph/selection sequence implies
uniform convergence on the common good event. Uniformity then permits arbitrary
bounded measurable scalar-state tests, including tests of the real anchor.
There is no assumption of conditional independence given only the counting
measure.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology Classical

namespace GeneralizedBulk.Graph

theorem uniform_on_good_of_all_sequences_dependent {S : ℕ → Type*} [∀ n, Nonempty (S n)]
    (good : ∀ n, Set (S n)) (f : ∀ n, S n → ℝ) (c : ℝ)
    (hne : ∀ᶠ n in atTop, (good n).Nonempty)
    (hseq : ∀ x : ∀ n, S n, (∀ᶠ n in atTop, x n ∈ good n) →
      Tendsto (fun n => f n (x n)) atTop (𝓝 c)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ good n, |f n x - c| < ε := by
  intro ε hε
  by_contra hnot
  have hbad : ∃ᶠ n in atTop, ∃ x ∈ good n, ε ≤ |f n x - c| := by
    simpa only [not_eventually, not_forall, not_lt, exists_prop] using hnot
  let fallback : ∀ n, S n := fun n =>
    if h : (good n).Nonempty then Classical.choose h else Classical.choice inferInstance
  have hfallback : ∀ᶠ n in atTop, fallback n ∈ good n := by
    filter_upwards [hne] with n hn
    simpa only [fallback, dif_pos hn] using Classical.choose_spec hn
  let x : ∀ n, S n := fun n =>
    if h : ∃ y ∈ good n, ε ≤ |f n y - c| then Classical.choose h else fallback n
  have hx : ∀ᶠ n in atTop, x n ∈ good n := by
    filter_upwards [hfallback] with n hn
    by_cases hb : ∃ y ∈ good n, ε ≤ |f n y - c|
    · simpa only [x, dif_pos hb] using (Classical.choose_spec hb).1
    · simpa only [x, dif_neg hb] using hn
  have hfreq : ∃ᶠ n in atTop, ε ≤ |f n (x n) - c| := by
    apply hbad.mono
    intro n hn
    simpa only [x, dif_pos hn] using (Classical.choose_spec hn).2
  have hsmall : ∀ᶠ n in atTop, |f n (x n) - c| < ε := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp (hseq x hx)) ε hε
  obtain ⟨n, hn, hn'⟩ := (hfreq.and_eventually hsmall).exists
  exact (not_lt_of_ge hn) hn'

theorem uniform_on_good_of_all_sequences {S : Type*} [Nonempty S]
    (good : ℕ → Set S) (f : ℕ → S → ℝ) (c : ℝ)
    (hne : ∀ᶠ n in atTop, (good n).Nonempty)
    (hseq : ∀ x : ℕ → S, (∀ᶠ n in atTop, x n ∈ good n) →
      Tendsto (fun n => f n (x n)) atTop (𝓝 c)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ good n, |f n x - c| < ε :=
  uniform_on_good_of_all_sequences_dependent (S := fun _ => S) good f c hne hseq

theorem integrable_abs_bounded_error {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] (f : S → ℝ) (hf : Measurable f)
    (c B : ℝ) (hB : ∀ x, |f x| ≤ B) (hc : |c| ≤ B) :
    Integrable (fun x => |f x - c|) μ := by
  apply (integrable_const (2 * B)).mono' ((hf.sub_const c).abs.aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_abs]
  exact (abs_sub (f x) c).trans (by linarith [hB x, hc])

theorem integral_abs_error_good_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (good : Set S) (hgood : MeasurableSet good)
    (f : S → ℝ) (hf : Measurable f) (c B : ℝ) (hB : ∀ x, |f x| ≤ B) (hc : |c| ≤ B)
    (ε : ℝ) (hε : 0 ≤ ε) (hsmall : ∀ x ∈ good, |f x - c| ≤ ε) :
    (∫ x, |f x - c| ∂μ) ≤ ε + 2 * B * (μ goodᶜ).toReal := by
  have hi := integrable_abs_bounded_error μ f hf c B hB hc
  have hInd : Integrable (goodᶜ.indicator (fun _ : S => (1 : ℝ))) μ :=
    (integrable_const _).indicator hgood.compl
  have hbound : ∀ x, |f x - c| ≤ ε + 2 * B * goodᶜ.indicator (fun _ : S => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ good
    · simpa [Set.indicator_of_not_mem, hx] using hsmall x hx
    · have he := (abs_sub (f x) c).trans (add_le_add (hB x) hc)
      simpa [Set.indicator_of_mem, hx] using he.trans (by linarith : B + B ≤ ε + 2 * B)
  calc
    _ ≤ ∫ x, ε + 2 * B * goodᶜ.indicator (fun _ : S => (1 : ℝ)) x ∂μ :=
      integral_mono hi ((integrable_const _).add (hInd.const_mul _)) hbound
    _ = _ := by
      rw [integral_add (integrable_const _) (hInd.const_mul _), integral_const_mul,
        integral_indicator hgood.compl]
      simp [measureReal_def]

theorem integral_abs_error_tendsto_zero {S : Type*} [MeasurableSpace S]
    (μ : ℕ → Measure S) [∀ n, IsProbabilityMeasure (μ n)]
    (good : ℕ → Set S) (hgood : ∀ n, MeasurableSet (good n))
    (f : ℕ → S → ℝ) (hf : ∀ n, Measurable (f n)) (c B : ℝ)
    (hB : ∀ n x, |f n x| ≤ B) (hc : |c| ≤ B)
    (huniform : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ good n, |f n x - c| < ε)
    (hbad : Tendsto (fun n => (μ n (good n)ᶜ).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, |f n x - c| ∂μ n) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (integral_nonneg (fun x => abs_nonneg _)))
  · intro b hb
    have ht : Tendsto (fun n => 2 * B * (μ n (good n)ᶜ).toReal) atTop (𝓝 0) := by
      simpa only [mul_zero] using hbad.const_mul (2 * B)
    have htail := (tendsto_order.mp ht).2 (b / 2) (by linarith)
    filter_upwards [huniform (b / 2) (by linarith), htail] with n hn htn
    have he := integral_abs_error_good_bound (μ n) (good n) (hgood n) (f n) (hf n) c B
      (hB n) hc (b / 2) (by linarith) (fun x hx => (hn x hx).le)
    linarith

/-- Full scalar-state tests factor from the limiting mark expectation. The
bounded test `H` may depend measurably on the entire graph-derived state,
including the anchor real part, and may vary with the graph size. -/
theorem bounded_scalar_mark_factorization {S : Type*} [MeasurableSpace S]
    (μ : ℕ → Measure S) [∀ n, IsProbabilityMeasure (μ n)]
    (good : ℕ → Set S) (hgood : ∀ n, MeasurableSet (good n))
    (f : ℕ → S → ℝ) (hf : ∀ n, Measurable (f n)) (c B : ℝ)
    (hB : ∀ n x, |f n x| ≤ B) (hc : |c| ≤ B)
    (huniform : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ good n, |f n x - c| < ε)
    (hbad : Tendsto (fun n => (μ n (good n)ᶜ).toReal) atTop (𝓝 0))
    (H : ℕ → S → ℂ) (hH : ∀ n, Measurable (H n)) (C : ℝ)
    (hC : ∀ n x, ‖H n x‖ ≤ C) :
    Tendsto (fun n => (∫ x, H n x * (f n x : ℂ) ∂μ n) - (∫ x, H n x ∂μ n) * (c : ℂ))
      atTop (𝓝 0) := by
  have hErr := integral_abs_error_tendsto_zero μ good hgood f hf c B hB hc huniform hbad
  have hnorm (n : ℕ) :
      ‖(∫ x, H n x * (f n x : ℂ) ∂μ n) - (∫ x, H n x ∂μ n) * (c : ℂ)‖ ≤
        C * ∫ x, |f n x - c| ∂μ n := by
    have hiH : Integrable (H n) (μ n) :=
      (integrable_const C).mono' (hH n).aestronglyMeasurable (Eventually.of_forall (hC n))
    have hiP : Integrable (fun x => H n x * (f n x : ℂ)) (μ n) := by
      apply (integrable_const (C * B)).mono' ((hH n).mul (hf n).complex_ofReal).aestronglyMeasurable
      filter_upwards [] with x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hC n x) (hB n x) (abs_nonneg _) ((norm_nonneg _).trans (hC n x))
    have hiE := integrable_abs_bounded_error (μ n) (f n) (hf n) c B (hB n) hc
    have heq : (∫ x, H n x * (f n x : ℂ) ∂μ n) - (∫ x, H n x ∂μ n) * (c : ℂ) =
        ∫ x, H n x * ((f n x - c : ℝ) : ℂ) ∂μ n := by
      rw [← integral_mul_const, ← integral_sub hiP (hiH.mul_const (c : ℂ))]
      apply integral_congr_ae
      filter_upwards [] with x
      push_cast
      ring
    rw [heq]
    have hiG : Integrable (fun x => H n x * ((f n x - c : ℝ) : ℂ)) (μ n) := by
      convert hiP.sub (hiH.mul_const (c : ℂ)) using 1
      funext x
      simp only [Pi.sub_apply]
      push_cast
      ring
    calc
      _ ≤ ∫ x, ‖H n x * ((f n x - c : ℝ) : ℂ)‖ ∂μ n := norm_integral_le_integral_norm _
      _ ≤ ∫ x, C * |f n x - c| ∂μ n := integral_mono hiG.norm (hiE.const_mul C) (fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hC n x) (abs_nonneg _))
      _ = _ := integral_const_mul _ _
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) hnorm
  simpa only [mul_zero] using hErr.const_mul C

end GeneralizedBulk.Graph
