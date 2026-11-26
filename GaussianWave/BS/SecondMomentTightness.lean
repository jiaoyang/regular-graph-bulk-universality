import GaussianWave.Compactness

/-! Qualitative compactness uses second moments only. Fourth moments are not
assumed in the BS limit construction, and second moments may decrease in a
weak limit. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace GaussianWave.BS

theorem isTightMeasureSet_of_uniform_norm_second
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (hi : ∀ n, Integrable (fun x => ‖x‖ ^ 2) (μ n)) (M : ℝ)
    (hM : ∀ n, (∫ x, ‖x‖ ^ 2 ∂μ n) ≤ M) :
    IsTightMeasureSet (Set.range μ) := by
  rw [IsTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases htop : ε = ∞
  · exact ⟨∅, isCompact_empty, fun η hη => by simp [htop]⟩
  have hδ : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨B, hB⟩ := exists_nat_gt (max 0 (M / ε.toReal))
  have hBpos : 0 < (B : ℝ) := (le_max_left _ _).trans_lt hB
  have hMB : M ≤ (B : ℝ) * ε.toReal :=
    ((div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hB)).le
  refine ⟨Metric.closedBall 0 ((B : ℝ) + 1), isCompact_closedBall _ _, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ n) (Eventually.of_forall (fun x : E => sq_nonneg ‖x‖)) (hi n) (B : ℝ)
  have htail : (μ n {x | (B : ℝ) ≤ ‖x‖ ^ 2}).toReal ≤ ε.toReal := by
    change (B : ℝ) * (μ n {x | (B : ℝ) ≤ ‖x‖ ^ 2}).toReal ≤ _ at hMarkov
    nlinarith [hM n]
  have hsub : (Metric.closedBall (0 : E) ((B : ℝ) + 1))ᶜ ⊆ {x | (B : ℝ) ≤ ‖x‖ ^ 2} := by
    intro x hx
    have hn : (B : ℝ) + 1 < ‖x‖ := by
      simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hx
    have hn1 : 1 ≤ ‖x‖ := by linarith [Nat.cast_nonneg (α := ℝ) B]
    change (B : ℝ) ≤ ‖x‖ ^ 2
    nlinarith
  calc
    _ ≤ μ n {x | (B : ℝ) ≤ ‖x‖ ^ 2} := measure_mono hsub
    _ = ENNReal.ofReal ((μ n {x | (B : ℝ) ≤ ‖x‖ ^ 2}).toReal) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal htail
    _ = ε := ENNReal.ofReal_toReal htop

theorem finite_laws_subsequence_of_uniform_norm_second
    {I : Type*} [Fintype I] (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (hi : ∀ n, Integrable (fun x => ‖x‖ ^ 2) (μ n : Measure (I → ℝ))) (M : ℝ)
    (hM : ∀ n, (∫ x, ‖x‖ ^ 2 ∂(μ n : Measure (I → ℝ))) ≤ M) :
    ∃ (ν : ProbabilityMeasure (I → ℝ)) (r : ℕ → ℕ), StrictMono r ∧
      Tendsto (μ ∘ r) atTop (𝓝 ν) := by
  exact laws_subsequence_of_tight_compact_embedding finiteRealCompactification
    isEmbedding_finiteRealCompactification measurableEmbedding_finiteRealCompactification μ
    (isTightMeasureSet_of_uniform_norm_second (fun n => (μ n : Measure (I → ℝ))) hi M hM)

/-- A continuous nonnegative moment is bounded in the weak limit. This
allows loss of variance and establishes genuine integrability of the limit. -/
theorem integrable_and_integral_le_of_weak_nonneg
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → ProbabilityMeasure E) (ν : ProbabilityMeasure E)
    (hweak : Tendsto μ atTop (𝓝 ν)) (f : E → ℝ) (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) (hi : ∀ n, Integrable f (μ n : Measure E))
    (M : ℝ) (hM : ∀ n, (∫ x, f x ∂(μ n : Measure E)) ≤ M) :
    Integrable f (ν : Measure E) ∧ (∫ x, f x ∂(ν : Measure E)) ≤ M := by
  have hM0 : 0 ≤ M := (integral_nonneg hf0).trans (hM 0)
  have hopen : ∀ U, IsOpen U → (ν : Measure E) U ≤
      atTop.liminf (fun n => (μ n : Measure E) U) :=
    fun U hU => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hU
  have hFatou := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure hf hf0 hopen
  have hbound : ∀ n, (∫⁻ x, ENNReal.ofReal (f x) ∂(μ n : Measure E)) ≤ ENNReal.ofReal M := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall hf0)]
    exact ENNReal.ofReal_le_ofReal (hM n)
  have hL : (∫⁻ x, ENNReal.ofReal (f x) ∂(ν : Measure E)) ≤ ENNReal.ofReal M :=
    hFatou.trans (liminf_le_of_frequently_le (Eventually.of_forall hbound).frequently)
  have hfinite : (∫⁻ x, ENNReal.ofReal (f x) ∂(ν : Measure E)) < ∞ :=
    hL.trans_lt ENNReal.ofReal_lt_top
  have hfi : Integrable f (ν : Measure E) := by
    exact ⟨hf.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf0)).mpr hfinite⟩
  refine ⟨hfi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall hf0)] at hL
  exact (ENNReal.ofReal_le_ofReal_iff hM0).mp hL

end GaussianWave.BS
