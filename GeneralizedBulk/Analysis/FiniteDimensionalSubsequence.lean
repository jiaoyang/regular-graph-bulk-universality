import BourgadeHuang.CountingLawSubsequence
import GeneralizedBulk.Gaussian.UniformIntegrability

/-!
# Actual finite-dimensional weak subsequences from fourth moments

We reuse the proved compact-law subsequence theorem from the characterization
repository. Coordinatewise arctangent supplies the compact embedding, and
Markov's inequality supplies tightness. No subsequence-existence hypothesis is
added to the graph Gaussian limit theorem.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology BigOperators ENNReal

namespace GeneralizedBulk.Analysis

def finiteRealCompactification {ι : Type*} (x : ι → ℝ) : ι → CountingCoordinateInterval :=
  fun i => compactifiedRealCoordinate (x i)

theorem continuous_finiteRealCompactification {ι : Type*} :
    Continuous (finiteRealCompactification (ι := ι)) :=
  continuous_pi (fun i => isEmbedding_compactifiedRealCoordinate.continuous.comp (continuous_apply i))

theorem injective_finiteRealCompactification {ι : Type*} :
    Function.Injective (finiteRealCompactification (ι := ι)) := by
  intro x y h
  funext i
  exact isEmbedding_compactifiedRealCoordinate.injective (congrFun h i)

theorem isEmbedding_finiteRealCompactification {ι : Type*} :
    Topology.IsEmbedding (finiteRealCompactification (ι := ι)) := by
  refine ⟨⟨?_⟩, injective_finiteRealCompactification⟩
  rw [induced_to_pi]
  change (⨅ i : ι, TopologicalSpace.induced (fun x : ι → ℝ => x i) inferInstance) = _
  congr 1
  funext i
  exact (congrArg (TopologicalSpace.induced (fun x : ι → ℝ => x i))
    isEmbedding_compactifiedRealCoordinate.isInducing.eq_induced).trans (by
      rw [induced_compose]
      rfl)

theorem measurableEmbedding_finiteRealCompactification {ι : Type*} [Fintype ι] :
    MeasurableEmbedding (finiteRealCompactification (ι := ι)) :=
  continuous_finiteRealCompactification.measurableEmbedding injective_finiteRealCompactification

theorem isTightMeasureSet_of_uniform_norm_fourth
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (hi : ∀ n, Integrable (fun x => ‖x‖ ^ 4) (μ n)) (M : ℝ)
    (hM : ∀ n, (∫ x, ‖x‖ ^ 4 ∂μ n) ≤ M) :
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
    (μ := μ n) (Eventually.of_forall (fun x => by positivity : ∀ x : E, 0 ≤ ‖x‖ ^ 4)) (hi n) (B : ℝ)
  have htail : (μ n {x | (B : ℝ) ≤ ‖x‖ ^ 4}).toReal ≤ ε.toReal := by
    change (B : ℝ) * (μ n {x | (B : ℝ) ≤ ‖x‖ ^ 4}).toReal ≤ _ at hMarkov
    nlinarith [hM n]
  have hsub : (Metric.closedBall (0 : E) ((B : ℝ) + 1))ᶜ ⊆ {x | (B : ℝ) ≤ ‖x‖ ^ 4} := by
    intro x hx
    have hn : (B : ℝ) + 1 < ‖x‖ := by
      simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hx
    have hn1 : 1 ≤ ‖x‖ := by linarith [Nat.cast_nonneg (α := ℝ) B]
    have hn2 : 1 ≤ ‖x‖ ^ 2 := by nlinarith
    have hp := mul_nonneg (sq_nonneg ‖x‖) (sub_nonneg.mpr hn2)
    change (B : ℝ) ≤ ‖x‖ ^ 4
    nlinarith
  calc
    _ ≤ μ n {x | (B : ℝ) ≤ ‖x‖ ^ 4} := measure_mono hsub
    _ = ENNReal.ofReal ((μ n {x | (B : ℝ) ≤ ‖x‖ ^ 4}).toReal) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal htail
    _ = ε := ENNReal.ofReal_toReal htop

/-- An actual weakly convergent subsequence exists for every finite-dimensional
probability-law sequence with a uniform fourth-norm moment. -/
theorem finite_laws_subsequence_of_uniform_norm_fourth
    {ι : Type*} [Fintype ι] (μ : ℕ → ProbabilityMeasure (ι → ℝ))
    (hi : ∀ n, Integrable (fun x => ‖x‖ ^ 4) (μ n : Measure (ι → ℝ))) (M : ℝ)
    (hM : ∀ n, (∫ x, ‖x‖ ^ 4 ∂(μ n : Measure (ι → ℝ))) ≤ M) :
    ∃ (ν : ProbabilityMeasure (ι → ℝ)) (r : ℕ → ℕ), StrictMono r ∧
      Tendsto (μ ∘ r) atTop (𝓝 ν) := by
  exact laws_subsequence_of_tight_compact_embedding finiteRealCompactification
    isEmbedding_finiteRealCompactification measurableEmbedding_finiteRealCompactification μ
    (isTightMeasureSet_of_uniform_norm_fourth (fun n => (μ n : Measure (ι → ℝ))) hi M hM)

end GeneralizedBulk.Analysis
