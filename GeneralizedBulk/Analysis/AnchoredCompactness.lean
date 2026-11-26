import BourgadeHuang.AnchoredSequenceCompactness
import GeneralizedBulk.Analysis.CappedMomentTransfer

/-!
# Compactness of anchored counting states from their scalar anchor

The closed state inequalities bound each local particle count. Their bounded
anchor level sets are compact, including configurations with merged particles
and possible escaped affine mass. Analytic tightness follows from the actual
state-space topology rather than a separate normal-family assumption.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology ENNReal
namespace GeneralizedBulk.Analysis

/-- Bounded scalar anchors form compact subsets of the genuine anchored
counting-state space. -/
theorem isCompact_anchored_anchor_level (B : ℝ) :
    IsCompact {s : AnchoredCountingState | ‖s.val.2‖ ≤ B} := by
  let bounds : ℕ → ℕ := fun n => ⌈(1 + ((n : ℝ) + 1) ^ 2) * B⌉₊
  have hcount (s : AnchoredCountingState) (hs : ‖s.val.2‖ ≤ B) (n : ℕ) :
      s.val.1.measure (realAnnulus n) ≤ bounds n := by
    have hr : ∀ x ∈ realAnnulus n, |x| ≤ (n : ℝ) + 1 := by
      intro x hx
      exact abs_le_of_mem_realAnnulus hx
    have hreal : (s.val.1.measure (realAnnulus n)).toReal ≤ (bounds n : ℝ) := by
      calc
        _ ≤ (1 + ((n : ℝ) + 1) ^ 2) * ‖s.val.2‖ := s.count_le_anchor hr
        _ ≤ (1 + ((n : ℝ) + 1) ^ 2) * B := mul_le_mul_of_nonneg_left hs (by positivity)
        _ ≤ _ := Nat.le_ceil _
    exact (ENNReal.toReal_le_toReal (isCompact_realAnnulus n).measure_ne_top
      (ENNReal.natCast_ne_top (bounds n))).mp hreal
  have hcompact := isClosed_validAnchoredCountingState.isClosedEmbedding_subtypeVal.isCompact_preimage
    ((isCompact_annularCompactFamily bounds).prod (isCompact_closedBall (0 : ℂ) B))
  have hclosed : IsClosed {s : AnchoredCountingState | ‖s.val.2‖ ≤ B} :=
    isClosed_le (continuous_snd.comp continuous_subtype_val).norm continuous_const
  apply hcompact.of_isClosed_subset hclosed
  intro s hs
  exact ⟨mem_annularCompactFamily_of_count_le s.val.1 bounds (hcount s hs),
    by simpa only [Metric.mem_closedBall, dist_zero_right] using hs⟩

/-- A sequence of anchored laws is tight as soon as its actual anchor tails
are uniformly small. No compact particle-count hypothesis is added. -/
theorem isTightMeasureSet_anchored_of_uniform_anchor_tails
    (laws : ℕ → Measure AnchoredCountingState)
    (htail : ∀ epsilon : ℝ≥0∞, 0 < epsilon → ∃ B : ℝ,
      ∀ n, laws n {s | B < ‖s.val.2‖} ≤ epsilon) :
    IsTightMeasureSet (Set.range laws) := by
  rw [IsTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro epsilon hepsilon
  obtain ⟨B,hB⟩ := htail epsilon hepsilon
  refine ⟨{s : AnchoredCountingState | ‖s.val.2‖ ≤ B}, isCompact_anchored_anchor_level B, ?_⟩
  rintro _ ⟨n,rfl⟩
  simpa only [Set.compl_setOf, not_le] using hB n

/-- Scalar anchor tails yield an actual jointly weakly convergent
subsequence, retaining the counting configuration and escaped affine mass. -/
theorem anchored_laws_subsequence_of_uniform_anchor_tails
    (laws : ℕ → ProbabilityMeasure AnchoredCountingState)
    (htail : ∀ epsilon : ℝ≥0∞, 0 < epsilon → ∃ B : ℝ,
      ∀ n, (laws n : Measure AnchoredCountingState) {s | B < ‖s.val.2‖} ≤ epsilon) :
    ∃ (ν : ProbabilityMeasure AnchoredCountingState) (r : ℕ → ℕ), StrictMono r ∧
      Tendsto (laws ∘ r) atTop (𝓝 ν) := by
  letI : PolishSpace AnchoredCountingState := isClosed_validAnchoredCountingState.polishSpace
  let f := fun s : AnchoredCountingState => jointCountingCompactification s.val
  have he : Topology.IsEmbedding f :=
    isEmbedding_jointCountingCompactification.comp Topology.IsEmbedding.subtypeVal
  have hm : MeasurableEmbedding f := he.continuous.measurableEmbedding he.injective
  exact laws_subsequence_of_tight_compact_embedding f he hm laws
    (isTightMeasureSet_anchored_of_uniform_anchor_tails _ htail)

end GeneralizedBulk.Analysis
