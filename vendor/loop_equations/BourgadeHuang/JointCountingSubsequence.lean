import BourgadeHuang.CountingLawSubsequence

/-!
# Joint vague and resolvent-anchor subsequences

Uniform compact counting moments and a uniform second moment of a complex anchor
produce a jointly weakly convergent subsequence of counting configurations and
complex anchors.
-/
noncomputable section
open scoped Topology ENNReal BoundedContinuousFunction
open MeasureTheory Filter Set

namespace BourgadeHuang

/-- A compactification of the real and imaginary parts of a complex anchor. -/
def complexCompactification (z : ℂ) : CountingCoordinateInterval × CountingCoordinateInterval :=
  (compactifiedRealCoordinate z.re, compactifiedRealCoordinate z.im)

theorem isEmbedding_complexCompactification : Topology.IsEmbedding complexCompactification :=
  (isEmbedding_compactifiedRealCoordinate.prodMap isEmbedding_compactifiedRealCoordinate).comp
    Complex.equivRealProdCLM.toHomeomorph.isEmbedding

/-- Configuration together with one complex resolvent value. -/
abbrev JointCountingState := LocalCountingMeasure × ℂ

/-- The joint compactification is a genuine embedding into a compact metric space. -/
def jointCountingCompactification : JointCountingState →
    CountingCompactCube × (CountingCoordinateInterval × CountingCoordinateInterval) :=
  Prod.map countingCompactification complexCompactification

theorem isEmbedding_jointCountingCompactification :
    Topology.IsEmbedding jointCountingCompactification :=
  isEmbedding_countingCompactification.prodMap isEmbedding_complexCompactification

theorem measurableEmbedding_jointCountingCompactification :
    MeasurableEmbedding jointCountingCompactification :=
  isEmbedding_jointCountingCompactification.continuous.measurableEmbedding
    isEmbedding_jointCountingCompactification.injective

/-- A single compact set captures both the configuration and the anchor. -/
theorem exists_compact_joint_capture_of_moments
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (ξ : ℕ → Ω → LocalCountingMeasure) (z : ℕ → Ω → ℂ)
    (hc : UniformCountMoments μ ξ)
    (hi : ∀ N, Integrable (fun ω => ‖z N ω‖ ^ 2) μ)
    (C : ℝ) (hC : ∀ N, (∫ ω, ‖z N ω‖ ^ 2 ∂μ) ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set JointCountingState, IsCompact K ∧
      ∀ N, μ ((fun ω => (ξ N ω, z N ω)) ⁻¹' Kᶜ) ≤ ENNReal.ofReal ε := by
  obtain ⟨K, hK, hcapture⟩ := exists_compact_capture_of_uniformCountMoments ξ hc (half_pos hε)
  obtain ⟨B, hB⟩ := exists_nat_uniform_tail_bound (fun N ω => ‖z N ω‖ ^ 2)
    (fun _ _ => sq_nonneg _) hi C hC (half_pos hε)
  let L : Set ℂ := Metric.closedBall 0 ((B : ℝ) + 1)
  refine ⟨K ×ˢ L, hK.prod (isCompact_closedBall _ _), fun N => ?_⟩
  have hsub : (fun ω => (ξ N ω, z N ω)) ⁻¹' (K ×ˢ L)ᶜ ⊆
      (ξ N ⁻¹' Kᶜ) ∪ {ω | (B : ℝ) < ‖z N ω‖ ^ 2} := by
    intro ω hω
    by_cases hξ : ξ N ω ∈ K
    · right
      have hn : (B : ℝ) + 1 < ‖z N ω‖ := by
        apply lt_of_not_ge
        intro hh
        apply hω
        exact ⟨hξ, by simpa [L, Metric.mem_closedBall, dist_zero_right] using hh⟩
      change (B : ℝ) < ‖z N ω‖ ^ 2
      have hn1 : 1 ≤ ‖z N ω‖ := by linarith [Nat.cast_nonneg (α := ℝ) B]
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (norm_nonneg (z N ω))]
    · exact Or.inl hξ
  calc
    μ ((fun ω => (ξ N ω, z N ω)) ⁻¹' (K ×ˢ L)ᶜ) ≤
        μ ((ξ N ⁻¹' Kᶜ) ∪ {ω | (B : ℝ) < ‖z N ω‖ ^ 2}) := measure_mono hsub
    _ ≤ μ (ξ N ⁻¹' Kᶜ) + μ {ω | (B : ℝ) < ‖z N ω‖ ^ 2} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add (hcapture N) (hB N)
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; congr 1; ring

/-- The joint laws are tight, with compact capture derived from the two moment estimates. -/
theorem isTightMeasureSet_joint_of_moments
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (ξ : ℕ → Ω → LocalCountingMeasure) (z : ℕ → Ω → ℂ)
    (hξ : ∀ N, Measurable (ξ N)) (hz : ∀ N, Measurable (z N))
    (hc : UniformCountMoments μ ξ)
    (hi : ∀ N, Integrable (fun ω => ‖z N ω‖ ^ 2) μ)
    (C : ℝ) (hC : ∀ N, (∫ ω, ‖z N ω‖ ^ 2 ∂μ) ≤ C) :
    IsTightMeasureSet (Set.range (fun N => Measure.map (fun ω => (ξ N ω, z N ω)) μ)) := by
  rw [IsTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases htop : ε = ∞
  · exact ⟨∅, isCompact_empty, fun _ _ => by simp [htop]⟩
  obtain ⟨K, hK, hcapture⟩ := exists_compact_joint_capture_of_moments ξ z hc hi C hC
    (ENNReal.toReal_pos hε.ne' htop)
  refine ⟨K, hK, ?_⟩
  rintro _ ⟨N, rfl⟩
  rw [Measure.map_apply ((hξ N).prodMk (hz N)) hK.measurableSet.compl]
  simpa only [ENNReal.ofReal_toReal htop] using hcapture N

/-- Uniform compact count moments and one scalar second moment give actual joint
subsequential convergence, tested against every bounded continuous state observable. -/
theorem exists_joint_subsequence_of_moments
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → LocalCountingMeasure) (z : ℕ → Ω → ℂ)
    (hξ : ∀ N, Measurable (ξ N)) (hz : ∀ N, Measurable (z N))
    (hc : UniformCountMoments μ ξ)
    (hi : ∀ N, Integrable (fun ω => ‖z N ω‖ ^ 2) μ)
    (C : ℝ) (hC : ∀ N, (∫ ω, ‖z N ω‖ ^ 2 ∂μ) ≤ C) :
    ∃ (ν : ProbabilityMeasure JointCountingState) (r : ℕ → ℕ), StrictMono r ∧
      ∀ F : JointCountingState →ᵇ ℝ,
        Tendsto (fun N => ∫ ω, F (ξ (r N) ω, z (r N) ω) ∂μ) atTop
          (𝓝 (∫ c, F c ∂(ν : Measure JointCountingState))) := by
  let laws : ℕ → ProbabilityMeasure JointCountingState := fun N =>
    ProbabilityMeasure.map (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω)
      ((hξ N).prodMk (hz N)).aemeasurable
  have ht : IsTightMeasureSet (Set.range (fun n => (laws n : Measure JointCountingState))) :=
    isTightMeasureSet_joint_of_moments ξ z hξ hz hc hi C hC
  obtain ⟨ν, r, hr, hlim⟩ := laws_subsequence_of_tight_compact_embedding jointCountingCompactification
    isEmbedding_jointCountingCompactification measurableEmbedding_jointCountingCompactification laws ht
  refine ⟨ν, r, hr, fun F => ?_⟩
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim F
  have he (N : ℕ) : (∫ c, F c ∂(laws (r N) : Measure JointCountingState)) =
      ∫ ω, F (ξ (r N) ω, z (r N) ω) ∂μ := by
    exact integral_map ((hξ (r N)).prodMk (hz (r N))).aemeasurable F.continuous.aestronglyMeasurable
  simpa only [Function.comp_apply, he] using hh

end BourgadeHuang
