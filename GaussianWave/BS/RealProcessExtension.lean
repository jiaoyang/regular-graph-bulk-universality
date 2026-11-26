import GaussianWave.BS.CompactProcessExtension

/-!
# Countable real-valued process extension

Arctangent compactification constructs the whole process from consistent
finite probability laws. Every compactified coordinate is almost surely
inside the actual real-coordinate image; countability recovers the whole
real-valued law. No moment or Gaussianity assumption is required.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical
namespace GaussianWave.BS

theorem measurableEmbedding_realProcessCompactification {I : Type*} [Countable I] :
    MeasurableEmbedding (finiteRealCompactification (ι := I)) :=
  continuous_finiteRealCompactification.measurableEmbedding injective_finiteRealCompactification

theorem exists_real_processLaw_of_finite_marginals
    {I : Type*} [Countable I]
    (P : ∀ S : Finset I, ProbabilityMeasure (S → ℝ))
    (hP : ∀ (S T : Finset I) (h : S ⊆ T),
      Measure.map (finiteSubrestriction (A := ℝ) h) (P T : Measure (T → ℝ)) =
        (P S : Measure (S → ℝ))) :
    ∃ Q : ProbabilityMeasure (I → ℝ), ∀ S : Finset I,
      Measure.map (finiteRestriction (A := ℝ) S) (Q : Measure (I → ℝ)) = (P S : Measure (S → ℝ)) := by
  let PC : ∀ S : Finset I, ProbabilityMeasure (S → CompactRealInterval) := fun S =>
    (P S).map (continuous_finiteRealCompactification (ι := S)).measurable.aemeasurable
  have hPC (S T : Finset I) (h : S ⊆ T) :
      Measure.map (finiteSubrestriction (A := CompactRealInterval) h) (PC T : Measure (T → CompactRealInterval)) =
        (PC S : Measure (S → CompactRealInterval)) := by
    change Measure.map (finiteSubrestriction (A := CompactRealInterval) h)
      (Measure.map (finiteRealCompactification (ι := T)) (P T : Measure (T → ℝ))) =
        Measure.map (finiteRealCompactification (ι := S)) (P S : Measure (S → ℝ))
    have hsubC : Measurable (finiteSubrestriction (A := CompactRealInterval) h) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply _)
    have hsubR : Measurable (finiteSubrestriction (A := ℝ) h) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply _)
    rw [Measure.map_map hsubC
      continuous_finiteRealCompactification.measurable]
    rw [← hP S T h, Measure.map_map continuous_finiteRealCompactification.measurable
      hsubR]
    rfl
  letI : Inhabited CompactRealInterval := ⟨compactifiedRealCoordinate 0⟩
  obtain ⟨QC, hQC⟩ := exists_processLaw_of_compact_finite_marginals PC hPC
  have hcoord (i : I) : ∀ᵐ x ∂(QC : Measure (I → CompactRealInterval)),
      x i ∈ Set.range compactifiedRealCoordinate := by
    let S : Finset I := {i}
    let j : S := ⟨i, by simp [S]⟩
    have ha : ∀ᵐ x ∂(PC S : Measure (S → CompactRealInterval)),
        x j ∈ Set.range compactifiedRealCoordinate := by
      change ∀ᵐ x ∂Measure.map (finiteRealCompactification (ι := S)) (P S : Measure (S → ℝ)), _
      apply (measurableEmbedding_finiteRealCompactification (ι := S)).ae_map_iff.mpr
      exact Filter.Eventually.of_forall (fun x => ⟨x j, rfl⟩)
    rw [← hQC S] at ha
    exact ae_of_ae_map (measurable_pi_lambda _ (fun i => measurable_pi_apply _)).aemeasurable ha
  have hall : ∀ᵐ x ∂(QC : Measure (I → CompactRealInterval)),
      ∀ i, x i ∈ Set.range compactifiedRealCoordinate := (ae_all_iff).mpr hcoord
  have hrange : ∀ᵐ x ∂(QC : Measure (I → CompactRealInterval)),
      x ∈ Set.range (finiteRealCompactification (ι := I)) := by
    filter_upwards [hall] with x hx
    refine ⟨fun i => Classical.choose (hx i), ?_⟩
    funext i
    exact Classical.choose_spec (hx i)
  have hzero : (QC : Measure (I → CompactRealInterval))
      (Set.range (finiteRealCompactification (ι := I)))ᶜ = 0 := ae_iff.mp hrange
  letI : MetricSpace (I → CompactRealInterval) :=
    TopologicalSpace.metrizableSpaceMetric (I → CompactRealInterval)
  let hf := measurableEmbedding_realProcessCompactification (I := I)
  let Q := embeddingPullbackLaw hf QC hzero
  have hQ : Measure.map (finiteRealCompactification (ι := I)) (Q : Measure (I → ℝ)) =
      (QC : Measure (I → CompactRealInterval)) :=
    congrArg (fun p : ProbabilityMeasure (I → CompactRealInterval) => (p : Measure (I → CompactRealInterval)))
      (map_embeddingPullbackLaw hf QC hzero)
  refine ⟨Q, ?_⟩
  intro S
  have hresC : Measurable (finiteRestriction (A := CompactRealInterval) S) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hresR : Measurable (finiteRestriction (A := ℝ) S) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have he : Measure.map (finiteRealCompactification (ι := S))
      (Measure.map (finiteRestriction (A := ℝ) S) (Q : Measure (I → ℝ))) =
        Measure.map (finiteRealCompactification (ι := S)) (P S : Measure (S → ℝ)) := by
    rw [Measure.map_map continuous_finiteRealCompactification.measurable hresR]
    have hcomp : finiteRealCompactification (ι := S) ∘ finiteRestriction (A := ℝ) S =
        finiteRestriction (A := CompactRealInterval) S ∘ finiteRealCompactification (ι := I) := rfl
    rw [hcomp, ← Measure.map_map hresC
      continuous_finiteRealCompactification.measurable, hQ, hQC S]
    rfl
  have he' := congrArg (Measure.comap (finiteRealCompactification (ι := S))) he
  simpa only [(measurableEmbedding_finiteRealCompactification (ι := S)).comap_map] using he'

end GaussianWave.BS
