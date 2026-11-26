import GaussianWave.BS.RealProcessExtension
import GaussianWave.BS.SecondMomentTightness
import GaussianWave.BS.WeakEigenrelations

/-! Genuine weak compactness for countable real processes from coordinate
second moments alone. Compactification is applied to the whole process;
coordinate tightness proves that the limit has no compactification-boundary
mass, and the actual real-valued process law is recovered. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical
namespace GaussianWave.BS

/-- A countable real-process sequence with uniformly bounded second moment
in each coordinate has an actual whole-process weakly convergent subsequence. -/
theorem process_laws_subsequence_of_uniform_coordinate_second
    {I : Type*} [Countable I] (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (hi : ∀ n i, Integrable (fun x => x i^2) (μ n : Measure (I → ℝ)))
    (M : I → ℝ) (hM : ∀ n i, (∫ x, x i^2 ∂(μ n : Measure (I → ℝ)))≤M i) :
    ∃ (ν : ProbabilityMeasure (I → ℝ)) (r : ℕ → ℕ), StrictMono r ∧
      Tendsto (μ ∘ r) atTop (𝓝 ν) := by
  letI : MetricSpace (I → CompactRealInterval) :=
    TopologicalSpace.metrizableSpaceMetric (I → CompactRealInterval)
  let F := finiteRealCompactification (ι := I)
  have hF : Continuous F := continuous_finiteRealCompactification
  let PC : ℕ → ProbabilityMeasure (I → CompactRealInterval) := fun n => μ n |>.map hF.measurable.aemeasurable
  obtain ⟨QC,r,hr,hconv⟩ := compact_probability_laws_subsequence PC
  have hcoord (i : I) : ∀ᵐ x ∂(QC : Measure (I → CompactRealInterval)),
      x i ∈ Set.range compactifiedRealCoordinate := by
    let ev := fun x : I → ℝ => x i
    let evC := fun x : I → CompactRealInterval => x i
    have hev : Continuous ev := continuous_apply i
    have hevC : Continuous evC := continuous_apply i
    let marg : ℕ → ProbabilityMeasure ℝ := fun n => μ n |>.map hev.measurable.aemeasurable
    let limit : ProbabilityMeasure CompactRealInterval := QC.map hevC.measurable.aemeasurable
    have hmi (n : ℕ) : Integrable (fun x : ℝ => ‖x‖^2) (marg n : Measure ℝ) := by
      change Integrable (fun x : ℝ => ‖x‖^2) (Measure.map ev (μ n : Measure (I → ℝ)))
      have hg : AEStronglyMeasurable (fun x : ℝ => ‖x‖^2)
          (Measure.map ev (μ n : Measure (I → ℝ))) := (by fun_prop : Continuous (fun x : ℝ => ‖x‖^2)).aestronglyMeasurable
      rw [integrable_map_measure hg hev.measurable.aemeasurable]
      simpa only [ev,Real.norm_eq_abs,sq_abs] using hi n i
    have hmm (n : ℕ) : (∫ x : ℝ, ‖x‖^2 ∂(marg n : Measure ℝ))≤M i := by
      have hg : AEStronglyMeasurable (fun x : ℝ => ‖x‖^2)
          (Measure.map ev (μ n : Measure (I → ℝ))) := (by fun_prop : Continuous (fun x : ℝ => ‖x‖^2)).aestronglyMeasurable
      rw [show (marg n : Measure ℝ)=Measure.map ev (μ n : Measure (I → ℝ)) from rfl,
        integral_map hev.measurable.aemeasurable hg]
      simpa only [ev,Real.norm_eq_abs,sq_abs] using hM n i
    have ht := isTightMeasureSet_of_uniform_norm_second (fun n => (marg n : Measure ℝ)) hmi (M i) hmm
    have hlim : Tendsto (fun n => (marg (r n)).map
        isEmbedding_compactifiedRealCoordinate.continuous.measurable.aemeasurable)
        atTop (𝓝 limit) := by
      have hc := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hconv hevC
      convert hc using 1
      funext n
      apply Subtype.ext
      change Measure.map compactifiedRealCoordinate (Measure.map ev (μ (r n) : Measure (I → ℝ)))=
        Measure.map evC (Measure.map F (μ (r n) : Measure (I → ℝ)))
      rw [Measure.map_map isEmbedding_compactifiedRealCoordinate.continuous.measurable hev.measurable,
        Measure.map_map hevC.measurable hF.measurable]
      rfl
    have hz := measure_compl_range_eq_zero_of_tight_map_limit compactifiedRealCoordinate
      isEmbedding_compactifiedRealCoordinate.continuous
      isEmbedding_compactifiedRealCoordinate.continuous.measurable marg ht limit r hlim
    have ha : ∀ᵐ y ∂(limit : Measure CompactRealInterval), y∈Set.range compactifiedRealCoordinate :=
      ae_iff.mpr hz
    exact ae_of_ae_map hevC.measurable.aemeasurable ha
  have hall : ∀ᵐ x ∂(QC : Measure (I → CompactRealInterval)),
      ∀ i, x i∈Set.range compactifiedRealCoordinate := ae_all_iff.mpr hcoord
  have hrange : ∀ᵐ x ∂(QC : Measure (I → CompactRealInterval)), x∈Set.range F := by
    filter_upwards [hall] with x hx
    refine ⟨fun i => Classical.choose (hx i),?_⟩
    funext i
    exact Classical.choose_spec (hx i)
  have hz : (QC : Measure (I → CompactRealInterval)) (Set.range F)ᶜ=0 := ae_iff.mp hrange
  let hf := measurableEmbedding_realProcessCompactification (I := I)
  refine ⟨embeddingPullbackLaw hf QC hz,r,hr,?_⟩
  exact tendsto_embeddingPullbackLaw isEmbedding_finiteRealCompactification hf (μ ∘ r) QC hz hconv

/-- Every coordinate second moment remains finite in the weak limit, with
its actual lower-semicontinuity bound; equality is deliberately not asserted. -/
theorem process_coordinate_second_limit
    {I : Type*} [Countable I] (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : ProbabilityMeasure (I → ℝ)) (hweak : Tendsto μ atTop (𝓝 ν))
    (hi : ∀ n i, Integrable (fun x => x i^2) (μ n : Measure (I → ℝ)))
    (M : I → ℝ) (hM : ∀ n i, (∫ x, x i^2 ∂(μ n : Measure (I → ℝ)))≤M i) (i : I) :
    Integrable (fun x => x i^2) (ν : Measure (I → ℝ)) ∧
      (∫ x, x i^2 ∂(ν : Measure (I → ℝ)))≤M i := by
  letI : MetricSpace (I → ℝ) := TopologicalSpace.metrizableSpaceMetric (I → ℝ)
  exact integrable_and_integral_le_of_weak_nonneg μ ν hweak (fun x => x i^2)
    ((continuous_apply i).pow 2) (fun x => sq_nonneg _) (fun n => hi n i) (M i) (fun n => hM n i)

end GaussianWave.BS
