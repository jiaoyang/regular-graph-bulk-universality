import BourgadeHuang.CountingSeparation
import BourgadeHuang.CompactLawSubsequence
import BourgadeHuang.TightEmbeddingSupport
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Extraction of vague laws from uniform compact count moments

The counting-measure space embeds into a countable compact cube. Compactness of
probability laws on that cube gives a subsequence. Tightness ensures that its
limit is carried by genuine counting configurations, and the embedding version
of the portmanteau theorem transfers convergence back to the vague topology.
-/
noncomputable section
open scoped Topology ENNReal BoundedContinuousFunction
open MeasureTheory Filter Set

namespace BourgadeHuang

section EmbeddingPullback
variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {f : X → Y}

/-- A probability law supported on the image of a measurable embedding pulls back
to an actual probability law on the source. -/
def embeddingPullbackLaw (hf : MeasurableEmbedding f) (ν : ProbabilityMeasure Y)
    (hν : (ν : Measure Y) (Set.range f)ᶜ = 0) : ProbabilityMeasure X :=
  ⟨Measure.comap f ν, ⟨by
    rw [hf.comap_apply, Set.image_univ, measure_of_measure_compl_eq_zero hν, measure_univ]⟩⟩

omit [TopologicalSpace X] [BorelSpace X] [MetricSpace Y] [BorelSpace Y] in
/-- Mapping the pullback law recovers the supported law exactly. -/
theorem map_embeddingPullbackLaw (hf : MeasurableEmbedding f) (ν : ProbabilityMeasure Y)
    (hν : (ν : Measure Y) (Set.range f)ᶜ = 0) :
    (embeddingPullbackLaw hf ν hν).map hf.measurable.aemeasurable = ν := by
  apply Subtype.ext
  change (Measure.comap f (ν : Measure Y)).map f = (ν : Measure Y)
  rw [hf.map_comap]
  apply Measure.restrict_eq_self_of_ae_mem
  exact (ae_iff.mpr hν)

/-- Weak convergence of mapped laws lifts through a topological embedding whenever
the limit is supported on its range. This is the open-set portmanteau criterion. -/
theorem tendsto_embeddingPullbackLaw (he : Topology.IsEmbedding f)
    (hf : MeasurableEmbedding f) (μ : ℕ → ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (hν : (ν : Measure Y) (Set.range f)ᶜ = 0)
    (hconv : Tendsto (fun n => (μ n).map hf.measurable.aemeasurable) atTop (𝓝 ν)) :
    Tendsto μ atTop (𝓝 (embeddingPullbackLaw hf ν hν)) := by
  apply tendsto_of_forall_isOpen_le_liminf
  intro U hU
  obtain ⟨V, hV, hVU⟩ := he.isInducing.isOpen_iff.mp hU
  have hh := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv hV
  have hνV : (ν : Measure Y) V = (embeddingPullbackLaw hf ν hν : Measure X) U := by
    calc
      (ν : Measure Y) V = ((embeddingPullbackLaw hf ν hν).map
          hf.measurable.aemeasurable : Measure Y) V :=
        congrArg (fun η : ProbabilityMeasure Y => (η : Measure Y) V)
          (map_embeddingPullbackLaw hf ν hν).symm
      _ = _ := by rw [ProbabilityMeasure.map_apply' _ _ hV.measurableSet, hVU]
  have hnV (n : ℕ) : ((μ n).map hf.measurable.aemeasurable : Measure Y) V = (μ n : Measure X) U := by
    rw [ProbabilityMeasure.map_apply' _ _ hV.measurableSet, hVU]
  rw [hνV] at hh
  simp_rw [hnV] at hh
  have hb : atTop.IsBoundedUnder (· ≤ ·) (fun n : ℕ => (μ n) U) :=
    ⟨1, by simp⟩
  apply ENNReal.coe_le_coe.mp
  rw [ENNReal.ofNNReal_liminf hb.isCoboundedUnder_ge]
  simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hh

end EmbeddingPullback

/-- A tight sequence of laws has a weak subsequence whenever its state space
embeds topologically and measurably into a compact metric space. -/
theorem laws_subsequence_of_tight_compact_embedding
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [CompactSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (f : X → Y) (he : Topology.IsEmbedding f) (hf : MeasurableEmbedding f)
    (μ : ℕ → ProbabilityMeasure X)
    (ht : IsTightMeasureSet (Set.range (fun n => (μ n : Measure X)))) :
    ∃ (ν : ProbabilityMeasure X) (r : ℕ → ℕ), StrictMono r ∧
      Tendsto (μ ∘ r) atTop (𝓝 ν) := by
  obtain ⟨ν, r, hr, hlim⟩ := compact_probability_laws_subsequence
    (fun n => (μ n).map hf.measurable.aemeasurable)
  have hs : (ν : Measure Y) (Set.range f)ᶜ = 0 :=
    measure_compl_range_eq_zero_of_tight_map_limit f he.continuous hf.measurable μ ht ν r hlim
  refine ⟨embeddingPullbackLaw hf ν hs, r, hr, ?_⟩
  exact tendsto_embeddingPullbackLaw he hf (μ ∘ r) ν hs hlim

/-- Tight sequences of laws of locally finite counting measures have a genuinely
vaguely convergent subsequence. The limit law is constructed by compactification
and pullback, not included among the assumptions. -/
theorem counting_laws_subsequence_of_tight
    (μ : ℕ → ProbabilityMeasure LocalCountingMeasure)
    (ht : IsTightMeasureSet (Set.range (fun n => (μ n : Measure LocalCountingMeasure)))) :
    ∃ (ν : ProbabilityMeasure LocalCountingMeasure) (r : ℕ → ℕ), StrictMono r ∧
      Tendsto (μ ∘ r) atTop (𝓝 ν) := by
  exact laws_subsequence_of_tight_compact_embedding countingCompactification
    isEmbedding_countingCompactification measurableEmbedding_countingCompactification μ ht

/-- Compact count moments give actual subsequential convergence in distribution
of the configuration laws for the vague topology. -/
theorem exists_vagueLaw_subsequence_of_uniformCountMoments
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → LocalCountingMeasure) (hm : ∀ N, Measurable (ξ N))
    (hc : UniformCountMoments μ ξ) :
    ∃ (ν : ProbabilityMeasure LocalCountingMeasure) (r : ℕ → ℕ), StrictMono r ∧
      VagueLawConverges μ (fun N => ξ (r N)) (ν : Measure LocalCountingMeasure) := by
  let laws : ℕ → ProbabilityMeasure LocalCountingMeasure := fun N =>
    ProbabilityMeasure.map (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω) (hm N).aemeasurable
  have ht : IsTightMeasureSet (Set.range (fun n => (laws n : Measure LocalCountingMeasure))) :=
    isTightMeasureSet_of_uniformCountMoments ξ hm hc
  obtain ⟨ν, r, hr, hlim⟩ := counting_laws_subsequence_of_tight laws ht
  refine ⟨ν, r, hr, fun F => ?_⟩
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim F
  have he (N : ℕ) : (∫ c, F c ∂(laws (r N) : Measure LocalCountingMeasure)) =
      ∫ ω, F (ξ (r N) ω) ∂μ := by
    exact integral_map (hm (r N)).aemeasurable F.continuous.aestronglyMeasurable
  simpa only [Function.comp_apply, he] using hh

end BourgadeHuang
