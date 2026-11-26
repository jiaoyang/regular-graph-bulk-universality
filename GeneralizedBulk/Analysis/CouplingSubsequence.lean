import GeneralizedBulk.Analysis.WeakLawTightness
import GeneralizedBulk.Analysis.JointMarkSubsequence
import GeneralizedBulk.Analysis.WeakRelations

/-! Tight weakly convergent marginals yield actual joint coupling
subsequences, with no joint moment bound or coupling existence premise. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology
namespace GeneralizedBulk.Analysis
variable {V ι : Type*} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [SecondCountableTopology V] [Fintype ι]

theorem isTightMeasureSet_of_weakLawConverges_finite_homeomorph
    (μ : ℕ → Measure V) [∀ n,IsProbabilityMeasure (μ n)]
    (ν : Measure V) [IsProbabilityMeasure ν] (hweak : External.WeakLawConverges μ ν)
    (e : V ≃ₜ (ι → ℝ)) : IsTightMeasureSet (range μ) := by
  letI : ∀ n,IsProbabilityMeasure ((μ n).map e) := fun n => isProbabilityMeasure_map e.continuous.measurable.aemeasurable
  letI : IsProbabilityMeasure (ν.map e) := isProbabilityMeasure_map e.continuous.measurable.aemeasurable
  have ht := isTightMeasureSet_of_weakLawConverges (fun n => (μ n).map e) (ν.map e)
    (weakLaw_map μ ν hweak e e.continuous)
  have hb := ht.map e.symm.continuous
  apply hb.subset
  rintro _ ⟨n,rfl⟩
  refine ⟨(μ n).map e,⟨n,rfl⟩,?_⟩
  rw [Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
  have he : e.symm ∘ e = id := by funext x; exact e.symm_apply_apply x
  rw [he,Measure.map_id]

theorem coupling_subsequence_of_weak_marginals_finite_homeomorph
    (μ : ℕ → ProbabilityMeasure (V × V)) (ρ : Measure V) [IsProbabilityMeasure ρ]
    (hleft : External.WeakLawConverges (fun n => (μ n : Measure (V × V)).map Prod.fst) ρ)
    (hright : External.WeakLawConverges (fun n => (μ n : Measure (V × V)).map Prod.snd) ρ)
    (e : V ≃ₜ (ι → ℝ)) :
    ∃ (ν : ProbabilityMeasure (V × V)) (r : ℕ → ℕ),StrictMono r ∧ Tendsto (μ ∘ r) atTop (𝓝 ν) := by
  letI : ∀ n,IsProbabilityMeasure ((μ n : Measure (V × V)).map Prod.fst) :=
    fun n => isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : ∀ n,IsProbabilityMeasure ((μ n : Measure (V × V)).map Prod.snd) :=
    fun n => isProbabilityMeasure_map measurable_snd.aemeasurable
  have ht := isTightMeasureSet_of_tight_marginals (fun n => (μ n : Measure (V × V)))
    (isTightMeasureSet_of_weakLawConverges_finite_homeomorph _ ρ hleft e)
    (isTightMeasureSet_of_weakLawConverges_finite_homeomorph _ ρ hright e)
  let c : ((ι → ℝ) × (ι → ℝ)) → (ι → CountingCoordinateInterval) × (ι → CountingCoordinateInterval) :=
    Prod.map finiteRealCompactification finiteRealCompactification
  have hc : Topology.IsEmbedding c := isEmbedding_finiteRealCompactification.prodMap isEmbedding_finiteRealCompactification
  have hcm : MeasurableEmbedding c := hc.continuous.measurableEmbedding hc.injective
  let f := c ∘ (e.prodCongr e)
  have hf : Topology.IsEmbedding f := hc.comp (e.prodCongr e).isEmbedding
  have hfm : MeasurableEmbedding f := hcm.comp (e.prodCongr e).measurableEmbedding
  exact laws_subsequence_of_tight_compact_embedding f hf hfm μ ht

end GeneralizedBulk.Analysis
