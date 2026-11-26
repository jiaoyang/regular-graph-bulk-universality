import GeneralizedBulk.Analysis.FiniteDimensionalSubsequence
import GeneralizedBulk.Analysis.TruncationConvergence
import BourgadeHuang.NevanlinnaDetermination
import BourgadeHuang.JointCountingSubsequence

/-! Actual joint anchored-state/finite-mark weak subsequences, from scalar
law tightness and finite mark fourth moments. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology ENNReal BigOperators
namespace GeneralizedBulk.Analysis

theorem isTightMeasureSet_of_tight_marginals
    {S V : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [T2Space S]
    [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
    [SecondCountableTopology S] [SecondCountableTopology V]
    (μ : ℕ → Measure (S × V))
    (hS : IsTightMeasureSet (range (fun n => (μ n).map Prod.fst)))
    (hV : IsTightMeasureSet (range (fun n => (μ n).map Prod.snd))) :
    IsTightMeasureSet (range μ) := by
  rw [IsTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hS hV ⊢
  intro ε hε
  have hhalf : 0 < ε/2 := ENNReal.div_pos_iff.mpr ⟨hε.ne',by norm_num⟩
  obtain ⟨KS,hKS,hS⟩ := hS (ε/2) hhalf
  obtain ⟨KV,hKV,hV⟩ := hV (ε/2) hhalf
  refine ⟨KS ×ˢ KV,hKS.prod hKV,?_⟩
  rintro _ ⟨n,rfl⟩
  have hsub : (KS ×ˢ KV)ᶜ ⊆ Prod.fst ⁻¹' KSᶜ ∪ Prod.snd ⁻¹' KVᶜ := by
    intro z hz
    simpa only [mem_compl_iff,mem_prod,not_and_or,mem_union,mem_preimage] using hz
  calc
    μ n (KS ×ˢ KV)ᶜ ≤ μ n (Prod.fst ⁻¹' KSᶜ ∪ Prod.snd ⁻¹' KVᶜ) := measure_mono hsub
    _ ≤ μ n (Prod.fst ⁻¹' KSᶜ) + μ n (Prod.snd ⁻¹' KVᶜ) := measure_union_le _ _
    _ = ((μ n).map Prod.fst) KSᶜ + ((μ n).map Prod.snd) KVᶜ := by
      rw [Measure.map_apply measurable_fst hKS.isClosed.measurableSet.compl,
        Measure.map_apply measurable_snd hKV.isClosed.measurableSet.compl]
    _ ≤ ε/2+ε/2 := add_le_add (hS _ ⟨n,rfl⟩) (hV _ ⟨n,rfl⟩)
    _ = ε := ENNReal.add_halves ε

def anchoredMarkCompactification {ι : Type*} (x : AnchoredCountingState × (ι → ℝ)) :
    (CountingCompactCube × (CountingCoordinateInterval × CountingCoordinateInterval)) × (ι → CountingCoordinateInterval) :=
  (jointCountingCompactification x.1.val,finiteRealCompactification x.2)

theorem isEmbedding_anchoredMarkCompactification {ι : Type*} :
    Topology.IsEmbedding (anchoredMarkCompactification (ι := ι)) :=
  (isEmbedding_jointCountingCompactification.comp Topology.IsEmbedding.subtypeVal).prodMap isEmbedding_finiteRealCompactification

theorem measurableEmbedding_anchoredMarkCompactification {ι : Type*} [Fintype ι] :
    MeasurableEmbedding (anchoredMarkCompactification (ι := ι)) :=
  isEmbedding_anchoredMarkCompactification.continuous.measurableEmbedding isEmbedding_anchoredMarkCompactification.injective

theorem anchored_mark_subsequence_of_tight_scalar_fourth
    {ι : Type*} [Fintype ι] (μ : ℕ → ProbabilityMeasure (AnchoredCountingState × (ι → ℝ)))
    (hscalar : IsTightMeasureSet (range (fun n => (μ n : Measure (AnchoredCountingState × (ι → ℝ))).map Prod.fst)))
    (hi : ∀ n,Integrable (fun z : AnchoredCountingState × (ι → ℝ) => ‖z.2‖^4) (μ n : Measure (AnchoredCountingState × (ι → ℝ)))) (M : ℝ)
    (hM : ∀ n,(∫ z,‖z.2‖^4 ∂(μ n : Measure (AnchoredCountingState × (ι → ℝ)))) ≤ M) :
    ∃ (ν : ProbabilityMeasure (AnchoredCountingState × (ι → ℝ))) (r : ℕ → ℕ),StrictMono r ∧
      Tendsto (μ ∘ r) atTop (𝓝 ν) := by
  let marks := fun n => (μ n : Measure (AnchoredCountingState × (ι → ℝ))).map Prod.snd
  letI : ∀ n,IsProbabilityMeasure (marks n) := fun n => isProbabilityMeasure_map measurable_snd.aemeasurable
  have himarks (n : ℕ) : Integrable (fun x : ι → ℝ => ‖x‖^4) (marks n) := by
    apply (integrable_map_measure (continuous_norm.pow 4).aestronglyMeasurable measurable_snd.aemeasurable).mpr
    exact hi n
  have hmarksM (n : ℕ) : (∫ x : ι → ℝ,‖x‖^4 ∂marks n) ≤ M := by
    dsimp only [marks]
    rw [integral_map measurable_snd.aemeasurable (continuous_norm.pow 4).aestronglyMeasurable]
    exact hM n
  have ht := isTightMeasureSet_of_tight_marginals (fun n => (μ n : Measure (AnchoredCountingState × (ι → ℝ)))) hscalar
    (isTightMeasureSet_of_uniform_norm_fourth marks himarks M hmarksM)
  exact laws_subsequence_of_tight_compact_embedding anchoredMarkCompactification isEmbedding_anchoredMarkCompactification
    measurableEmbedding_anchoredMarkCompactification μ ht

theorem anchored_mark_subsequence_of_tight_scalar_good_fourth
    {ι : Type*} [Fintype ι] {ΩN : ℕ → Type*} [∀ n,MeasurableSpace (ΩN n)]
    (P : ∀ n,Measure (ΩN n)) [∀ n,IsProbabilityMeasure (P n)]
    (S : ∀ n,ΩN n → AnchoredCountingState) (marks : ∀ n,ΩN n → (ι → ℝ))
    (hS : ∀ n,Measurable (S n)) (hmarks : ∀ n,Measurable (marks n))
    (hscalar : IsTightMeasureSet (range (fun n => (P n).map (S n))))
    (good : ∀ n,Set (ΩN n)) (hgood : ∀ n,MeasurableSet (good n))
    (hbad : Tendsto (fun n => (P n).real (good n)ᶜ) atTop (𝓝 0))
    (hi : ∀ n,IntegrableOn (fun x => ‖marks n x‖^4) (good n) (P n)) (M : ℝ)
    (hM : ∀ n,(∫ x in good n,‖marks n x‖^4 ∂P n) ≤ M) :
    ∃ (ν : ProbabilityMeasure (AnchoredCountingState × (ι → ℝ))) (r : ℕ → ℕ),StrictMono r ∧
      External.WeakLawConverges
        (fun n => (P (r n)).map (fun x => (S (r n) x,marks (r n) x))) (ν : Measure _) := by
  letI : MetricSpace AnchoredCountingState := TopologicalSpace.metrizableSpaceMetric AnchoredCountingState
  let F := fun n (x : ΩN n) => (S n x,(good n).indicator (marks n) x)
  have hF (n : ℕ) : Measurable (F n) := (hS n).prodMk ((hmarks n).indicator (hgood n))
  have hnorm (n : ℕ) : (fun x => ‖(F n x).2‖^4) = (good n).indicator (fun x => ‖marks n x‖^4) := by
    funext x
    by_cases hx : x ∈ good n <;> simp [F,hx]
  have hFi (n : ℕ) : Integrable (fun x => ‖(F n x).2‖^4) (P n) := by
    rw [hnorm]
    exact (integrable_indicator_iff (hgood n)).mpr (hi n)
  have hFM (n : ℕ) : (∫ x,‖(F n x).2‖^4 ∂P n) ≤ M := by
    rw [hnorm,integral_indicator (hgood n)]
    exact hM n
  let laws : ℕ → ProbabilityMeasure (AnchoredCountingState × (ι → ℝ)) :=
    fun n => ⟨(P n).map (F n),isProbabilityMeasure_map (hF n).aemeasurable⟩
  have hscalar' : IsTightMeasureSet (range (fun n => (laws n : Measure (AnchoredCountingState × (ι → ℝ))).map Prod.fst)) := by
    have he (n : ℕ) : (laws n : Measure (AnchoredCountingState × (ι → ℝ))).map Prod.fst = (P n).map (S n) := by
      change ((P n).map (F n)).map Prod.fst = _
      rw [Measure.map_map measurable_fst (hF n)]
      rfl
    simpa only [he] using hscalar
  have hli (n : ℕ) : Integrable (fun z : AnchoredCountingState × (ι → ℝ) => ‖z.2‖^4) (laws n : Measure _) := by
    exact (integrable_map_measure (continuous_snd.norm.pow 4).aestronglyMeasurable (hF n).aemeasurable).mpr (hFi n)
  have hlM (n : ℕ) : (∫ z : AnchoredCountingState × (ι → ℝ),‖z.2‖^4 ∂(laws n : Measure _)) ≤ M := by
    change (∫ z : AnchoredCountingState × (ι → ℝ),‖z.2‖^4 ∂(P n).map (F n)) ≤ M
    rw [integral_map (hF n).aemeasurable (continuous_snd.norm.pow 4).aestronglyMeasurable]
    exact hFM n
  obtain ⟨ν,r,hr,hw⟩ := anchored_mark_subsequence_of_tight_scalar_fourth laws hscalar' hli M hlM
  have hweak : External.WeakLawConverges (fun n => (P (r n)).map (F (r n))) (ν : Measure _) := by
    intro G
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hw G
  refine ⟨ν,r,hr,?_⟩
  apply weakLaw_of_equal_on_large_events (fun n => P (r n))
    (fun n x => (S (r n) x,marks (r n) x)) (fun n => F (r n))
    (fun n => (hS (r n)).prodMk (hmarks (r n))) (fun n => hF (r n))
    (fun n => good (r n)) ?_ (hbad.comp hr.tendsto_atTop) (ν : Measure _) hweak
  intro n x hx
  simp [F,hx]

theorem anchored_mark_subsequence_of_tight_scalar_eventual_good_fourth
    {ι : Type*} [Fintype ι] {ΩN : ℕ → Type*} [∀ n,MeasurableSpace (ΩN n)]
    (P : ∀ n,Measure (ΩN n)) [∀ n,IsProbabilityMeasure (P n)]
    (S : ∀ n,ΩN n → AnchoredCountingState) (marks : ∀ n,ΩN n → (ι → ℝ))
    (hS : ∀ n,Measurable (S n)) (hmarks : ∀ n,Measurable (marks n))
    (hscalar : IsTightMeasureSet (range (fun n => (P n).map (S n))))
    (good : ∀ n,Set (ΩN n)) (hgood : ∀ n,MeasurableSet (good n))
    (hbad : Tendsto (fun n => (P n).real (good n)ᶜ) atTop (𝓝 0)) (M : ℝ)
    (hfourth : ∀ᶠ n in atTop,IntegrableOn (fun x => ‖marks n x‖^4) (good n) (P n) ∧
      (∫ x in good n,‖marks n x‖^4 ∂P n) ≤ M) :
    ∃ (ν : ProbabilityMeasure (AnchoredCountingState × (ι → ℝ))) (r : ℕ → ℕ),StrictMono r ∧
      External.WeakLawConverges
        (fun n => (P (r n)).map (fun x => (S (r n) x,marks (r n) x))) (ν : Measure _) := by
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp hfourth
  have hshift : Tendsto (fun n : ℕ => n+N0) atTop atTop := tendsto_add_atTop_nat N0
  have hs : IsTightMeasureSet (range (fun n => (P (n+N0)).map (S (n+N0)))) := by
    apply hscalar.subset
    rintro _ ⟨n,rfl⟩
    exact ⟨n+N0,rfl⟩
  obtain ⟨ν,r,hr,hw⟩ := anchored_mark_subsequence_of_tight_scalar_good_fourth
    (fun n => P (n+N0)) (fun n => S (n+N0)) (fun n => marks (n+N0))
    (fun n => hS (n+N0)) (fun n => hmarks (n+N0)) hs
    (fun n => good (n+N0)) (fun n => hgood (n+N0)) (hbad.comp hshift)
    (fun n => (hN0 (n+N0) (by omega)).1) M (fun n => (hN0 (n+N0) (by omega)).2)
  refine ⟨ν,fun n => r n+N0,fun i j hij => Nat.add_lt_add_right (hr hij) N0,hw⟩

end GeneralizedBulk.Analysis
