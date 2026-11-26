import GaussianWave.Foundation

/-! Actual finite-dimensional weak subsequences, obtained by compactifying
with arctangents and proving compactness of probability laws using Riesz--Markov.
Adapted from the user's earlier compact-law and finite-dimensional proofs;
no earlier project is an import or assumed compactness principle. -/
noncomputable section
open scoped Topology CompactlySupported BoundedContinuousFunction ENNReal BigOperators
open MeasureTheory Filter Set
namespace GaussianWave

private theorem isClosed_forall_condition {A I : Type*} [TopologicalSpace A]
    (p : I → A → Prop) (h : ∀ i, IsClosed {a | p i a}) :
    IsClosed {a | ∀ i, p i a} := by
  simpa only [Set.setOf_forall] using isClosed_iInter h

section CompactFunctionals
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Bounded positive unital linear functionals, with the topology of pointwise
convergence on continuous test functions. -/
def compactLawFunctionals : Set (C(X, ℝ) → ℝ) := {L |
    (∀ f, L f ∈ Set.Icc (-‖f‖) ‖f‖) ∧
    (∀ f g, L (f + g) = L f + L g) ∧
    (∀ (r : ℝ) f, L (r • f) = r * L f) ∧
    (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ L f) ∧
    L 1 = 1}

/-- Tychonoff compactness applies to the exact positivity and linearity equations. -/
theorem isCompact_compactLawFunctionals : IsCompact (compactLawFunctionals (X := X)) := by
  have hc : IsClosed (compactLawFunctionals (X := X)) := by
    apply IsClosed.inter
    · exact isClosed_forall_condition _ (fun f => isClosed_Icc.preimage (continuous_apply f))
    · apply IsClosed.inter
      · exact isClosed_forall_condition _ (fun f => isClosed_forall_condition _
          (fun g => isClosed_eq (continuous_apply (f + g))
            ((continuous_apply f).add (continuous_apply g))))
      · apply IsClosed.inter
        · exact isClosed_forall_condition _ (fun r => isClosed_forall_condition _
            (fun f => isClosed_eq (continuous_apply (r • f))
              (continuous_const.mul (continuous_apply f))))
        · apply IsClosed.inter
          · apply isClosed_forall_condition
            intro f
            by_cases hf : ∀ x, 0 ≤ f x
            · simpa [hf] using
                (isClosed_le continuous_const (continuous_apply f) :
                  IsClosed {L : C(X, ℝ) → ℝ | 0 ≤ L f})
            · simp [hf]
          · exact isClosed_eq (continuous_apply 1) continuous_const
  exact (isCompact_pi_infinite (fun f : C(X, ℝ) =>
    (isCompact_Icc : IsCompact (Set.Icc (-‖f‖) ‖f‖)))).of_isClosed_subset hc
    (fun _ h => h.1)

instance compactLawFunctionals_compactSpace :
    CompactSpace (compactLawFunctionals (X := X)) :=
  isCompact_iff_compactSpace.mp isCompact_compactLawFunctionals

/-- The compact-support version of a positive functional, suitable for Riesz–Markov. -/
def compactLawLinear (L : compactLawFunctionals (X := X)) : C_c(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := L.val f.toContinuousMap
  map_add' f g := L.property.2.1 f.toContinuousMap g.toContinuousMap
  map_smul' r f := L.property.2.2.1 r f.toContinuousMap

theorem compactLawLinear_nonneg (L : compactLawFunctionals (X := X))
    (f : C_c(X, ℝ)) (hf : 0 ≤ f) : 0 ≤ compactLawLinear L f :=
  L.property.2.2.2.1 _ hf

variable [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- The representing measure has mass one, as proved from the functional's
normalization and the two Riesz–Markov inequalities. -/
theorem compactLawLinear_riesz_probability (L : compactLawFunctionals (X := X)) :
    IsProbabilityMeasure (RealRMK.rieszMeasure (compactLawLinear_nonneg L)) := by
  let f : C_c(X, ℝ) := CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported (1 : C(X, ℝ))
  have hf : compactLawLinear L f = 1 := L.property.2.2.2.2
  refine ⟨le_antisymm ?_ ?_⟩
  · have hh := RealRMK.rieszMeasure_le_of_eq_one (compactLawLinear_nonneg L)
      (f := f) (fun _ => zero_le_one) isCompact_univ (fun _ _ => rfl)
    simpa only [hf, ENNReal.ofReal_one] using hh
  · have hh := RealRMK.le_rieszMeasure_tsupport_subset (compactLawLinear_nonneg L)
      (f := f) (fun _ => ⟨zero_le_one, le_rfl⟩) (Set.subset_univ _)
    simpa only [hf, ENNReal.ofReal_one] using hh

/-- The probability measure represented by a compact positive functional. -/
def compactLawMeasure (L : compactLawFunctionals (X := X)) : ProbabilityMeasure X :=
  ⟨RealRMK.rieszMeasure (compactLawLinear_nonneg L), compactLawLinear_riesz_probability L⟩

/-- The representing law integrates every continuous test to the original functional. -/
theorem integral_compactLawMeasure (L : compactLawFunctionals (X := X)) (f : C(X, ℝ)) :
    (∫ x, f x ∂(compactLawMeasure L : Measure X)) = L.val f := by
  exact RealRMK.integral_rieszMeasure (compactLawLinear_nonneg L)
    (CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported f)

/-- Pointwise convergence of functionals is weak convergence of the represented laws. -/
theorem continuous_compactLawMeasure : Continuous (compactLawMeasure (X := X)) := by
  rw [continuous_iff_continuousAt]
  intro L
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  simp only [show ∀ K : compactLawFunctionals (X := X),
      (∫ x, f x ∂(compactLawMeasure K : Measure X)) = K.val f.toContinuousMap from
    fun K => integral_compactLawMeasure K f.toContinuousMap]
  exact ((continuous_apply f.toContinuousMap).comp continuous_subtype_val).continuousAt

end CompactFunctionals

section CompactMetricLaws
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Integration against a probability law is a bounded positive unital functional. -/
def probabilityLawFunctional (μ : ProbabilityMeasure X) : compactLawFunctionals (X := X) := by
  refine ⟨(fun f => ∫ x, f x ∂(μ : Measure X)), ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    have hh := norm_integral_le_of_norm_le_const (μ := (μ : Measure X))
      (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x))
    have hh' : |∫ x, f x ∂(μ : Measure X)| ≤ ‖f‖ := by simpa using hh
    exact abs_le.mp hh'
  · intro f g
    exact integral_add
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g))
  · intro r f
    exact integral_const_mul r (fun x => f x)
  · intro f hf
    exact integral_nonneg hf
  · simp

/-- Riesz representation recovers the original law, so every law is represented. -/
theorem compactLawMeasure_probabilityLawFunctional (μ : ProbabilityMeasure X) :
    compactLawMeasure (probabilityLawFunctional μ) = μ := by
  have hh : (compactLawMeasure (probabilityLawFunctional μ)).toFiniteMeasure = μ.toFiniteMeasure := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    exact integral_compactLawMeasure (probabilityLawFunctional μ) f.toContinuousMap
  apply Subtype.ext
  exact congrArg (fun ν : FiniteMeasure X => (ν : Measure X)) hh

/-- Probability laws on a compact metric space form a compact space in the weak
topology. The compactness follows from the representing positive functionals. -/
theorem compactSpace_probabilityMeasure : CompactSpace (ProbabilityMeasure X) := by
  constructor
  have hh := isCompact_univ.image (continuous_compactLawMeasure (X := X))
  have hsurj : Function.Surjective (compactLawMeasure (X := X)) :=
    fun μ => ⟨probabilityLawFunctional μ, compactLawMeasure_probabilityLawFunctional μ⟩
  simpa only [Set.image_univ, Set.range_eq_univ.mpr hsurj] using hh

/-- Every sequence of probability laws on a compact metric space has an actual
weakly convergent subsequence. -/
theorem compact_probability_laws_subsequence [SecondCountableTopology X]
    (μ : ℕ → ProbabilityMeasure X) :
    ∃ (ν : ProbabilityMeasure X) (r : ℕ → ℕ), StrictMono r ∧
      Tendsto (μ ∘ r) atTop (𝓝 ν) := by
  letI : CompactSpace (ProbabilityMeasure X) := compactSpace_probabilityMeasure
  exact SeqCompactSpace.tendsto_subseq μ

/-- The subsequence can be tested against every real bounded continuous function. -/
theorem compact_probability_laws_subsequence_integrals [SecondCountableTopology X]
    (μ : ℕ → ProbabilityMeasure X) :
    ∃ (ν : ProbabilityMeasure X) (r : ℕ → ℕ), StrictMono r ∧
      ∀ f : X →ᵇ ℝ, Tendsto
        (fun n => ∫ x, f x ∂(μ (r n) : Measure X)) atTop
        (𝓝 (∫ x, f x ∂(ν : Measure X))) := by
  obtain ⟨ν, r, hr, hh⟩ := compact_probability_laws_subsequence μ
  exact ⟨ν, r, hr, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hh⟩

end CompactMetricLaws




/-- Tightness prevents mass escaping the range of a continuous map under weak
convergence. Injectivity and compactness of the ambient target are unnecessary. -/
theorem measure_compl_range_eq_zero_of_tight_map_limit
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (f : X → Y) (hf : Continuous f) (hfm : Measurable f)
    (μ : ℕ → ProbabilityMeasure X)
    (ht : IsTightMeasureSet (Set.range (fun n => (μ n : Measure X))))
    (ν : ProbabilityMeasure Y) (r : ℕ → ℕ)
    (hlim : Tendsto (fun n => (μ (r n)).map hfm.aemeasurable) atTop (𝓝 ν)) :
    (ν : Measure Y) (Set.range f)ᶜ = 0 := by
  apply le_antisymm _ bot_le
  apply le_of_forall_gt_imp_ge_of_dense
  intro ε hε
  obtain ⟨K, hK, hmass⟩ :=
    IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht ε hε
  have hclosed : IsClosed (f '' K) := (hK.image hf).isClosed
  have hpre : f ⁻¹' (f '' K)ᶜ ⊆ Kᶜ := by
    intro x hx hxK
    exact hx ⟨x, hxK, rfl⟩
  have hm (n : ℕ) : ((μ (r n)).map hfm.aemeasurable : Measure Y) (f '' K)ᶜ ≤ ε := by
    rw [ProbabilityMeasure.map_apply' _ _ hclosed.measurableSet.compl]
    exact (measure_mono hpre).trans (hmass _ ⟨r n, rfl⟩)
  calc
    (ν : Measure Y) (Set.range f)ᶜ ≤ (ν : Measure Y) (f '' K)ᶜ :=
      measure_mono (Set.compl_subset_compl.mpr (Set.image_subset_range _ _))
    _ ≤ atTop.liminf (fun n => ((μ (r n)).map hfm.aemeasurable : Measure Y) (f '' K)ᶜ) :=
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hclosed.isOpen_compl
    _ ≤ ε := liminf_le_of_frequently_le (Filter.Eventually.of_forall hm).frequently



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



abbrev CompactRealInterval := Set.Icc (-(Real.pi / 2)) (Real.pi / 2)
instance : CompactSpace CompactRealInterval := isCompact_iff_compactSpace.mp isCompact_Icc

def compactifiedRealCoordinate (x : ℝ) : CompactRealInterval :=
  ⟨Real.arctan x, (Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩

theorem isEmbedding_compactifiedRealCoordinate : Topology.IsEmbedding compactifiedRealCoordinate := by
  apply Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
  exact Real.arctan_strictMono.isEmbedding_of_ordConnected
    (by rw [Real.range_arctan]; exact Set.ordConnected_Ioo)

def finiteRealCompactification {ι : Type*} (x : ι → ℝ) : ι → CompactRealInterval :=
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


end GaussianWave
