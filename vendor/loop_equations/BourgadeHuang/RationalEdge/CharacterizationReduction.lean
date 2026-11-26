import BourgadeHuang.RationalEdge.Limits

/-! Compactness-to-convergence assembly. The uniqueness hypothesis in this
intermediate lemma is explicit and must be discharged by the rational CMS
uniqueness theorem at the article-facing endpoint. -/
noncomputable section
open scoped Topology BoundedContinuousFunction
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge

/-- The counting configuration is a continuous projection of the anchored state. -/
theorem anchored_sequence_vagueLawConverges
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → AnchoredCountingState) (ν : ProbabilityMeasure AnchoredCountingState)
    (hw : WeakLawConverges μ X (ν : Measure AnchoredCountingState)) :
    VagueLawConverges μ (fun N ω => (X N ω).val.1)
      (anchoredCountingLaw ν : Measure LocalCountingMeasure) := by
  intro F
  have hh := hw (F.compContinuous ⟨fun s => s.val.1, continuous_fst.comp continuous_subtype_val⟩)
  have he : (∫ c, F c ∂(anchoredCountingLaw ν : Measure LocalCountingMeasure)) =
      ∫ s, F s.val.1 ∂(ν : Measure AnchoredCountingState) :=
    integral_map (measurable_fst.comp measurable_subtype_coe).aemeasurable
      F.continuous.aestronglyMeasurable
  rw [he]
  exact hh

theorem weakLawConverges_of_vanishingHierarchy_and_uniqueness
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (β : ℝ) (X : ℕ → Ω → AnchoredCountingState) (hX : ∀ N, Measurable (X N))
    (hm : ∀ N q : ℕ, Integrable (fun ω => ‖(X N ω).val.2‖ ^ q) μ)
    (h : VanishingHierarchy μ β X)
    (ν : ProbabilityMeasure AnchoredCountingState)
    (hunique : ∀ ρ : ProbabilityMeasure AnchoredCountingState,
      ExactHierarchy (ρ : Measure AnchoredCountingState) β →
      (∃ a : ℝ, 0 < a ∧ Integrable
        (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2))
          (ρ : Measure AnchoredCountingState)) → ρ = ν) :
    WeakLawConverges μ X (ν : Measure AnchoredCountingState) := by
  intro F
  apply tendsto_of_subseq_tendsto
  intro r hr
  obtain ⟨t, ht, hrt⟩ := strictMono_subseq_of_tendsto_atTop hr
  obtain ⟨ρ, s, hs, hw, hh, he⟩ := exists_exact_anchored_subsequence_of_vanishingHierarchy μ β
    (fun N => X (r (t N))) (fun N => hX (r (t N)))
    (fun N q => hm (r (t N)) q) (h.comp hrt.tendsto_atTop)
  have heq := hunique ρ hh he
  subst ρ
  exact ⟨t ∘ s, hw F⟩

theorem vagueLawConverges_of_vanishingHierarchy_and_uniqueness
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (β : ℝ) (X : ℕ → Ω → AnchoredCountingState) (hX : ∀ N, Measurable (X N))
    (hm : ∀ N q : ℕ, Integrable (fun ω => ‖(X N ω).val.2‖ ^ q) μ)
    (h : VanishingHierarchy μ β X)
    (ν : ProbabilityMeasure AnchoredCountingState)
    (hunique : ∀ ρ : ProbabilityMeasure AnchoredCountingState,
      ExactHierarchy (ρ : Measure AnchoredCountingState) β →
      (∃ a : ℝ, 0 < a ∧ Integrable
        (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2))
          (ρ : Measure AnchoredCountingState)) → ρ = ν) :
    VagueLawConverges μ (fun N ω => (X N ω).val.1)
      (anchoredCountingLaw ν : Measure LocalCountingMeasure) :=
  anchored_sequence_vagueLawConverges μ X ν
    (weakLawConverges_of_vanishingHierarchy_and_uniqueness μ β X hX hm h ν hunique)

end BourgadeHuang.RationalEdge
