import BourgadeHuang.JointCountingSubsequence
import BourgadeHuang.VanishingAnchoredHierarchy
import BourgadeHuang.CountingEvaluation

/-! Tightness and genuine anchored subsequences for arbitrary random counting
Nevanlinna states. The proof uses their actual weighted mass and anchor. -/
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem uniformCountMoments_of_uniform_anchor_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → AnchoredCountingState) (hX : ∀N,Measurable (X N))
    (hm : ∀N q : ℕ,Integrable (fun ω => ‖(X N ω).val.2‖^q) μ)
    (hb : ∀q : ℕ,∃C : ℝ,∀N,(∫ω,‖(X N ω).val.2‖^q ∂μ) ≤ C) :
    UniformCountMoments μ (fun N ω => (X N ω).val.1) := by
  intro a b q
  let R := |a|+|b|
  have hR : ∀t∈Set.Icc a b,|t| ≤ R := by
    intro t ht
    rcases ht with ⟨hta,htb⟩
    apply abs_le.mpr
    constructor <;> dsimp [R] <;> linarith [neg_abs_le a,le_abs_self b,abs_nonneg a,abs_nonneg b]
  have hpoint (N : ℕ) (ω : Ω) :
      ((X N ω).val.1.measure (Set.Icc a b)).toReal^q ≤ (1+R^2)^q*‖(X N ω).val.2‖^q := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg ((X N ω).count_le_anchor hR) q
  have hi (N : ℕ) : Integrable
      (fun ω => ((X N ω).val.1.measure (Set.Icc a b)).toReal^q) μ := by
    apply ((hm N q).const_mul ((1+R^2)^q)).mono'
    · exact (((LocalCountingMeasure.measurable_compact_count isCompact_Icc).comp
        (measurable_fst.comp ((hX N).subtype_val))).pow_const q).aestronglyMeasurable
    · exact Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg ENNReal.toReal_nonneg _)]
        exact hpoint N ω)
  obtain ⟨C,hC⟩ := hb q
  refine ⟨hi,(1+R^2)^q*C,fun N => ?_⟩
  calc
    _ ≤ ∫ω,(1+R^2)^q*‖(X N ω).val.2‖^q ∂μ :=
      integral_mono (hi N) ((hm N q).const_mul _) (hpoint N)
    _ = (1+R^2)^q*(∫ω,‖(X N ω).val.2‖^q ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hC N) (by positivity)

theorem exists_anchored_subsequence_of_uniform_anchor_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → AnchoredCountingState) (hX : ∀N,Measurable (X N))
    (hm : ∀N q : ℕ,Integrable (fun ω => ‖(X N ω).val.2‖^q) μ)
    (hb : ∀q : ℕ,∃C : ℝ,∀N,(∫ω,‖(X N ω).val.2‖^q ∂μ) ≤ C) :
    ∃(ν : ProbabilityMeasure AnchoredCountingState) (r : ℕ → ℕ),StrictMono r ∧
      WeakLawConverges μ (fun N => X (r N)) (ν : Measure AnchoredCountingState) := by
  letI : MetricSpace JointCountingState := TopologicalSpace.metrizableSpaceMetric JointCountingState
  obtain ⟨C,hC⟩ := hb 2
  obtain ⟨ν,r,hr,hw⟩ := exists_joint_subsequence_of_moments
    (fun N ω => (X N ω).val.1) (fun N ω => (X N ω).val.2)
    (fun N => measurable_fst.comp ((hX N).subtype_val))
    (fun N => measurable_snd.comp ((hX N).subtype_val))
    (uniformCountMoments_of_uniform_anchor_moments μ X hX hm hb) (fun N => hm N 2) C hC
  have hw' : WeakLawConverges μ (fun N ω => (X (r N) ω).val) (ν : Measure JointCountingState) := hw
  have hvalid : ∀ᵐs∂(ν : Measure JointCountingState),ValidAnchoredCountingState s :=
    hw'.ae_mem_closed (fun N => (hX (r N)).subtype_val) ν isClosed_validAnchoredCountingState
      (fun N ω => (X (r N) ω).property)
  have hf : MeasurableEmbedding (Subtype.val : AnchoredCountingState → JointCountingState) :=
    MeasurableEmbedding.subtype_coe isClosed_validAnchoredCountingState.measurableSet
  have hν : (ν : Measure JointCountingState)
      (Set.range (Subtype.val : AnchoredCountingState → JointCountingState))ᶜ = 0 := by
    have he : Set.range (Subtype.val : AnchoredCountingState → JointCountingState) =
        {p | ValidAnchoredCountingState p} := by ext p; simp
    rw [he]
    exact ae_iff.mp hvalid
  exact ⟨embeddingPullbackLaw hf ν hν,r,hr,
    WeakLawConverges.lift_embedding (fun N => hX (r N))
      Topology.IsEmbedding.subtypeVal hf ν hν hw'⟩

end BourgadeHuang
