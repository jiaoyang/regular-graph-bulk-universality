import Mathlib

/-! Product bounded-continuous tests determine genuine finite Borel laws.
This is the measure-theoretic closure of conditional marked factorization. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
namespace GeneralizedBulk.Analysis

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
    [HasOuterApproxClosed E] [HasOuterApproxClosed F]
    [SecondCountableTopology E] [SecondCountableTopology F]

private def realBCF (G : E →ᵇ ℝ≥0) : E →ᵇ ℝ :=
  ⟨⟨fun x => (G x : ℝ),NNReal.continuous_coe.comp G.continuous⟩,G.map_bounded'⟩

private def tensorNNBCF (G : E →ᵇ ℝ≥0) (H : F →ᵇ ℝ≥0) : E × F →ᵇ ℝ≥0 :=
  G.compContinuous ⟨Prod.fst,continuous_fst⟩ * H.compContinuous ⟨Prod.snd,continuous_snd⟩

private theorem tensor_lintegral_eq {μ ν : Measure (E × F)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (G : E →ᵇ ℝ) (H : F →ᵇ ℝ),
      (∫ z,G z.1*H z.2 ∂μ) = ∫ z,G z.1*H z.2 ∂ν)
    (G : E →ᵇ ℝ≥0) (H : F →ᵇ ℝ≥0) :
    (∫⁻ z,(G z.1 : ℝ≥0∞)*(H z.2 : ℝ≥0∞) ∂μ) =
      ∫⁻ z,(G z.1 : ℝ≥0∞)*(H z.2 : ℝ≥0∞) ∂ν := by
  let T := tensorNNBCF G H
  change (∫⁻ z,(T z : ℝ≥0∞) ∂μ) = ∫⁻ z,(T z : ℝ≥0∞) ∂ν
  apply (ENNReal.toReal_eq_toReal_iff' (T.lintegral_lt_top_of_nnreal μ).ne
    (T.lintegral_lt_top_of_nnreal ν).ne).mp
  rw [T.toReal_lintegral_coe_eq_integral μ,T.toReal_lintegral_coe_eq_integral ν]
  exact h (realBCF G) (realBCF H)

set_option maxHeartbeats 2000000 in
/-- Equality of all tensor-product bounded continuous tests determines the
whole finite Borel law, without an independence or conditional-law assumption. -/
theorem measure_eq_of_tensor_bcf {μ ν : Measure (E × F)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (G : E →ᵇ ℝ) (H : F →ᵇ ℝ),
      (∫ z,G z.1*H z.2 ∂μ) = ∫ z,G z.1*H z.2 ∂ν) : μ = ν := by
  have hw (H : F →ᵇ ℝ≥0) :
      Measure.map Prod.fst (μ.withDensity (fun z => (H z.2 : ℝ≥0∞))) =
        Measure.map Prod.fst (ν.withDensity (fun z => (H z.2 : ℝ≥0∞))) := by
    let Hsnd : E × F →ᵇ ℝ≥0 := H.compContinuous ⟨Prod.snd,continuous_snd⟩
    haveI : IsFiniteMeasure (μ.withDensity (fun z => (H z.2 : ℝ≥0∞))) :=
      isFiniteMeasure_withDensity (Hsnd.lintegral_lt_top_of_nnreal μ).ne
    haveI : IsFiniteMeasure (ν.withDensity (fun z => (H z.2 : ℝ≥0∞))) :=
      isFiniteMeasure_withDensity (Hsnd.lintegral_lt_top_of_nnreal ν).ne
    apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
    intro G
    rw [lintegral_map G.measurable_coe_ennreal_comp measurable_fst,
      lintegral_map G.measurable_coe_ennreal_comp measurable_fst,
      lintegral_withDensity_eq_lintegral_mul _
        (show Measurable (fun z : E × F => (H z.2 : ℝ≥0∞)) from Hsnd.measurable_coe_ennreal_comp)
        (show Measurable (fun z : E × F => (G z.1 : ℝ≥0∞)) from G.measurable_coe_ennreal_comp.comp measurable_fst),
      lintegral_withDensity_eq_lintegral_mul _
        (show Measurable (fun z : E × F => (H z.2 : ℝ≥0∞)) from Hsnd.measurable_coe_ennreal_comp)
        (show Measurable (fun z : E × F => (G z.1 : ℝ≥0∞)) from G.measurable_coe_ennreal_comp.comp measurable_fst)]
    simpa only [mul_comm] using tensor_lintegral_eq h G H
  have hrestrict (A : Set E) (hA : MeasurableSet A) :
      Measure.map Prod.snd (μ.restrict (Prod.fst ⁻¹' A)) =
        Measure.map Prod.snd (ν.restrict (Prod.fst ⁻¹' A)) := by
    apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
    intro H
    rw [lintegral_map H.measurable_coe_ennreal_comp measurable_snd,
      lintegral_map H.measurable_coe_ennreal_comp measurable_snd]
    have hh := congrArg (fun ρ : Measure E => ρ A) (hw H)
    dsimp only at hh
    rw [Measure.map_apply measurable_fst hA,Measure.map_apply measurable_fst hA,
      withDensity_apply _ (measurable_fst hA),withDensity_apply _ (measurable_fst hA)] at hh
    exact hh
  apply ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod
  · rintro _ ⟨A,hA,B,hB,rfl⟩
    have hh := congrArg (fun ρ : Measure F => ρ B) (hrestrict A hA)
    dsimp only at hh
    rw [Measure.map_apply measurable_snd hB,Measure.map_apply measurable_snd hB,
      Measure.restrict_apply (measurable_snd hB),Measure.restrict_apply (measurable_snd hB)] at hh
    have heq : Prod.snd ⁻¹' B ∩ Prod.fst ⁻¹' A = A ×ˢ B := by ext z; simp only [mem_inter_iff,mem_preimage,mem_prod]; tauto
    simpa only [heq] using hh
  · have hh := congrArg (fun ρ : Measure F => ρ univ) (hrestrict univ MeasurableSet.univ)
    dsimp only at hh
    simpa only [Measure.map_apply measurable_snd MeasurableSet.univ,preimage_univ,Measure.restrict_univ] using hh

/-- Literal factorized product tests imply equality with the product law. -/
theorem measure_eq_prod_of_tensor_bcf {μ : Measure (E × F)} [IsFiniteMeasure μ]
    (ν : Measure E) (π : Measure F) [IsFiniteMeasure ν] [IsFiniteMeasure π]
    (h : ∀ (G : E →ᵇ ℝ) (H : F →ᵇ ℝ),
      (∫ z,G z.1*H z.2 ∂μ) = (∫ x,G x ∂ν)*(∫ y,H y ∂π)) :
    μ = ν.prod π := by
  apply measure_eq_of_tensor_bcf
  intro G H
  rw [h G H]
  exact (integral_prod_mul (μ := ν) (ν := π) G H).symm

end GeneralizedBulk.Analysis
