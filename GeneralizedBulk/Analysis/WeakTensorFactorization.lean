import GeneralizedBulk.Analysis.TensorMeasureUniqueness
import GeneralizedBulk.ExternalInputs

/-! Weak limits of genuine product-test factorizations are product laws,
including restriction to a continuous discrete-count stratum. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace GeneralizedBulk.Analysis
variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
    [HasOuterApproxClosed E] [HasOuterApproxClosed F]
    [SecondCountableTopology E] [SecondCountableTopology F]

private def tensorBCF (G : E →ᵇ ℝ) (H : F →ᵇ ℝ) : E × F →ᵇ ℝ :=
  G.compContinuous ⟨Prod.fst,continuous_fst⟩ * H.compContinuous ⟨Prod.snd,continuous_snd⟩

/-- Tensor factorization of a convergent sequence identifies its actual joint
limit with the product of the limiting scalar law and the fixed mark law. -/
theorem weakLimit_eq_prod_of_tensor_factorization
    (μ : ℕ → Measure (E × F)) (ρ : Measure (E × F)) (ν : Measure E) (π : Measure F)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] [IsFiniteMeasure π]
    (hjoint : External.WeakLawConverges μ ρ)
    (hfirst : External.WeakLawConverges (fun n => Measure.map Prod.fst (μ n)) ν)
    (hfactor : ∀ (G : E →ᵇ ℝ) (H : F →ᵇ ℝ),
      Tendsto (fun n => (∫ z,G z.1*H z.2 ∂μ n)-
        (∫ x,G x ∂Measure.map Prod.fst (μ n))*(∫ y,H y ∂π)) atTop (nhds 0)) :
    ρ = ν.prod π := by
  apply measure_eq_prod_of_tensor_bcf ν π
  intro G H
  have hlimit := (hjoint (tensorBCF G H)).sub ((hfirst G).mul_const (∫ y,H y ∂π))
  have heq : (∫ z,G z.1*H z.2 ∂ρ)-(∫ x,G x ∂ν)*(∫ y,H y ∂π)=0 :=
    tendsto_nhds_unique hlimit (hfactor G H)
  linarith

set_option maxHeartbeats 1500000 in
/-- A continuous indicator can encode a discrete retained-count stratum.
Factorization tested on that stratum identifies the full restricted joint
law; no conditional probability or division by its mass is required. -/
theorem weakLimit_restrict_eq_prod_of_tensor_factorization
    (μ : ℕ → Measure (E × F)) (ρ : Measure (E × F)) (ν : Measure E) (π : Measure F)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] [IsFiniteMeasure π]
    (χ : E →ᵇ ℝ) (hχ : ∀ x,χ x=0 ∨ χ x=1)
    (hjoint : External.WeakLawConverges μ ρ)
    (hfirst : External.WeakLawConverges (fun n => Measure.map Prod.fst (μ n)) ν)
    (hfactor : ∀ (G : E →ᵇ ℝ) (H : F →ᵇ ℝ),
      Tendsto (fun n => (∫ z,(G z.1*χ z.1)*H z.2 ∂μ n)-
        (∫ x,G x*χ x ∂Measure.map Prod.fst (μ n))*(∫ y,H y ∂π)) atTop (nhds 0)) :
    ρ.restrict (Prod.fst ⁻¹' {x | χ x=1}) = (ν.restrict {x | χ x=1}).prod π := by
  have hs : MeasurableSet {x : E | χ x=1} := isClosed_eq χ.continuous continuous_const |>.measurableSet
  apply measure_eq_prod_of_tensor_bcf (ν.restrict {x | χ x=1}) π
  intro G H
  have hlimit := (hjoint (tensorBCF (G*χ) H)).sub ((hfirst (G*χ)).mul_const (∫ y,H y ∂π))
  have heq : (∫ z,(G z.1*χ z.1)*H z.2 ∂ρ)-(∫ x,G x*χ x ∂ν)*(∫ y,H y ∂π)=0 :=
    tendsto_nhds_unique hlimit (hfactor G H)
  have hiρ : (∫ z,G z.1*H z.2 ∂ρ.restrict (Prod.fst ⁻¹' {x | χ x=1})) =
      ∫ z,(G z.1*χ z.1)*H z.2 ∂ρ := by
    rw [← integral_indicator (measurable_fst hs)]
    apply integral_congr_ae
    filter_upwards [] with z
    rcases hχ z.1 with hz | hz <;> simp [Set.indicator,hz]
  have hiν : (∫ x,G x ∂ν.restrict {x | χ x=1}) = ∫ x,G x*χ x ∂ν := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [] with x
    rcases hχ x with hx | hx <;> simp [Set.indicator,hx]
  rw [hiρ,hiν]
  linarith

end GeneralizedBulk.Analysis
