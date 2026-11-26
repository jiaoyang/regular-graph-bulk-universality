import GeneralizedBulk.Exterior.FiniteJetCoordinates
import GeneralizedBulk.Analysis.AEContinuousMapping

/-! Actual joint raw jet laws pass to exterior value laws through the
almost-sure inverse, without a uniform determinant lower bound. -/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.Exterior
open Graph Analysis

theorem weakLaw_finiteJetExterior {I : Type*} [Fintype I]
    (μ : ℕ → Measure (FiniteRawJet I)) [∀ n,IsProbabilityMeasure (μ n)]
    (ν : Measure (FiniteRawJet I)) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges μ ν)
    (hu : ∀ᵐ v ∂ν,∀ i,IsUnit (finiteRawJetMatrix v i false)) :
    External.WeakLawConverges (fun n => (μ n).map finiteJetExterior)
      (ν.map finiteJetExterior) := by
  let e := rawFieldRealHomeomorph I
  let f := e ∘ finiteJetExterior
  have hf : Measurable f := e.continuous.measurable.comp measurable_finiteJetExterior
  have hm := weakLaw_map_of_ae_continuous μ ν hweak f hf
    (hu.mono (fun v hv => e.continuous.continuousAt.comp (continuousAt_finiteJetExterior v hv)))
  have hall := weakLaw_map _ _ hm e.symm e.symm.continuous
  have hcomp : e.symm ∘ f=finiteJetExterior := by
    funext v
    exact e.symm_apply_apply (finiteJetExterior v)
  simpa only [Measure.map_map e.symm.continuous.measurable hf,hcomp] using hall

end GeneralizedBulk.Exterior
