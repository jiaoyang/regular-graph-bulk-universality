import GeneralizedBulk.Exterior.StratifiedExterior
import GeneralizedBulk.Analysis.StratumAE

/-! Normalization gives actual simultaneous invertibility of the mixed raw
Gaussian field at every nonreal spectral point. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped ENNReal
namespace GeneralizedBulk.Gaussian
open Exterior Counting Analysis

theorem massMarkedMatrix_ae_isUnit
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters)
    (hlinear : ∀ᵐ s ∂ν,anchoredLinearCoefficient s=0)
    (hmass : ∀ᵐ s ∂ν,s.val.1.measure Set.univ=∞) :
    ∀ᵐ z ∂massMarkedLaw ν parameters,∀ w : NonrealSpectral,
      IsUnit (massMarkedMatrix ν hm parameters w.val z) := by
  let P := (infiniteBranchLaw ν hmass : Measure (MassState none))
  have hmap : Measure.map (Subtype.val : MassState none → AnchoredCountingState) P=ν :=
    infinite_branch_scalar_marginal ν hmass
  have hlin : ∀ᵐ s ∂P,anchoredLinearCoefficient (stratumPresentation none s).scalar=0 := by
    rw [← hmap] at hlinear
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable hlinear
  letI : Infinite (MassLabels none) := inferInstanceAs (Infinite ℕ)
  have hu := constructedMatrix_ae_isUnit P (stratumPresentation none)
    (measurable_stratumPresentation none)
    (massStratum_anchor_integrable ν hm (infiniteActive ν hmass)) parameters hlin
  rw [massMarkedLaw_eq_infinite_branch ν hmass parameters]
  apply (measurableEmbedding_sigma_mk (infiniteActive ν hmass)).ae_map_iff.mpr
  filter_upwards [hu] with z hz
  intro w
  exact hz w

end GeneralizedBulk.Gaussian
