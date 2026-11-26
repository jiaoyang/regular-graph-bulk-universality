import GeneralizedBulk.Gaussian.StratifiedConstruction
import GeneralizedBulk.Gaussian.RawAnalytic
import GeneralizedBulk.Graph.RawPairCompactness
import GeneralizedBulk.Analysis.StratumAE

/-! Genuine measurable value/derivative coordinates for the mass-stratified
Gaussian marking, before infinite-particle normalization. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.Gaussian
open Analysis Counting Exterior Graph
variable (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
variable (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)

def massMarkedDerivative (parameters : Parameters) (w : ℂ) (z : MassMarkedSample ν) : EndpointMatrix :=
  ((parameters.scale : ℂ)*anchoredDerivative (massScalarState ν z) w) •
      covarianceMatrix (parameters.p : ℂ) + massCenteredField ν hm parameters (w,true) z

theorem measurable_massMarkedMatrix (parameters : Parameters) {w : ℂ} (hw : w.im ≠ 0) :
    Measurable (massMarkedMatrix ν hm parameters w) := by
  have hs := (continuous_anchoredNevanlinna hw).measurable.comp (measurable_massScalarState ν)
  have hmean : Measurable (fun z => Marked.mean parameters id w (massScalarState ν z)) := by
    simp_rw [mean_eq_covariance]
    exact ((measurable_const.add (hs.const_mul (parameters.scale : ℂ))).smul measurable_const).add measurable_const
  exact hmean.add (measurable_massCenteredField ν hm parameters (w,false))

theorem measurable_massMarkedDerivative (parameters : Parameters) {w : ℂ} (hw : w.im ≠ 0) :
    Measurable (massMarkedDerivative ν hm parameters w) := by
  have hs := (continuous_anchoredDerivative hw).measurable.comp (measurable_massScalarState ν)
  exact ((hs.const_mul (parameters.scale : ℂ)).smul measurable_const).add
    (measurable_massCenteredField ν hm parameters (w,true))

theorem hasDerivAt_massMarkedMatrix_ae (parameters : Parameters) :
    ∀ᵐ z ∂massMarkedLaw ν parameters,∀ i j : Fin 4,∀ w : ℂ,∀ hw : w.im ≠ 0,
      HasDerivAt (fun u => massMarkedMatrix ν hm parameters u z i j)
        (massMarkedDerivative ν hm parameters w z i j) w := by
  apply ae_stratumMarkedLaw_of_fibers ν massClass measurable_massClass (MassMarkSpace ν)
    (fun a => iidLaw (markLaw parameters.p) (MassLabels a.val))
  intro a
  have hd := hasDerivAt_constructedMatrix_ae (massStratumLaw ν a : Measure (MassState a.val))
    (stratumPresentation a.val) (measurable_stratumPresentation a.val)
    (massStratum_anchor_integrable ν hm a) parameters
  filter_upwards [hd] with z hz
  intro i j w hw
  have hh := hz i j w hw
  simpa only [massMarkedMatrix,massMarkedDerivative,massCenteredField,constructedDerivative,
    massScalarState,stratumSampleValue,stratumPresentation_scalar] using hh

def massRawCoordinate (parameters : Parameters) (z : MassMarkedSample ν)
    (w : ℂ) (j : RawComplexCoordinate) : ℂ :=
  if w.im=0 then 0 else
    match j with
    | Sum.inl _ => anchoredNevanlinna (massScalarState ν z) w
    | Sum.inr ij => massMarkedMatrix ν hm parameters w z ij.1 ij.2

def massRawCoordinateDerivative (parameters : Parameters) (z : MassMarkedSample ν)
    (w : ℂ) (j : RawComplexCoordinate) : ℂ :=
  if w.im=0 then 0 else
    match j with
    | Sum.inl _ => anchoredDerivative (massScalarState ν z) w
    | Sum.inr ij => massMarkedDerivative ν hm parameters w z ij.1 ij.2

theorem measurable_massRawCoordinate (parameters : Parameters) (w : ℂ) :
    Measurable (fun z => massRawCoordinate ν hm parameters z w) := by
  apply measurable_pi_lambda
  intro j
  by_cases hw : w.im=0
  · simp only [massRawCoordinate,hw,↓reduceIte]
    exact measurable_const
  · cases j with
    | inl u =>
      simp only [massRawCoordinate,hw,↓reduceIte]
      exact (continuous_anchoredNevanlinna hw).measurable.comp (measurable_massScalarState ν)
    | inr ij =>
      simp only [massRawCoordinate,hw,↓reduceIte]
      exact (show Continuous (fun A : EndpointMatrix => A ij.1 ij.2) from
        (continuous_apply ij.2).comp (continuous_apply ij.1)).measurable.comp
        (measurable_massMarkedMatrix ν hm parameters hw)

theorem measurable_massRawCoordinateDerivative (parameters : Parameters) (w : ℂ) :
    Measurable (fun z => massRawCoordinateDerivative ν hm parameters z w) := by
  apply measurable_pi_lambda
  intro j
  by_cases hw : w.im=0
  · simp only [massRawCoordinateDerivative,hw,↓reduceIte]
    exact measurable_const
  · cases j with
    | inl u =>
      simp only [massRawCoordinateDerivative,hw,↓reduceIte]
      exact (continuous_anchoredDerivative hw).measurable.comp (measurable_massScalarState ν)
    | inr ij =>
      simp only [massRawCoordinateDerivative,hw,↓reduceIte]
      exact (show Continuous (fun A : EndpointMatrix => A ij.1 ij.2) from
        (continuous_apply ij.2).comp (continuous_apply ij.1)).measurable.comp
        (measurable_massMarkedDerivative ν hm parameters hw)

theorem hasDerivAt_massRawCoordinate_ae (parameters : Parameters) :
    ∀ᵐ z ∂massMarkedLaw ν parameters,∀ w : ℂ,∀ hw : w.im ≠ 0,∀ j : RawComplexCoordinate,
      HasDerivAt (fun u => massRawCoordinate ν hm parameters z u j)
        (massRawCoordinateDerivative ν hm parameters z w j) w := by
  filter_upwards [hasDerivAt_massMarkedMatrix_ae ν hm parameters] with z hz
  intro w hw j
  have hnhds : ∀ᶠ u in 𝓝 w,u.im ≠ 0 :=
    (isOpen_ne_fun Complex.continuous_im continuous_const).mem_nhds hw
  cases j with
  | inl a =>
    simp only [massRawCoordinateDerivative,hw,↓reduceIte]
    apply (hasDerivAt_anchoredNevanlinna (massScalarState ν z) hw).congr_of_eventuallyEq
    filter_upwards [hnhds] with u hu
    simp only [massRawCoordinate,hu,↓reduceIte]
  | inr ij =>
    simp only [massRawCoordinateDerivative,hw,↓reduceIte]
    apply (hz ij.1 ij.2 w hw).congr_of_eventuallyEq
    filter_upwards [hnhds] with u hu
    simp only [massRawCoordinate,hu,↓reduceIte]

end GeneralizedBulk.Gaussian
