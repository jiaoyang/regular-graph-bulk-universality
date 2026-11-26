import GeneralizedBulk.Exterior.ConstructedPositivity
import GeneralizedBulk.Exterior.JetLift
import GeneralizedBulk.Gaussian.RawAnalytic

/-!
# The actual exterior derivative jet is determined by its values

The raw field is differentiated through its genuine matrix inverse on the
common sign-definite event. Horizontal difference quotients then identify
the measurable derivative extraction used to lift exterior value laws.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.Exterior
open Gaussian

variable {I S : Type*} [Countable I] [MeasurableSpace S]
variable (P : Measure S) [IsProbabilityMeasure P]
variable (X : S → PresentedState I) (hX : Measurable X)
variable (hm : Integrable (fun x => ‖(X x).scalar.val.2‖) P)

/-- The true complex derivative of the exterior self-energy is its explicit
inverse-product slot. No derivative-jet identity is supplied as a premise. -/
theorem hasDerivAt_constructedExterior_ae [Infinite I] (parameters : Parameters)
    (hlinear : ∀ᵐ x ∂P, anchoredLinearCoefficient (X x).scalar = 0) :
    ∀ᵐ z ∂P.prod (iidLaw (markLaw parameters.p) I), ∀ w : NonrealSpectral,
      HasDerivAt (fun u => rawExterior
        (Marked.mean parameters (fun x => (X x).scalar) u z.1 +
          constructedField P X hX hm parameters (u, false) z))
        (rawExteriorDerivative (constructedMatrix P X hX hm parameters z w)
          (constructedDerivative P X hX hm parameters z w)) w.1 := by
  filter_upwards [hasDerivAt_constructedMatrix_ae P X hX hm parameters,
    constructedMatrix_ae_isUnit P X hX hm parameters hlinear] with z hd hu
  intro w
  have hmatrix : HasDerivAt (fun u =>
      Marked.mean parameters (fun x => (X x).scalar) u z.1 +
        constructedField P X hX hm parameters (u, false) z)
      (constructedDerivative P X hX hm parameters z w) w.1 :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (fun j => hd i j w.1 w.2))
  exact hasDerivAt_rawExterior hmatrix (hu w)

set_option maxHeartbeats 500000 in
/-- On a single event, every derivative slot of the actual exterior jet is
the horizontal derivative of its value slot. This supports all spectral
parameters simultaneously, in both half-planes. -/
theorem constructedJet_horizontalDifference_tendsto_ae [Infinite I] (parameters : Parameters)
    (hlinear : ∀ᵐ x ∂P, anchoredLinearCoefficient (X x).scalar = 0) :
    ∀ᵐ z ∂P.prod (iidLaw (markLaw parameters.p) I), ∀ w : NonrealSpectral,
      Tendsto (horizontalDifference (fun u =>
        (jetOfRaw (constructedScalar X z) (constructedMatrix P X hX hm parameters z)
          (constructedDerivative P X hX hm parameters z)).2 (u, false)) w)
        atTop (𝓝 ((jetOfRaw (constructedScalar X z) (constructedMatrix P X hX hm parameters z)
          (constructedDerivative P X hX hm parameters z)).2 (w, true))) := by
  filter_upwards [hasDerivAt_constructedExterior_ae P X hX hm parameters hlinear] with z hz
  intro w
  have ht := horizontalDifference_tendsto_of_hasDerivAt (w := w) (hz w)
  simpa only [jetOfRaw, Bool.false_eq_true, ↓reduceIte, constructedMatrix] using ht

/-- Only the law symmetry of the scalar/exterior values is needed. Analytic
construction supplies the derivative-jet symmetry used by the stationary flow. -/
theorem constructedJet_symmetry_of_value_law [Infinite I] (parameters : Parameters)
    (hlinear : ∀ᵐ x ∂P, anchoredLinearCoefficient (X x).scalar = 0)
    (Q : Mat)
    (hsym : Measure.map (action Q)
      (Measure.map (fun z => valueOfJet
        (jetOfRaw (constructedScalar X z) (constructedMatrix P X hX hm parameters z)
          (constructedDerivative P X hX hm parameters z)))
        (P.prod (iidLaw (markLaw parameters.p) I))) =
      Measure.map (fun z => valueOfJet
        (jetOfRaw (constructedScalar X z) (constructedMatrix P X hX hm parameters z)
          (constructedDerivative P X hX hm parameters z)))
        (P.prod (iidLaw (markLaw parameters.p) I))) :
    Measure.map (action Q)
      (Measure.map (fun z => jetOfRaw (constructedScalar X z)
        (constructedMatrix P X hX hm parameters z) (constructedDerivative P X hX hm parameters z))
        (P.prod (iidLaw (markLaw parameters.p) I))) =
      Measure.map (fun z => jetOfRaw (constructedScalar X z)
        (constructedMatrix P X hX hm parameters z) (constructedDerivative P X hX hm parameters z))
        (P.prod (iidLaw (markLaw parameters.p) I)) := by
  exact jet_law_symmetry_of_value_law _ _
    (measurable_jetOfRaw _ _ _ (measurable_constructedScalar X hX)
      (measurable_constructedMatrix P X hX hm parameters)
      (measurable_constructedDerivative P X hX hm parameters)) Q
    (constructedJet_horizontalDifference_tendsto_ae P X hX hm parameters hlinear) hsym

end GeneralizedBulk.Exterior
