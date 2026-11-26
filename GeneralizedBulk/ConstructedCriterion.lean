import GeneralizedBulk.Main
import GeneralizedBulk.Exterior.ConstructedStationarity
import GeneralizedBulk.Exterior.JetLift
import GeneralizedBulk.Exterior.ConstructedJetDerivative
import GeneralizedBulk.Analysis.NoLinearTerm

/-!
# The constructed Gaussian marked switching criterion

The analytic response and Wick interfaces are proved by construction. The
remaining model hypothesis is the literal joint exterior switching symmetry.
BS and HY are needed upstream for graph limits, not for this ensemble-free
criterion. The loop characterization is the imported theorem at beta one.
-/
noncomputable section
open MeasureTheory BourgadeHuang

namespace GeneralizedBulk
open Gaussian Exterior
variable {I S : Type*} [Countable I] [MeasurableSpace S]
variable (P : Measure S) [IsProbabilityMeasure P]
variable (X : S → PresentedState I) (hX : Measurable X)
variable (hm1 : Integrable (fun x => ‖(X x).scalar.val.2‖) P)

/-- The actual exterior jet, obtained by inversion of the constructed raw
Gaussian matrix. Invertibility on the common event is a proved theorem. -/
def gaussianExteriorJet (parameters : Parameters) (z : S × (I → (Fin 4 → ℝ))) :
    JetState NonrealSpectral :=
  jetOfRaw (constructedScalar X z) (constructedMatrix P X hX hm1 parameters z)
    (constructedDerivative P X hX hm1 parameters z)

/-- The full exterior scalar together with matrix values, as in the
manuscript's `(tau,K)` symmetry; no derivative coordinate occurs here. -/
def gaussianExterior (parameters : Parameters) (z : S × (I → (Fin 4 → ℝ))) :
    ValueState := valueOfJet (gaussianExteriorJet P X hX hm1 parameters z)

theorem measurable_gaussianExteriorJet (parameters : Parameters) :
    Measurable (gaussianExteriorJet P X hX hm1 parameters) :=
  measurable_jetOfRaw _ _ _ (measurable_constructedScalar X hX)
    (measurable_constructedMatrix P X hX hm1 parameters)
    (measurable_constructedDerivative P X hX hm1 parameters)

theorem measurable_gaussianExterior (parameters : Parameters) :
    Measurable (gaussianExterior P X hX hm1 parameters) :=
  measurable_valueOfJet.comp (measurable_gaussianExteriorJet P X hX hm1 parameters)

/-- A checked intermediate endpoint with the actual exterior derivative jet.
Neither covariance, positivity, weighted integrability, nor expected
stationarity is an additional premise. -/
theorem identify_of_gaussian_jet_switching [Infinite I] (parameters : Parameters)
    (hm : ∀ q : ℕ, Integrable (fun x => ‖(X x).scalar.val.2‖ ^ q) P)
    (hlinear : ∀ᵐ x ∂P, anchoredLinearCoefficient (X x).scalar = 0)
    (hswitch : Measure.map (action GeneralizedSwitching.endpointPermutation)
      (Measure.map (gaussianExteriorJet P X hX hm1 parameters)
        (P.prod (iidLaw (markLaw parameters.p) I))) =
      Measure.map (gaussianExteriorJet P X hX hm1 parameters)
        (P.prod (iidLaw (markLaw parameters.p) I))) :
    Measure.map (fun x => (X x).scalar.val.1) P = sineOneLaw := by
  exact identify_of_wick_and_stationary_response parameters P (iidLaw (markLaw parameters.p) I)
    (fun x => (X x).scalar) (PresentedState.measurable_scalar.comp hX) hm
    (fun x => particleKernel (X x).scalar) (constructedZ P X hX hm1 parameters)
    (constructedZ_wickFiberData P X hX hm1 parameters hlinear)
    (constructed_stationaryWeightedResponse P X hX hm1 parameters hm hlinear hswitch)

/-- The generalized marked switching criterion with the actual Gaussian
series and exterior flow fully constructed. The single symmetry assumption is
the joint law of `(tau,K)`; derivative-jet symmetry is derived measurably. -/
theorem identify_of_gaussian_exterior_switching [Infinite I] (parameters : Parameters)
    (hm : ∀ q : ℕ, Integrable (fun x => ‖(X x).scalar.val.2‖ ^ q) P)
    (hlinear : ∀ᵐ x ∂P, anchoredLinearCoefficient (X x).scalar = 0)
    (hswitch : Measure.map (action GeneralizedSwitching.endpointPermutation)
      (Measure.map (gaussianExterior P X hX hm1 parameters)
        (P.prod (iidLaw (markLaw parameters.p) I))) =
      Measure.map (gaussianExterior P X hX hm1 parameters)
        (P.prod (iidLaw (markLaw parameters.p) I))) :
    Measure.map (fun x => (X x).scalar.val.1) P = sineOneLaw := by
  apply identify_of_gaussian_jet_switching P X hX hm1 parameters hm hlinear
  exact constructedJet_symmetry_of_value_law P X hX hm1 parameters hlinear
    GeneralizedSwitching.endpointPermutation hswitch

/-- In a microscopic limit, uniform imaginary-height moments discharge the
zero-affine-coefficient condition rather than adding it to the assumptions. -/
theorem identify_of_uniform_height_gaussian_exterior_switching [Infinite I]
    (parameters : Parameters)
    (hm : ∀ q : ℕ, Integrable (fun x => ‖(X x).scalar.val.2‖ ^ q) P)
    (C : ℝ) (hheight : ∀ n : ℕ,
      (∫ x, ‖anchoredNevanlinna (X x).scalar
        (((n : ℝ) + 1 : ℝ) * Complex.I)‖ ∂P) ≤ C)
    (hswitch : Measure.map (action GeneralizedSwitching.endpointPermutation)
      (Measure.map (gaussianExterior P X hX hm1 parameters)
        (P.prod (iidLaw (markLaw parameters.p) I))) =
      Measure.map (gaussianExterior P X hX hm1 parameters)
        (P.prod (iidLaw (markLaw parameters.p) I))) :
    Measure.map (fun x => (X x).scalar.val.1) P = sineOneLaw := by
  exact identify_of_gaussian_exterior_switching P X hX hm1 parameters hm
    (Analysis.anchoredLinearCoefficient_eq_zero_ae_of_uniform_height P
      (fun x => (X x).scalar) (PresentedState.measurable_scalar.comp hX) hm1 C hheight) hswitch

end GeneralizedBulk
