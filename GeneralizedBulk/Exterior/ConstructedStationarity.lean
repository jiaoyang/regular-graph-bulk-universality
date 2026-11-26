import GeneralizedBulk.Exterior.ConstructedPositivity
import GeneralizedBulk.Gaussian.WeightedResponse

/-!
# Polynomial stationarity of the actual Gaussian marked field

The actual rotation, inverse calculus, Gaussian law, and weighted moment
bounds construct the stationary response interface from the exterior switch
symmetry. Expected stationarity is a conclusion, not a model premise.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped BigOperators
namespace GeneralizedBulk.Exterior
open Gaussian

variable {I S : Type*} [Countable I] [MeasurableSpace S]
variable (P : Measure S) [IsProbabilityMeasure P]
variable (X : S → PresentedState I) (hX : Measurable X)
variable (hm1 : Integrable (fun x => ‖(X x).scalar.val.2‖) P)

@[simp] theorem constructedMatrix_eq_markedMatrix (parameters : Parameters)
    (z : S × (I → (Fin 4 → ℝ))) (w : NonrealSpectral) :
    constructedMatrix P X hX hm1 parameters z w =
      Marked.markedMatrix parameters (fun x => (X x).scalar)
        (constructedZ P X hX hm1 parameters) w.1 z.1 z.2 := rfl

/-- The raw sign trace already equals the centered marked observable. -/
theorem trace_constructedMatrix_eq_h (parameters : Parameters)
    (z : S × (I → (Fin 4 → ℝ))) (w : NonrealSpectral) :
    Matrix.trace (signMatrix * constructedMatrix P X hX hm1 parameters z w) =
      Marked.h (constructedZ P X hX hm1 parameters) w.1 z.1 z.2 :=
  (Marked.h_eq_trace_marked parameters (fun x => (X x).scalar)
    (constructedZ P X hX hm1 parameters) w.1 z.1 z.2).symm

/-- The actual raw flow response is precisely the already defined marked
polynomial response, including every differentiated auxiliary channel. -/
theorem rawPolynomialResponse_constructed (parameters : Parameters)
    {n : ℕ} (w : NonrealSpectral) (aux : Fin n → NonrealSpectral)
    (z : S × (I → (Fin 4 → ℝ))) :
    rawPolynomialResponse (constructedScalar X z)
      (constructedMatrix P X hX hm1 parameters z)
      (constructedDerivative P X hX hm1 parameters z) w aux =
    Loop.responseObservable (fun x => (X x).scalar)
      (Marked.h (constructedZ P X hX hm1 parameters))
      (Marked.dh parameters (fun x => (X x).scalar) (constructedZ P X hX hm1 parameters))
      (Marked.ds (constructedZ P X hX hm1 parameters)) w.1 (fun j => (aux j).1) z := by
  simp only [rawPolynomialResponse, trace_constructedMatrix_eq_h,
    ← ds_eq_trace_constructedDerivative, constructedScalar,
    Loop.responseObservable, Loop.scalarProduct, Loop.scalarExcludedProduct, Marked.dh,
    constructedMatrix_eq_markedMatrix,
    ← Marked.h_eq_trace_marked parameters (fun x => (X x).scalar)
      (constructedZ P X hX hm1 parameters)]

/-- Under the exterior switch law, the actual Gaussian model has vanishing
expected response for every polynomial, with upper and lower parameters mixed. -/
theorem constructed_response_integral_eq_zero [Infinite I] (parameters : Parameters)
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(X x).scalar.val.2‖ ^ n) P)
    (hlinear : ∀ᵐ x ∂P, anchoredLinearCoefficient (X x).scalar = 0)
    (hswitch : Measure.map (action GeneralizedSwitching.endpointPermutation)
      (Measure.map (fun z => jetOfRaw (constructedScalar X z)
        (constructedMatrix P X hX hm1 parameters z) (constructedDerivative P X hX hm1 parameters z))
        (P.prod (iidLaw (markLaw parameters.p) I))) =
      Measure.map (fun z => jetOfRaw (constructedScalar X z)
        (constructedMatrix P X hX hm1 parameters z) (constructedDerivative P X hX hm1 parameters z))
        (P.prod (iidLaw (markLaw parameters.p) I)))
    {n : ℕ} {w : ℂ} (hw : w.im ≠ 0) (aux : Fin n → ℂ) (ha : ∀ j, (aux j).im ≠ 0) :
    (∫ z, Loop.responseObservable (fun x => (X x).scalar)
      (Marked.h (constructedZ P X hX hm1 parameters))
      (Marked.dh parameters (fun x => (X x).scalar) (constructedZ P X hX hm1 parameters))
      (Marked.ds (constructedZ P X hX hm1 parameters)) w aux z
        ∂P.prod (iidLaw (markLaw parameters.p) I)) = 0 := by
  let w' : NonrealSpectral := ⟨w, hw⟩
  let aux' : Fin n → NonrealSpectral := fun j => ⟨aux j, ha j⟩
  have hF : Integrable (fun z => rawPolynomialObservable (constructedScalar X z)
      (constructedMatrix P X hX hm1 parameters z) w' aux')
      (P.prod (iidLaw (markLaw parameters.p) I)) := by
    simpa only [rawPolynomialObservable, constructedScalar, constructedMatrix_eq_markedMatrix,
      w', aux'] using Response.constructed_polynomialObservable_integrable P X hX hm1 parameters hm w aux ha
  have hG : Integrable (fun z => rawPolynomialResponse (constructedScalar X z)
      (constructedMatrix P X hX hm1 parameters z) (constructedDerivative P X hX hm1 parameters z) w' aux')
      (P.prod (iidLaw (markLaw parameters.p) I)) := by
    simp_rw [rawPolynomialResponse_constructed]
    exact Response.constructed_responseObservable_integrable P X hX hm1 parameters hm hw aux ha
  have hzero := integral_rawPolynomialResponse_eq_zero
    (P.prod (iidLaw (markLaw parameters.p) I)) (constructedScalar X)
    (constructedMatrix P X hX hm1 parameters) (constructedDerivative P X hX hm1 parameters)
    (measurable_constructedScalar X hX) (measurable_constructedMatrix P X hX hm1 parameters)
    (measurable_constructedDerivative P X hX hm1 parameters) w' aux' hswitch
    (constructedJet_ordinary_law P X hX hm1 parameters)
    (constructedMatrix_ae_signDefinite P X hX hm1 parameters hlinear) hF hG
  simpa only [rawPolynomialResponse_constructed, w', aux'] using hzero

/-- The weighted stationary response interface is now constructed from actual
series and symmetries, with no analytic or probabilistic response assumptions. -/
theorem constructed_stationaryWeightedResponse [Infinite I] (parameters : Parameters)
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(X x).scalar.val.2‖ ^ n) P)
    (hlinear : ∀ᵐ x ∂P, anchoredLinearCoefficient (X x).scalar = 0)
    (hswitch : Measure.map (action GeneralizedSwitching.endpointPermutation)
      (Measure.map (fun z => jetOfRaw (constructedScalar X z)
        (constructedMatrix P X hX hm1 parameters z) (constructedDerivative P X hX hm1 parameters z))
        (P.prod (iidLaw (markLaw parameters.p) I))) =
      Measure.map (fun z => jetOfRaw (constructedScalar X z)
        (constructedMatrix P X hX hm1 parameters z) (constructedDerivative P X hX hm1 parameters z))
        (P.prod (iidLaw (markLaw parameters.p) I))) :
    Marked.StationaryWeightedResponse P (iidLaw (markLaw parameters.p) I) parameters
      (fun x => (X x).scalar) (constructedZ P X hX hm1 parameters) := by
  constructor
  · intro n w hw aux ha
    exact Response.constructed_weighted_drift_integrable P X hX hm1 parameters hm hw aux ha
  · intro n w hw aux ha j
    exact Response.constructed_weighted_cross_integrable P X hX hm1 parameters hm w aux ha j
  · intro n w hw aux ha
    exact constructed_response_integral_eq_zero P X hX hm1 parameters hm hlinear hswitch hw aux ha

end GeneralizedBulk.Exterior
