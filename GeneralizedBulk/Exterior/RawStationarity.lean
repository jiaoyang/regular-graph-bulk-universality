import GeneralizedBulk.Exterior.RawCoordinates
import GeneralizedBulk.Exterior.Stationarity

/-!
# Stationarity transported back to the raw marked fields

All exterior coordinates are constructed from raw values and spectral
 derivatives. The expected raw polynomial response follows from exterior
switch and ordinary Gaussian-rotation laws, not a stationary-response premise.
-/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators ComplexOrder
namespace GeneralizedBulk.Exterior

/-- Construct exterior scalar and matrix jets from raw scalar/resolvent jets. -/
def jetOfRaw {I : Type*} (s : I → ℂ) (M L : I → Mat) : JetState I :=
  (fun w => rawExteriorScalar (s w) (M w) (L w),
    fun slot => if slot.2 then rawExteriorDerivative (M slot.1) (L slot.1)
      else rawExterior (M slot.1))

@[simp] theorem reconstructedMatrix_jetOfRaw {I : Type*} (s : I → ℂ) (M L : I → Mat)
    (w : I) (hM : IsUnit (M w)) :
    reconstructedMatrix (jetOfRaw s M L) w = M w := by
  have hK : (jetOfRaw s M L).2 (w, false) = rawExterior (M w) := rfl
  rw [reconstructedMatrix, hK]
  exact reconstruct_raw_matrix (M w) hM

@[simp] theorem reconstructedScalar_jetOfRaw {I : Type*} (s : I → ℂ) (M L : I → Mat)
    (w : I) (hM : IsUnit (M w)) :
    reconstructedScalar (jetOfRaw s M L) w = s w := by
  rw [reconstructedScalar, reconstructedMatrix_jetOfRaw s M L w hM]
  change rawExteriorScalar (s w) (M w) (L w) +
    Matrix.trace (M w * rawExteriorDerivative (M w) (L w)) = s w
  exact reconstruct_raw_scalar (s w) (M w) (L w) hM

@[simp] theorem reconstructedDerivative_jetOfRaw {I : Type*} (s : I → ℂ) (M L : I → Mat)
    (w : I) (hM : IsUnit (M w)) :
    reconstructedDerivative (jetOfRaw s M L) w = L w := by
  rw [reconstructedDerivative, reconstructedMatrix_jetOfRaw s M L w hM]
  change M w * rawExteriorDerivative (M w) (L w) * M w = L w
  exact reconstruct_raw_derivative (M w) (L w) hM

theorem measurable_jetOfRaw
    {Ω I : Type*} [MeasurableSpace Ω]
    (s : Ω → I → ℂ) (M L : Ω → I → Mat)
    (hs : ∀ w, Measurable (fun ω => s ω w))
    (hM : ∀ w, Measurable (fun ω => M ω w))
    (hL : ∀ w, Measurable (fun ω => L ω w)) :
    Measurable (fun ω => jetOfRaw (s ω) (M ω) (L ω)) := by
  have hinv (w : I) : Measurable (fun ω => (M ω w)⁻¹) := measurable_matrix_inverse.comp (hM w)
  have htrace : Measurable (Matrix.trace : Mat → ℂ) := continuous_id.matrix_trace.measurable
  refine (measurable_pi_lambda _ fun w => (hs w).sub
    (htrace.comp ((hinv w).mul (hL w)))).prodMk (measurable_pi_lambda _ fun slot => ?_)
  rcases slot with ⟨w, b⟩
  cases b
  · exact measurable_const.sub (hinv w)
  · exact ((hinv w).mul (hL w)).mul (hinv w)

def rawPolynomialObservable {I : Type*} {n : ℕ} (s : I → ℂ) (M : I → Mat)
    (w : I) (aux : Fin n → I) : ℂ :=
  Matrix.trace (signMatrix * M w) * ∏ j, s (aux j)

def rawPolynomialResponse {I : Type*} {n : ℕ} (s : I → ℂ) (M L : I → Mat)
    (w : I) (aux : Fin n → I) : ℂ :=
  Matrix.trace (signMatrix * matrixResponse (M w)) * ∏ j, s (aux j) +
    ∑ j, (Matrix.trace (signMatrix * M w) * (2 * Matrix.trace (signMatrix * L (aux j)))) *
      excludedProduct (fun a => s (aux a)) j

theorem polynomialObservable_jetOfRaw {I : Type*} {n : ℕ} (s : I → ℂ) (M L : I → Mat)
    (hM : ∀ w, IsUnit (M w)) (w : I) (aux : Fin n → I) :
    polynomialObservable w aux (jetOfRaw s M L) = rawPolynomialObservable s M w aux := by
  simp only [polynomialObservable, signObservable, reconstructedMatrix_jetOfRaw _ _ _ _ (hM _),
    reconstructedScalar_jetOfRaw _ _ _ _ (hM _), rawPolynomialObservable]

theorem polynomialResponse_jetOfRaw {I : Type*} {n : ℕ} (s : I → ℂ) (M L : I → Mat)
    (hM : ∀ w, IsUnit (M w)) (w : I) (aux : Fin n → I) :
    polynomialResponse w aux (jetOfRaw s M L) = rawPolynomialResponse s M L w aux := by
  simp only [polynomialResponse, signResponse, signObservable, scalarResponse, excludedProduct,
    reconstructedMatrix_jetOfRaw _ _ _ _ (hM _), reconstructedScalar_jetOfRaw _ _ _ _ (hM _),
    reconstructedDerivative_jetOfRaw _ _ _ _ (hM _), rawPolynomialResponse]

/-- The expected raw response is a theorem of the exterior construction. -/
theorem integral_rawPolynomialResponse_eq_zero
    {Ω I : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [SFinite P]
    (s : Ω → I → ℂ) (M L : Ω → I → Mat)
    (hs : ∀ w, Measurable (fun ω => s ω w))
    (hM : ∀ w, Measurable (fun ω => M ω w))
    (hL : ∀ w, Measurable (fun ω => L ω w))
    (w : I) (aux : Fin n → I)
    (hswitch : Measure.map (action GeneralizedSwitching.endpointPermutation)
      (Measure.map (fun ω => jetOfRaw (s ω) (M ω) (L ω)) P) =
        Measure.map (fun ω => jetOfRaw (s ω) (M ω) (L ω)) P)
    (hordinary : ∀ t : ℝ, Measure.map (action (ordinaryRotation t))
      (Measure.map (fun ω => jetOfRaw (s ω) (M ω) (L ω)) P) =
        Measure.map (fun ω => jetOfRaw (s ω) (M ω) (L ω)) P)
    (hpos : ∀ᵐ ω ∂P, ∀ u : I, ImaginarySignDefinite (M ω u))
    (hF : Integrable (fun ω => rawPolynomialObservable (s ω) (M ω) w aux) P)
    (hG : Integrable (fun ω => rawPolynomialResponse (s ω) (M ω) (L ω) w aux) P) :
    (∫ ω, rawPolynomialResponse (s ω) (M ω) (L ω) w aux ∂P) = 0 := by
  let jet := fun ω => jetOfRaw (s ω) (M ω) (L ω)
  have hjet := measurable_jetOfRaw s M L hs hM hL
  have hunit : ∀ᵐ ω ∂P, ∀ u : I, IsUnit (M ω u) := by
    filter_upwards [hpos] with ω hp
    intro u
    exact isUnit_of_imaginary_signDefinite _ (hp u)
  have hpositive : ∀ᵐ ω ∂P, ∀ u : I, ImaginarySignDefinite ((jet ω).2 (u, false)) := by
    filter_upwards [hpos] with ω hp
    intro u
    exact rawExterior_imaginary_signDefinite _ (hp u)
  have hFeq : (fun ω => rawPolynomialObservable (s ω) (M ω) w aux) =ᵐ[P]
      (fun ω => polynomialObservable w aux (jet ω)) := by
    filter_upwards [hunit] with ω hu
    exact (polynomialObservable_jetOfRaw _ _ _ hu w aux).symm
  have hGeq : (fun ω => rawPolynomialResponse (s ω) (M ω) (L ω) w aux) =ᵐ[P]
      (fun ω => polynomialResponse w aux (jet ω)) := by
    filter_upwards [hunit] with ω hu
    exact (polynomialResponse_jetOfRaw _ _ _ hu w aux).symm
  have hzero := integral_polynomialResponse_pullback_eq_zero P jet hjet w aux
    hswitch hordinary hpositive (hF.congr hFeq) (hG.congr hGeq)
  rw [integral_congr_ae hGeq]
  exact hzero

end GeneralizedBulk.Exterior
