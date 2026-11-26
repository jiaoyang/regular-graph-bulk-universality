import GeneralizedBulk.GaussianContractions
import GeneralizedBulk.Loop.Hierarchy

/-!
# Constructing loop contractions from entrywise Wick covariance

The `false` slot records a centered matrix value, while the `true` slot is
intended to record its spectral derivative. The actual analytic derivative
identification and the Wick covariance of the Gaussian marked series remain
to be constructed. The slot-kernel identities below state the precise entries
needed for that construction, rather than assuming the resulting trace
contractions or the final scalar hierarchy.
-/

noncomputable section
open MeasureTheory BourgadeHuang

namespace GeneralizedBulk.Marked

abbrev SpectralSlot := ℂ × Bool

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

/-- The deterministic mean in the raw endpoint resolvent. -/
def mean (parameters : Parameters) (X : S → AnchoredCountingState) (w : ℂ) (x : S) :
    EndpointMatrix :=
  let g := (parameters.center : ℂ) + (parameters.scale : ℂ) * anchoredNevanlinna (X x) w
  GeneralizedSwitching.meanMatrix g ((parameters.p : ℂ) * g + parameters.r) 0

def markedMatrix (parameters : Parameters) (X : S → AnchoredCountingState)
    (Z : S → SpectralSlot → T → EndpointMatrix) (w : ℂ) (x : S) (γ : T) :
    EndpointMatrix := mean parameters X w x + Z x (w, false) γ

def h (Z : S → SpectralSlot → T → EndpointMatrix) (w : ℂ) (x : S) (γ : T) : ℂ :=
  Matrix.trace (signMatrix * Z x (w, false) γ)

def ds (Z : S → SpectralSlot → T → EndpointMatrix) (w : ℂ) (x : S) (γ : T) : ℂ :=
  2 * Matrix.trace (signMatrix * Z x (w, true) γ)

def dh (parameters : Parameters) (X : S → AnchoredCountingState)
    (Z : S → SpectralSlot → T → EndpointMatrix) (w : ℂ) (x : S) (γ : T) : ℂ :=
  Matrix.trace (signMatrix * matrixResponse (markedMatrix parameters X Z w x γ))

omit [MeasurableSpace S] [MeasurableSpace T] in
/-- The centered sign trace equals the sign trace of the full raw matrix;
the real background in the mean is retained. -/
theorem h_eq_trace_marked (parameters : Parameters) (X : S → AnchoredCountingState)
    (Z : S → SpectralSlot → T → EndpointMatrix) (w : ℂ) (x : S) (γ : T) :
    h Z w x γ = Matrix.trace (signMatrix * markedMatrix parameters X Z w x γ) := by
  simp [markedMatrix, mean, mul_add, Matrix.trace_add, trace_sign_mean, h]

/-- Concrete fiber data to be supplied by the Gaussian series and its spectral
derivative. This is a new analytic obligation, not part of external BS or HY. -/
structure WickFiberData (P : Measure S) (Q : Measure T)
    (parameters : Parameters) (X : S → AnchoredCountingState)
    (kernel : S → SpectralSlot → SpectralSlot → ℂ)
    (Z : S → SpectralSlot → T → EndpointMatrix) : Prop where
  entry_wick : ∀ᵐ x ∂P, EntryWickCovariance Q (parameters.p : ℂ)
    (parameters.scale : ℂ) (kernel x) (Z x)
  diagonal_kernel : ∀ w : ℂ, w.im ≠ 0 → ∀ᵐ x ∂P,
    kernel x (w, false) (w, false) = anchoredDerivative (X x) w
  interaction_kernel : ∀ w u : ℂ, w.im ≠ 0 → u.im ≠ 0 → ∀ᵐ x ∂P,
    kernel x (w, false) (u, true) = anchoredInteraction (X x) w u

/-- Polynomial integrability and stationarity to be derived from the exterior
flow. No Gaussian contractions or scalar loop equations are assumed here. -/
structure StationaryWeightedResponse (P : Measure S) (Q : Measure T)
    (parameters : Parameters) (X : S → AnchoredCountingState)
    (Z : S → SpectralSlot → T → EndpointMatrix) : Prop where
  weighted_drift_integrable : ∀ n : ℕ, ∀ w : ℂ, w.im ≠ 0 →
    ∀ aux : Fin n → ℂ, (∀ j, (aux j).im ≠ 0) →
      Integrable (fun z : S × T => dh parameters X Z w z.1 z.2 *
        Loop.scalarProduct (X z.1) aux) (P.prod Q)
  weighted_cross_integrable : ∀ n : ℕ, ∀ w : ℂ, w.im ≠ 0 →
    ∀ aux : Fin n → ℂ, (∀ j, (aux j).im ≠ 0) → ∀ j : Fin n,
      Integrable (fun z : S × T => (h Z w z.1 z.2 * ds Z (aux j) z.1 z.2) *
        Loop.scalarExcludedProduct (X z.1) aux j) (P.prod Q)
  stationary : ∀ n : ℕ, ∀ w : ℂ, w.im ≠ 0 →
    ∀ aux : Fin n → ℂ, (∀ j, (aux j).im ≠ 0) →
      (∫ z, Loop.responseObservable X (h Z) (dh parameters X Z) (ds Z) w aux z
        ∂P.prod Q) = 0

/-- Entrywise Wick covariance proves both trace contractions, which then
construct the loop-closure interface. The hierarchy is not a hypothesis. -/
theorem productResponseIdentities
    (P : Measure S) (Q : Measure T) [IsProbabilityMeasure Q]
    (parameters : Parameters) (X : S → AnchoredCountingState)
    (kernel : S → SpectralSlot → SpectralSlot → ℂ)
    (Z : S → SpectralSlot → T → EndpointMatrix)
    (wick : WickFiberData P Q parameters X kernel Z)
    (flow : StationaryWeightedResponse P Q parameters X Z) :
    Loop.ProductResponseIdentities P Q X (parameters.contractionCoefficient : ℂ)
      (h Z) (dh parameters X Z) (ds Z) := by
  refine ⟨?_, ?_, ?_, ?_, flow.weighted_drift_integrable,
    flow.weighted_cross_integrable, flow.stationary⟩
  · intro w hw
    filter_upwards [wick.entry_wick] with x hx
    exact hx.integrable_shifted_drift _ _ (w, false)
  · intro w u hw hu
    filter_upwards [wick.entry_wick] with x hx
    have hi := (hx.integrable_sign_trace_product (w, false) (u, true)).const_mul 2
    convert hi using 1
    funext γ
    simp only [h, ds]
    ring
  · intro w hw
    filter_upwards [wick.entry_wick, wick.diagonal_kernel w hw] with x hx hdiag
    have hd := calibrated_wick_drift parameters hx (anchoredNevanlinna (X x) w) (w, false)
    rw [hdiag] at hd
    exact hd
  · intro w u hw hu
    filter_upwards [wick.entry_wick, wick.interaction_kernel w u hw hu] with x hx hker
    have heq : (fun γ => h Z w x γ * ds Z u x γ) =
        (fun γ => 2 * (Matrix.trace (signMatrix * Z x (w, false) γ) *
          Matrix.trace (signMatrix * Z x (u, true) γ))) := by
      funext γ
      simp only [h, ds]
      ring
    rw [heq, integral_const_mul, hx.sign_trace_covariance, hker]
    unfold Parameters.contractionCoefficient
    push_cast
    ring

end GeneralizedBulk.Marked
