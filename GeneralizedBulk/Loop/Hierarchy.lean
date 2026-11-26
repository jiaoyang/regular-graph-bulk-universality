import BourgadeHuang.RationalBulk.Theorem15
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Closing the microscopic loop hierarchy

This module proves the passage from a stationary marked response and its two
conditional (fiber) contractions to the literal Bourgade--Huang bulk hierarchy.
The scalar-state probability space and the independent mark probability space
are explicit. Fubini and every use of integral additivity have integrability
hypotheses; an undefined Bochner integral cannot create the loop equation.

`ProductResponseIdentities` is an intermediate analytic interface. Constructing
it from the Gaussian marked series and exterior switching symmetry remains a
separate proof obligation. It is not an external BS/HY assumption, and its fields
do not assume the loop hierarchy or the desired point-process law.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory BourgadeHuang

namespace GeneralizedBulk.Loop

/-- Scalar part of the drift in the beta-one loop equation. -/
def scalarDrift (X : AnchoredCountingState) (w : ℂ) : ℂ :=
  anchoredDerivative X w + anchoredNevanlinna X w ^ 2 + 1

/-- Product of the scalar observables in the auxiliary channels. -/
def scalarProduct {n : ℕ} (X : AnchoredCountingState) (aux : Fin n → ℂ) : ℂ :=
  ∏ j, anchoredNevanlinna X (aux j)

/-- Product with the differentiated auxiliary channel removed. -/
def scalarExcludedProduct {n : ℕ} (X : AnchoredCountingState)
    (aux : Fin n → ℂ) (j : Fin n) : ℂ :=
  excludedProduct (fun k => anchoredNevanlinna X (aux k)) j

/-- At beta one the coefficients are exactly one and two. The identity also
covers an empty auxiliary family and repeated parameters. -/
theorem loopIntegrand_one {n : ℕ} (X : AnchoredCountingState)
    (w : ℂ) (aux : Fin n → ℂ) :
    RationalBulk.loopIntegrand 1 X w aux =
      scalarDrift X w * scalarProduct X aux +
        2 * ∑ j, anchoredInteraction X w (aux j) * scalarExcludedProduct X aux j := by
  norm_num [RationalBulk.loopIntegrand, scalarDrift, scalarProduct, scalarExcludedProduct]

/-- The expanded derivative of `h(w) * product_j s(aux_j)`. It uses only a
scalar observable, its flow derivative, and the scalar field's flow response. -/
def responseObservable {S T : Type*} {n : ℕ}
    (X : S → AnchoredCountingState)
    (h dh ds : ℂ → S → T → ℂ) (w : ℂ) (aux : Fin n → ℂ) (z : S × T) : ℂ :=
  dh w z.1 z.2 * scalarProduct (X z.1) aux +
    ∑ j, (h w z.1 z.2 * ds (aux j) z.1 z.2) *
      scalarExcludedProduct (X z.1) aux j

/-- Explicit analytic identities supplied by the marked limit.

`dh` represents the flow derivative of `h`, while `ds` represents the flow
response of the scalar field. Their interpretations must be proved when this
structure is constructed. The contraction fields are actual integrals over the
independent mark probability space, conditional on the entire scalar state.
No restriction to one half-plane or to distinct parameters is imposed. -/
structure ProductResponseIdentities
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (P : Measure S) (Q : Measure T) (X : S → AnchoredCountingState)
    (κ : ℂ) (h dh ds : ℂ → S → T → ℂ) : Prop where
  drift_integrable : ∀ w : ℂ, w.im ≠ 0 →
    ∀ᵐ x ∂P, Integrable (dh w x) Q
  cross_integrable : ∀ w u : ℂ, w.im ≠ 0 → u.im ≠ 0 →
    ∀ᵐ x ∂P, Integrable (fun γ => h w x γ * ds u x γ) Q
  drift_contraction : ∀ w : ℂ, w.im ≠ 0 →
    ∀ᵐ x ∂P, (∫ γ, dh w x γ ∂Q) = κ * scalarDrift (X x) w
  cross_contraction : ∀ w u : ℂ, w.im ≠ 0 → u.im ≠ 0 →
    ∀ᵐ x ∂P, (∫ γ, h w x γ * ds u x γ ∂Q) =
      (2 * κ) * anchoredInteraction (X x) w u
  weighted_drift_integrable : ∀ n : ℕ, ∀ w : ℂ, w.im ≠ 0 →
    ∀ aux : Fin n → ℂ, (∀ j, (aux j).im ≠ 0) →
      Integrable (fun z : S × T => dh w z.1 z.2 * scalarProduct (X z.1) aux)
        (P.prod Q)
  weighted_cross_integrable : ∀ n : ℕ, ∀ w : ℂ, w.im ≠ 0 →
    ∀ aux : Fin n → ℂ, (∀ j, (aux j).im ≠ 0) → ∀ j : Fin n,
      Integrable (fun z : S × T =>
        (h w z.1 z.2 * ds (aux j) z.1 z.2) *
          scalarExcludedProduct (X z.1) aux j) (P.prod Q)
  stationary : ∀ n : ℕ, ∀ w : ℂ, w.im ≠ 0 →
    ∀ aux : Fin n → ℂ, (∀ j, (aux j).im ≠ 0) →
      (∫ z, responseObservable X h dh ds w aux z ∂P.prod Q) = 0

namespace ProductResponseIdentities

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
variable {P : Measure S} {Q : Measure T}
variable {X : S → AnchoredCountingState} {κ : ℂ}
variable {h dh ds : ℂ → S → T → ℂ}

/-- The expanded marked response is genuinely integrable. -/
theorem integrable_response
    (H : ProductResponseIdentities P Q X κ h dh ds)
    {n : ℕ} {w : ℂ} (hw : w.im ≠ 0)
    {aux : Fin n → ℂ} (ha : ∀ j, (aux j).im ≠ 0) :
    Integrable (responseObservable X h dh ds w aux) (P.prod Q) := by
  exact (H.weighted_drift_integrable n w hw aux ha).add
    (integrable_finset_sum _ (fun j _ => H.weighted_cross_integrable n w hw aux ha j))

/-- Fiber integration is the rigorous conditional-expectation contraction:
the stationary marked response contracts to `κ * loopIntegrand 1`. -/
theorem fiber_integral_response
    (H : ProductResponseIdentities P Q X κ h dh ds)
    {n : ℕ} {w : ℂ} (hw : w.im ≠ 0)
    {aux : Fin n → ℂ} (ha : ∀ j, (aux j).im ≠ 0) :
    ∀ᵐ x ∂P,
      (∫ γ, responseObservable X h dh ds w aux (x, γ) ∂Q) =
        κ * RationalBulk.loopIntegrand 1 (X x) w aux := by
  have hci : ∀ᵐ x ∂P, ∀ j : Fin n,
      Integrable (fun γ => h w x γ * ds (aux j) x γ) Q :=
    ae_all_iff.mpr (fun j => H.cross_integrable w (aux j) hw (ha j))
  have hcc : ∀ᵐ x ∂P, ∀ j : Fin n,
      (∫ γ, h w x γ * ds (aux j) x γ ∂Q) =
        (2 * κ) * anchoredInteraction (X x) w (aux j) :=
    ae_all_iff.mpr (fun j => H.cross_contraction w (aux j) hw (ha j))
  filter_upwards [H.drift_integrable w hw, H.drift_contraction w hw, hci, hcc]
    with x hdi hdc hci hcc
  have h0 : Integrable (fun γ => dh w x γ * scalarProduct (X x) aux) Q :=
    hdi.mul_const _
  have hj (j : Fin n) : Integrable
      (fun γ => (h w x γ * ds (aux j) x γ) * scalarExcludedProduct (X x) aux j) Q :=
    (hci j).mul_const _
  rw [show (fun γ => responseObservable X h dh ds w aux (x, γ)) =
      (fun γ => dh w x γ * scalarProduct (X x) aux +
        ∑ j, (h w x γ * ds (aux j) x γ) * scalarExcludedProduct (X x) aux j) from rfl]
  rw [integral_add h0 (integrable_finset_sum _ (fun j _ => hj j)),
    integral_finset_sum _ (fun j _ => hj j), integral_mul_const, hdc]
  simp_rw [integral_mul_const, hcc]
  rw [loopIntegrand_one]
  simp only [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

/-- Integrability of the stationary response transfers to the scalar loop
polynomial. Thus the equation below is not an identity of undefined integrals. -/
theorem integrable_loop
    [SFinite Q] (H : ProductResponseIdentities P Q X κ h dh ds) (hκ : κ ≠ 0)
    {n : ℕ} {w : ℂ} (hw : w.im ≠ 0)
    {aux : Fin n → ℂ} (ha : ∀ j, (aux j).im ≠ 0) :
    Integrable (fun x => RationalBulk.loopIntegrand 1 (X x) w aux) P := by
  have hi := (H.integrable_response hw ha).integral_prod_left
  have hm : Integrable (fun x => κ * RationalBulk.loopIntegrand 1 (X x) w aux) P :=
    hi.congr (H.fiber_integral_response hw ha)
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hκ) _).mp hm

/-- Stationarity and the two Gaussian contractions imply every literal loop
identity, including mixed half-planes, repeated arguments, and `n = 0`. -/
theorem integral_loop_eq_zero
    [SFinite P] [SFinite Q] (H : ProductResponseIdentities P Q X κ h dh ds) (hκ : κ ≠ 0)
    {n : ℕ} {w : ℂ} (hw : w.im ≠ 0)
    {aux : Fin n → ℂ} (ha : ∀ j, (aux j).im ≠ 0) :
    (∫ x, RationalBulk.loopIntegrand 1 (X x) w aux ∂P) = 0 := by
  have heq : (∫ z, responseObservable X h dh ds w aux z ∂P.prod Q) =
      κ * ∫ x, RationalBulk.loopIntegrand 1 (X x) w aux ∂P := by
    rw [integral_prod _ (H.integrable_response hw ha)]
    rw [integral_congr_ae (H.fiber_integral_response hw ha), integral_const_mul]
  have hz : κ * (∫ x, RationalBulk.loopIntegrand 1 (X x) w aux ∂P) = 0 := by
    rw [← heq]
    exact H.stationary n w hw aux ha
  exact (mul_eq_zero.mp hz).resolve_left hκ

/-- Construct the existing repository's exact hierarchy structure from the
new marked-response identities. The hierarchy itself is a conclusion. -/
theorem bulkLoopEquations
    [SFinite P] [SFinite Q] (H : ProductResponseIdentities P Q X κ h dh ds) (hκ : κ ≠ 0)
    (hX : Measurable X)
    (hm : ∀ q : ℕ, Integrable (fun x => ‖(X x).val.2‖ ^ q) P) :
    RationalBulk.BulkLoopEquations P 1 X := by
  refine ⟨hX, hm, ?_⟩
  intro n w hw aux ha
  exact H.integral_loop_eq_zero hκ hw ha

/-- The proved loop closure feeds directly into the imported rational bulk
characterization, giving equality with its actual Sine-one counting law. -/
theorem countingLaw_eq_sineOne
    [IsProbabilityMeasure P] [SFinite Q]
    (H : ProductResponseIdentities P Q X κ h dh ds) (hκ : κ ≠ 0)
    (hX : Measurable X)
    (hm : ∀ q : ℕ, Integrable (fun x => ‖(X x).val.2‖ ^ q) P) :
    Measure.map (fun x => (X x).val.1) P =
      (RationalBulk.sineBetaLaw (1 : ℚ) (by norm_num) : Measure LocalCountingMeasure) := by
  exact RationalBulk.bourgade_huang_theorem_1_5 (1 : ℚ) (by norm_num) P X
    (by simpa using H.bulkLoopEquations hκ hX hm)

end ProductResponseIdentities
end GeneralizedBulk.Loop
