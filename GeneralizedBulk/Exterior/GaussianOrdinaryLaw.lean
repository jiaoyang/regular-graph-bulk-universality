import GeneralizedBulk.Gaussian.GlobalConstruction
import GeneralizedBulk.Gaussian.GlobalFieldRotation
import GeneralizedBulk.Exterior.Equivariance
import GeneralizedBulk.Exterior.RealRotation

/-!
# The ordinary exterior law of the actual Gaussian marked field

The raw matrix and its spectral derivative include their deterministic means.
The full exterior jet law is invariant under ordinary rotation because the
actual infinite Gaussian marks admit a measure-preserving action.
-/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators

namespace GeneralizedBulk.Exterior

abbrev NonrealSpectral := {w : ℂ // w.im ≠ 0}

variable {I S : Type*} [Countable I] [MeasurableSpace S]
variable (P : Measure S) [IsProbabilityMeasure P]
variable (X : S → Gaussian.PresentedState I) (hX : Measurable X)
variable (hm : Integrable (fun x => ‖(X x).scalar.val.2‖) P)

def constructedScalar (z : S × (I → (Fin 4 → ℝ))) (w : NonrealSpectral) : ℂ :=
  anchoredNevanlinna (X z.1).scalar w.1

def constructedMatrix (parameters : Parameters) (z : S × (I → (Fin 4 → ℝ)))
    (w : NonrealSpectral) : Mat :=
  Marked.mean parameters (fun x => (X x).scalar) w.1 z.1 +
    Gaussian.constructedField P X hX hm parameters (w.1, false) z

def constructedDerivative (parameters : Parameters) (z : S × (I → (Fin 4 → ℝ)))
    (w : NonrealSpectral) : Mat :=
  ((parameters.scale : ℂ) * anchoredDerivative (X z.1).scalar w.1) •
      covarianceMatrix (parameters.p : ℂ) +
    Gaussian.constructedField P X hX hm parameters (w.1, true) z

theorem mean_eq_covariance (parameters : Parameters) (Y : S → AnchoredCountingState)
    (w : ℂ) (x : S) :
    Marked.mean parameters Y w x =
      ((parameters.center : ℂ) + (parameters.scale : ℂ) * anchoredNevanlinna (Y x) w) •
        covarianceMatrix (parameters.p : ℂ) + (parameters.r : ℂ) • GeneralizedSwitching.edgeMatrix := by
  exact (meanMatrix_from_covariance _ _ _).symm

include hX in
theorem measurable_constructedScalar (w : NonrealSpectral) :
    Measurable (fun z : S × (I → (Fin 4 → ℝ)) => constructedScalar X z w) :=
  ((continuous_anchoredNevanlinna w.2).measurable.comp
    (Gaussian.PresentedState.measurable_scalar.comp hX)).comp measurable_fst

theorem measurable_constructedMatrix (parameters : Parameters) (w : NonrealSpectral) :
    Measurable (fun z => constructedMatrix P X hX hm parameters z w) := by
  have hs := measurable_constructedScalar X hX w
  have hmean : Measurable (fun z : S × (I → (Fin 4 → ℝ)) =>
      Marked.mean parameters (fun x => (X x).scalar) w.1 z.1) := by
    simp_rw [mean_eq_covariance]
    exact ((measurable_const.add (hs.const_mul (parameters.scale : ℂ))).smul measurable_const).add
      measurable_const
  exact hmean.add (Gaussian.measurable_constructedField P X hX hm parameters (w.1, false))

theorem measurable_constructedDerivative (parameters : Parameters) (w : NonrealSpectral) :
    Measurable (fun z => constructedDerivative P X hX hm parameters z w) := by
  have hd : Measurable (fun z : S × (I → (Fin 4 → ℝ)) => anchoredDerivative (X z.1).scalar w.1) :=
    ((continuous_anchoredDerivative w.2).measurable.comp
      (Gaussian.PresentedState.measurable_scalar.comp hX)).comp measurable_fst
  exact ((hd.const_mul (parameters.scale : ℂ)).smul measurable_const).add
    (Gaussian.measurable_constructedField P X hX hm parameters (w.1, true))

theorem ordinaryRotation_mean (parameters : Parameters) (Y : S → AnchoredCountingState)
    (t : ℝ) (w : ℂ) (x : S) :
    ordinaryRotation t * Marked.mean parameters Y w x * (ordinaryRotation t).transpose =
      Marked.mean parameters Y w x := by
  have hJ : ordinaryRotation t * GeneralizedSwitching.edgeMatrix * (ordinaryRotation t).transpose =
      (GeneralizedSwitching.edgeMatrix : Mat) := by
    rw [ordinaryRotation_commutes_edge, Matrix.mul_assoc, ordinaryRotation_mul_transpose, mul_one]
  rw [mean_eq_covariance]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    ordinaryRotation_preserves_covariance, hJ]

theorem constructed_raw_equivariant_ae (parameters : Parameters) (t : ℝ) :
    ∀ᵐ z ∂P.prod (Gaussian.iidLaw (Gaussian.markLaw parameters.p) I),
      (∀ w : NonrealSpectral,
        constructedMatrix P X hX hm parameters (Gaussian.jointMarkAction (realOrdinaryRotation t) z) w =
          ordinaryRotation t * constructedMatrix P X hX hm parameters z w * (ordinaryRotation t).transpose) ∧
      (∀ w : NonrealSpectral,
        constructedDerivative P X hX hm parameters (Gaussian.jointMarkAction (realOrdinaryRotation t) z) w =
          ordinaryRotation t * constructedDerivative P X hX hm parameters z w * (ordinaryRotation t).transpose) := by
  have he := Gaussian.actual_globalCenteredField_equivariant_ae P X hX hm parameters
    (realOrdinaryRotation t) (realOrdinaryRotation_preserves_covariance t parameters.p)
  simp only [realOrdinaryRotation_complex] at he
  filter_upwards [he] with z hz
  constructor
  · intro w
    change Marked.mean parameters (fun x => (X x).scalar) w.1 z.1 + _ = _
    simp only [constructedMatrix, Matrix.mul_add, Matrix.add_mul, ordinaryRotation_mean]
    exact congrArg (fun M => Marked.mean parameters (fun x => (X x).scalar) w.1 z.1 + M)
      (hz (w.1, false))
  · intro w
    change ((parameters.scale : ℂ) * anchoredDerivative (X z.1).scalar w.1) • covarianceMatrix _ + _ = _
    simp only [constructedDerivative, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, ordinaryRotation_preserves_covariance]
    exact congrArg (fun M => ((parameters.scale : ℂ) * anchoredDerivative (X z.1).scalar w.1) •
      covarianceMatrix (parameters.p : ℂ) + M) (hz (w.1, true))

theorem constructedJet_ordinary_law (parameters : Parameters) (t : ℝ) :
    Measure.map (action (ordinaryRotation t))
      (Measure.map (fun z => jetOfRaw (constructedScalar X z)
        (constructedMatrix P X hX hm parameters z) (constructedDerivative P X hX hm parameters z))
        (P.prod (Gaussian.iidLaw (Gaussian.markLaw parameters.p) I))) =
    Measure.map (fun z => jetOfRaw (constructedScalar X z)
      (constructedMatrix P X hX hm parameters z) (constructedDerivative P X hX hm parameters z))
      (P.prod (Gaussian.iidLaw (Gaussian.markLaw parameters.p) I)) := by
  apply exterior_law_of_measurePreserving _ _
    (measurable_jetOfRaw _ _ _ (measurable_constructedScalar X hX)
      (measurable_constructedMatrix P X hX hm parameters)
      (measurable_constructedDerivative P X hX hm parameters))
    (Gaussian.jointMarkAction (realOrdinaryRotation t))
    (Gaussian.jointMarkAction_measurePreserving P parameters.p parameters.abs_p_lt_one
      (realOrdinaryRotation t) (realOrdinaryRotation_preserves_covariance t parameters.p))
  filter_upwards [constructed_raw_equivariant_ae P X hX hm parameters t] with z hz
  have hM := funext hz.1
  have hL := funext hz.2
  change jetOfRaw (constructedScalar X z) _ _ = _
  rw [hM, hL]
  exact jetOfRaw_conjugate _ _ _ (ordinaryRotation t)
    (ordinaryRotation_mul_transpose t) (ordinaryRotation_commutes_edge t)

/-- The full deterministic derivative has zero sign trace, so the marked
scalar response is exactly twice the sign trace of the full raw derivative. -/
theorem ds_eq_trace_constructedDerivative (parameters : Parameters)
    (z : S × (I → (Fin 4 → ℝ))) (w : NonrealSpectral) :
    Marked.ds (Gaussian.constructedZ P X hX hm parameters) w.1 z.1 z.2 =
      2 * Matrix.trace (signMatrix * constructedDerivative P X hX hm parameters z w) := by
  simp only [Marked.ds, constructedDerivative, Matrix.mul_add, Matrix.trace_add,
    Matrix.mul_smul, Matrix.trace_smul, trace_sign_covariance, smul_zero, zero_add,
    Gaussian.constructedZ]

end GeneralizedBulk.Exterior
