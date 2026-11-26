import GeneralizedBulk.Gaussian.GlobalAnchorRotation
import GeneralizedBulk.Gaussian.GlobalField
import GeneralizedBulk.Gaussian.SeriesRotationCommon

/-!
# Actual ordinary-rotation equivariance of the global analytic field

A single probability-one event supports the conjugation identity for every
spectral value and derivative slot. The proof combines the genuine joint L²
anchor with the absolutely convergent raw-mark correction.
-/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators

namespace GeneralizedBulk.Gaussian

theorem rawMarkMatrix_matrixAction (p : ℝ) (O : Matrix (Fin 4) (Fin 4) ℝ)
    (hO : O * covarianceMatrix p * O.transpose = covarianceMatrix p)
    (y : Fin 4 → ℝ) :
    rawMarkMatrix p (O.mulVec y) =
      (O.map Complex.ofReal) * rawMarkMatrix p y * (O.map Complex.ofReal).transpose := by
  ext i j
  rw [matrix_conjugation_entry]
  simp only [rawMarkMatrix, Matrix.map_apply]
  exact_mod_cast rawQuadratic_matrixAction p O hO y i j

variable {I S : Type*} [Countable I] [MeasurableSpace S]
variable (P : Measure S) [IsProbabilityMeasure P]
variable (X : S → PresentedState I) (hX : Measurable X)
variable (hm : Integrable (fun x => ‖(X x).scalar.val.2‖) P)

theorem actual_globalCenteredField_equivariant_ae (parameters : Parameters)
    (O : Matrix (Fin 4) (Fin 4) ℝ)
    (hO : O * covarianceMatrix parameters.p * O.transpose = covarianceMatrix parameters.p) :
    ∀ᵐ z ∂P.prod (iidLaw (markLaw parameters.p) I), ∀ v : ℂ × Bool,
      globalCenteredField X parameters.p parameters.scale
          (presentedGlobalAnchorMatrix P X hX hm parameters) v (jointMarkAction O z) =
        (O.map Complex.ofReal) *
          globalCenteredField X parameters.p parameters.scale
            (presentedGlobalAnchorMatrix P X hX hm parameters) v z *
          (O.map Complex.ofReal).transpose := by
  let T := jointMarkAction (I := I) (S := S) O
  let anchor := presentedGlobalAnchorMatrix P X hX hm parameters
  let OC := O.map Complex.ofReal
  have hT := jointMarkAction_measurePreserving (I := I) P parameters.p parameters.abs_p_lt_one O hO
  have hrotated := hT.quasiMeasurePreserving.ae (ae_weightedEvent P X hX parameters.p)
  filter_upwards [ae_weightedEvent P X hX parameters.p, hrotated,
    presentedGlobalAnchor_equivariant_ae P X hX hm parameters O hO] with z hz hTz hA
  intro v
  have ha : anchor (T z) = OC * anchor z * OC.transpose := by
    ext i j
    rw [matrix_conjugation_entry]
    exact hA i j
  have hraw (n : I) : rawMarkMatrix parameters.p ((T z).2 n) =
      OC * rawMarkMatrix parameters.p (z.2 n) * OC.transpose :=
    rawMarkMatrix_matrixAction parameters.p O hO (z.2 n)
  rw [globalCenteredField_eq_presented X parameters.p parameters.scale anchor (T z) hTz v,
    globalCenteredField_eq_presented X parameters.p parameters.scale anchor z hz v]
  exact presented_matrixField_conjugate (X z.1).presentation OC (anchor z) (anchor (T z))
    parameters.scale (fun n => rawMarkMatrix parameters.p (z.2 n))
    (fun n => rawMarkMatrix parameters.p ((T z).2 n)) ha hraw
    (fun a b => weightedEvent_entry_summable hz a b) v

end GeneralizedBulk.Gaussian
