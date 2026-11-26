import GeneralizedBulk.Gaussian.Characteristic

/-! # Measure-preserving covariance symmetries of the full iid mark family -/
noncomputable section
open MeasureTheory

namespace GeneralizedBulk.Gaussian

theorem markFamily_matrixAction_invariant (p : ℝ) (hp : |p| < 1)
    (O : Matrix (Fin 4) (Fin 4) ℝ)
    (hO : O * covarianceMatrix p * O.transpose = covarianceMatrix p) (I : Type*) :
    Measure.map (coordinateAction (fun x : Fin 4 → ℝ => O.mulVec x) (I := I))
      (iidLaw (markLaw p) I) = iidLaw (markLaw p) I :=
  iidLaw_coordinateAction_invariant (markLaw p) I _ (measurable_matrixAction O)
    (markLaw_matrixAction_invariant p hp O hO)

theorem markFamily_matrixAction_measurePreserving (p : ℝ) (hp : |p| < 1)
    (O : Matrix (Fin 4) (Fin 4) ℝ)
    (hO : O * covarianceMatrix p * O.transpose = covarianceMatrix p) (I : Type*) :
    MeasurePreserving (coordinateAction (fun x : Fin 4 → ℝ => O.mulVec x) (I := I))
      (iidLaw (markLaw p) I) (iidLaw (markLaw p) I) :=
  ⟨measurable_coordinateAction (measurable_matrixAction O) I,
    markFamily_matrixAction_invariant p hp O hO I⟩

end GeneralizedBulk.Gaussian
