import GeneralizedBulk.Gaussian.GlobalAnchor
import GeneralizedBulk.Gaussian.SeriesRotation
import GeneralizedBulk.Exterior.Rotation

/-!
# Covariance-preserving action on the jointly measurable anchor

The scalar state stays fixed while every actual independent Gaussian mark is
rotated. The genuine joint Hilbert sum conjugates under this measure-preserving
action; no separate covariance or stationarity assumption is introduced.
-/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators

namespace GeneralizedBulk.Gaussian

variable {I S : Type*} [MeasurableSpace S]

def jointMarkAction (O : Matrix (Fin 4) (Fin 4) ℝ) :
    S × (I → (Fin 4 → ℝ)) → S × (I → (Fin 4 → ℝ)) :=
  Prod.map id (coordinateAction (fun y : Fin 4 → ℝ => O.mulVec y))

theorem jointMarkAction_measurePreserving (P : Measure S) [IsProbabilityMeasure P]
    (p : ℝ) (hp : |p| < 1) (O : Matrix (Fin 4) (Fin 4) ℝ)
    (hO : O * covarianceMatrix p * O.transpose = covarianceMatrix p) :
    MeasurePreserving (jointMarkAction (I := I) (S := S) O)
      (P.prod (iidLaw (markLaw p) I)) (P.prod (iidLaw (markLaw p) I)) :=
  (MeasurePreserving.id P).prod (markFamily_matrixAction_measurePreserving p hp O hO I)

section Generic
variable (P : Measure S) [IsProbabilityMeasure P]
variable (p : ℝ) (hp : |p| < 1)
variable (A : I → S → ℂ) (hA : ∀ n, Measurable (A n))
variable (hA2 : ∀ n, Integrable (fun x => ‖A n x‖ ^ 2) P)
variable (O : Matrix (Fin 4) (Fin 4) ℝ)
variable (hO : O * covarianceMatrix p * O.transpose = covarianceMatrix p)

theorem jointTerm_equivariant (n : I) (i j : Fin 4) :
    pullbackL2 (P.prod (iidLaw (markLaw p) I)) (jointMarkAction O)
      (jointMarkAction_measurePreserving P p hp O hO) (jointTerm P p A hA hA2 n i j) =
    conjugateL2 (P.prod (iidLaw (markLaw p) I)) (O.map Complex.ofReal)
      (fun a b => jointTerm P p A hA hA2 n a b) i j := by
  let μ := P.prod (iidLaw (markLaw p) I)
  let T := jointMarkAction (I := I) (S := S) O
  have hT := jointMarkAction_measurePreserving (I := I) P p hp O hO
  have ht := hT.quasiMeasurePreserving.ae_eq_comp (jointTerm_ae P p A hA hA2 n i j)
  have hr : ∀ᵐ z ∂μ, ∀ a b : Fin 4,
      jointTerm P p A hA hA2 n a b z = jointTermFunction p A n a b z :=
    ae_all_iff.mpr (fun a => ae_all_iff.mpr (fun b => jointTerm_ae P p A hA hA2 n a b))
  apply Lp.ext
  filter_upwards [pullbackL2_ae μ T hT (jointTerm P p A hA hA2 n i j), ht,
    conjugateL2_ae μ (O.map Complex.ofReal) (fun a b => jointTerm P p A hA hA2 n a b) i j,
    hr] with z hpull hraw hconj hr
  rw [hpull, hconj]
  change jointTerm P p A hA hA2 n i j (T z) = _ at hraw
  rw [hraw]
  simp only [Matrix.map_apply, hr, jointTermFunction]
  change A n z.1 * (rawQuadratic p i j (O.mulVec (z.2 n)) : ℂ) =
    ∑ a : Fin 4, ∑ b : Fin 4, (O i a : ℂ) * (O j b : ℂ) *
      (A n z.1 * (rawQuadratic p a b (z.2 n) : ℂ))
  rw [rawQuadratic_matrixAction p O hO]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

variable (hsq : Summable (fun n => ∫ x, ‖A n x‖ ^ 2 ∂P))

include hsq in
theorem globalAnchorLp_equivariant (i j : Fin 4) :
    pullbackL2 (P.prod (iidLaw (markLaw p) I)) (jointMarkAction O)
      (jointMarkAction_measurePreserving P p hp O hO) (globalAnchorLp P p A hA hA2 i j) =
    conjugateL2 (P.prod (iidLaw (markLaw p) I)) (O.map Complex.ofReal)
      (fun a b => globalAnchorLp P p A hA hA2 a b) i j := by
  have hs (a b : Fin 4) :
      Summable (fun n => (1 : ℂ) • jointTerm P p A hA hA2 n a b) := by
    simpa only [one_smul] using summable_jointTerm P p hp A hA hA2 hsq a b
  simpa only [l2Series, one_smul, globalAnchorLp] using
    l2Series_equivariant (P.prod (iidLaw (markLaw p) I)) (jointMarkAction O)
      (jointMarkAction_measurePreserving P p hp O hO) (O.map Complex.ofReal)
      (fun n a b => jointTerm P p A hA hA2 n a b) (fun _ => 1) hs
      (fun n a b => jointTerm_equivariant P p hp A hA hA2 O hO n a b) i j

end Generic

section Presented
variable [Countable I] (P : Measure S) [IsProbabilityMeasure P]
variable (X : S → PresentedState I) (hX : Measurable X)
variable (hm : Integrable (fun x => ‖(X x).scalar.val.2‖) P)

def presentedGlobalAnchorMatrix (parameters : Parameters)
    (z : S × (I → (Fin 4 → ℝ))) : EndpointMatrix :=
  fun i j => presentedGlobalAnchor P X hX hm parameters i j z

theorem measurable_presentedGlobalAnchorMatrix (parameters : Parameters) :
    Measurable (presentedGlobalAnchorMatrix P X hX hm parameters) := by
  change @Measurable _ (Fin 4 → Fin 4 → ℂ) _ (borel _) _
  rw [← @BorelSpace.measurable_eq (Fin 4 → Fin 4 → ℂ) _ MeasurableSpace.pi (by infer_instance)]
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact presentedGlobalAnchor_measurable P X hX hm parameters i j

theorem presentedGlobalAnchor_equivariant (parameters : Parameters)
    (O : Matrix (Fin 4) (Fin 4) ℝ)
    (hO : O * covarianceMatrix parameters.p * O.transpose = covarianceMatrix parameters.p)
    (i j : Fin 4) :
    pullbackL2 (P.prod (iidLaw (markLaw parameters.p) I)) (jointMarkAction O)
      (jointMarkAction_measurePreserving P parameters.p parameters.abs_p_lt_one O hO)
      (presentedGlobalAnchor P X hX hm parameters i j) =
    conjugateL2 (P.prod (iidLaw (markLaw parameters.p) I)) (O.map Complex.ofReal)
      (fun a b => presentedGlobalAnchor P X hX hm parameters a b) i j := by
  exact globalAnchorLp_equivariant P parameters.p parameters.abs_p_lt_one
    (presentedAnchorCoefficient X parameters.scale)
    (measurable_presentedAnchorCoefficient X hX parameters.scale)
    (integrable_presentedAnchorCoefficient_sq P X hX hm parameters.scale) O hO
    (summable_presentedAnchorCoefficient_integrals P X hX hm parameters.scale) i j

/-- The jointly measurable representative satisfies actual conjugation almost
surely under the genuine Gaussian action. -/
theorem presentedGlobalAnchor_equivariant_ae (parameters : Parameters)
    (O : Matrix (Fin 4) (Fin 4) ℝ)
    (hO : O * covarianceMatrix parameters.p * O.transpose = covarianceMatrix parameters.p) :
    ∀ᵐ z ∂P.prod (iidLaw (markLaw parameters.p) I), ∀ i j : Fin 4,
      presentedGlobalAnchor P X hX hm parameters i j (jointMarkAction O z) =
        ∑ a : Fin 4, ∑ b : Fin 4, (O i a : ℂ) * (O j b : ℂ) *
          presentedGlobalAnchor P X hX hm parameters a b z := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  let μ := P.prod (iidLaw (markLaw parameters.p) I)
  let T := jointMarkAction (I := I) (S := S) O
  have hT := jointMarkAction_measurePreserving (I := I) P parameters.p parameters.abs_p_lt_one O hO
  have hpull := pullbackL2_ae μ T hT (presentedGlobalAnchor P X hX hm parameters i j)
  have hconj := conjugateL2_ae μ (O.map Complex.ofReal)
    (fun a b => presentedGlobalAnchor P X hX hm parameters a b) i j
  rw [presentedGlobalAnchor_equivariant P X hX hm parameters O hO i j] at hpull
  filter_upwards [hpull, hconj] with z hp hc
  simpa only [Matrix.map_apply] using hp.symm.trans hc

end Presented

end GeneralizedBulk.Gaussian
