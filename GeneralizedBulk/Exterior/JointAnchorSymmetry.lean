import GeneralizedBulk.Gaussian.GlobalAnchorRotation

/-! The actual jointly measurable Gaussian anchor is a symmetric matrix. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped BigOperators
namespace GeneralizedBulk.Gaussian

/-- Real endpoint covariance is symmetric, so every centered quadratic mark
is a symmetric matrix before any passage to an infinite sum. -/
theorem rawQuadratic_symmetric (p : ℝ) (y : Fin 4 → ℝ) (i j : Fin 4) :
    rawQuadratic p j i y = rawQuadratic p i j y := by
  have hc : covarianceMatrix p j i = covarianceMatrix p i j := by
    rw [covarianceMatrix_eq]
    fin_cases i <;> fin_cases j <;> rfl
  simp only [rawQuadratic, hc, mul_comm]

theorem markQuadraticFamily_symmetric (p : ℝ) {I : Type*} (n : I)
    (ω : I → (Fin 4 → ℝ)) (i j : Fin 4) :
    markQuadraticFamily p n j i ω = markQuadraticFamily p n i j ω :=
  rawQuadratic_symmetric p (ω n) i j

variable {I S : Type*} [MeasurableSpace S]
    (P : Measure S) [IsProbabilityMeasure P]
    (p : ℝ) (A : I → S → ℂ) (hA : ∀ n, Measurable (A n))
    (hA2 : ∀ n, Integrable (fun x => ‖A n x‖ ^ 2) P)

theorem jointTerm_symmetric (n : I) (i j : Fin 4) :
    jointTerm P p A hA hA2 n j i = jointTerm P p A hA hA2 n i j := by
  apply Lp.ext
  filter_upwards [jointTerm_ae P p A hA hA2 n j i, jointTerm_ae P p A hA hA2 n i j]
    with z hji hij
  simp only [hji, hij, jointTermFunction, markQuadraticFamily_symmetric p n z.2 i j]

/-- Equality is first proved in the actual complete Hilbert space, hence is
valid for the chosen measurable representatives as well. -/
theorem globalAnchorLp_symmetric (i j : Fin 4) :
    globalAnchorLp P p A hA hA2 j i = globalAnchorLp P p A hA hA2 i j := by
  unfold globalAnchorLp
  apply tsum_congr
  intro n
  exact jointTerm_symmetric P p A hA hA2 n i j

variable [Countable I] (X : S → PresentedState I) (hX : Measurable X)
    (hm : Integrable (fun x => ‖(X x).scalar.val.2‖) P)

/-- The literal representative chosen for the joint anchor is symmetric at
every sample; no uncountable intersection of almost-everywhere events occurs. -/
theorem presentedGlobalAnchorMatrix_transpose (parameters : Parameters)
    (z : S × (I → (Fin 4 → ℝ))) :
    (presentedGlobalAnchorMatrix P X hX hm parameters z).transpose =
      presentedGlobalAnchorMatrix P X hX hm parameters z := by
  ext i j
  change presentedGlobalAnchor P X hX hm parameters j i z =
    presentedGlobalAnchor P X hX hm parameters i j z
  change globalAnchorLp P parameters.p (presentedAnchorCoefficient X parameters.scale)
    (measurable_presentedAnchorCoefficient X hX parameters.scale)
    (integrable_presentedAnchorCoefficient_sq P X hX hm parameters.scale) j i z = _
  rw [globalAnchorLp_symmetric]
  rfl

theorem presentedGlobalAnchorMatrix_transpose_ae (parameters : Parameters) :
    ∀ᵐ z ∂P.prod (iidLaw (markLaw parameters.p) I),
      (presentedGlobalAnchorMatrix P X hX hm parameters z).transpose =
        presentedGlobalAnchorMatrix P X hX hm parameters z :=
  Eventually.of_forall (presentedGlobalAnchorMatrix_transpose P X hX hm parameters)

end GeneralizedBulk.Gaussian
