import GeneralizedBulk.Gaussian.GlobalField
import GeneralizedBulk.Gaussian.GlobalAnchorRotation
import GeneralizedBulk.Gaussian.SeriesPresentedBounds

/-!
# The actual Gaussian analytic field over random particle configurations

All series, representatives, and conditional Wick identities are constructed.
The only scalar moment used for this construction is the first anchor moment.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped BigOperators Topology

namespace GeneralizedBulk.Gaussian
variable {I S : Type*} [Countable I] [MeasurableSpace S]
variable (P : Measure S) [IsProbabilityMeasure P]
variable (X : S → PresentedState I) (hX : Measurable X)
variable (hm : Integrable (fun x => ‖(X x).scalar.val.2‖) P)

def constructedField (parameters : Parameters) (v : ℂ × Bool)
    (z : S × (I → (Fin 4 → ℝ))) : EndpointMatrix :=
  globalCenteredField X parameters.p parameters.scale
    (presentedGlobalAnchorMatrix P X hX hm parameters) v z

def constructedZ (parameters : Parameters) (x : S) (v : ℂ × Bool)
    (γ : I → (Fin 4 → ℝ)) : EndpointMatrix :=
  constructedField P X hX hm parameters v (x, γ)

theorem measurable_constructedField (parameters : Parameters) (v : ℂ × Bool) :
    Measurable (constructedField P X hX hm parameters v) :=
  measurable_globalCenteredField X hX parameters.p parameters.scale _
    (measurable_presentedGlobalAnchorMatrix P X hX hm parameters) v

/-- A single conditional event identifies all sixteen anchor entries. -/
theorem constructedAnchor_conditional_agreement (parameters : Parameters) :
    ∀ᵐ x ∂P, ∀ i j : Fin 4,
      (fun γ => presentedGlobalAnchorMatrix P X hX hm parameters (x, γ) i j)
        =ᵐ[iidLaw (markLaw parameters.p) I]
      (fun γ => presentedGaussianL2 parameters (X x).presentation
        (Complex.I, false) γ i j) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  simpa only [presentedGlobalAnchorMatrix, presentedGaussianL2, matrixL2Series,
    presentedAnchorCoefficient] using
    presentedGlobalAnchor_conditional_agreement P X hX hm parameters i j

/-- This equality holds for every spectral slot on one conditional event. -/
theorem constructedZ_eq_presented_ae (parameters : Parameters) :
    ∀ᵐ x ∂P, ∀ᵐ γ ∂iidLaw (markLaw parameters.p) I, ∀ v : ℂ × Bool,
      constructedZ P X hX hm parameters x v γ =
        presentedGaussianField parameters (X x).presentation
          (fun η => presentedGlobalAnchorMatrix P X hX hm parameters (x, η)) v γ := by
  have hg := Measure.ae_ae_of_ae_prod (ae_weightedEvent P X hX parameters.p)
  filter_upwards [hg] with x hx
  filter_upwards [hx] with γ hγ
  intro v
  exact globalCenteredField_eq_presented X parameters.p parameters.scale
    (presentedGlobalAnchorMatrix P X hX hm parameters) (x, γ) hγ v

/-- The infinite-series covariance is a theorem of the actual joint model,
including repeated particles and the spectral derivative slots. -/
theorem constructedZ_entryWick (parameters : Parameters) :
    ∀ᵐ x ∂P, EntryWickCovariance (iidLaw (markLaw parameters.p) I)
      (parameters.p : ℂ) (parameters.scale : ℂ) (particleKernel (X x).scalar)
      (constructedZ P X hX hm parameters x) := by
  filter_upwards [constructedAnchor_conditional_agreement P X hX hm parameters,
    constructedZ_eq_presented_ae P X hX hm parameters] with x ha heq
  apply (presentedGaussianField_entryWick parameters (X x).presentation
    (fun γ => presentedGlobalAnchorMatrix P X hX hm parameters (x, γ)) ha).congr_ae
  intro v i j
  exact heq.mono (fun γ h => congrFun (congrFun (h v).symm i) j)

/-- No Wick or convergence premise remains in this constructor. The vanishing
linear coefficient is the scalar-state hypothesis of the switching criterion. -/
theorem constructedZ_wickFiberData (parameters : Parameters)
    (hlinear : ∀ᵐ x ∂P, anchoredLinearCoefficient (X x).scalar = 0) :
    Marked.WickFiberData P (iidLaw (markLaw parameters.p) I) parameters
      (fun x => (X x).scalar) (fun x => particleKernel (X x).scalar)
      (constructedZ P X hX hm parameters) := by
  refine ⟨constructedZ_entryWick P X hX hm parameters, ?_, ?_⟩
  · intro w hw
    filter_upwards [hlinear] with x hx
    exact particleKernel_diagonal (X x).scalar hx hw
  · intro w u hw hu
    exact Eventually.of_forall (fun x => particleKernel_interaction (X x).scalar hw hu)

/-- The value and derivative fields are actual derivatives on a single
probability-one event, simultaneously at every nonreal parameter. -/
theorem constructedField_hasDerivAt_ae (parameters : Parameters) :
    ∀ᵐ z ∂P.prod (iidLaw (markLaw parameters.p) I), ∀ i j : Fin 4,
      ∀ w : ℂ, w.im ≠ 0 →
      HasDerivAt (fun u => constructedField P X hX hm parameters (u, false) z i j)
        (constructedField P X hX hm parameters (w, true) z i j) w :=
  globalCenteredField_hasDerivAt_ae P X hX parameters.p parameters.scale _

/-- Conditional L² integrability is proved rather than supplied to the loop
calculation. -/
theorem constructedZ_memLp_two (parameters : Parameters) (v : ℂ × Bool) (i j : Fin 4) :
    ∀ᵐ x ∂P, MemLp (fun γ => constructedZ P X hX hm parameters x v γ i j) 2
      (iidLaw (markLaw parameters.p) I) := by
  filter_upwards [constructedAnchor_conditional_agreement P X hX hm parameters,
    constructedZ_eq_presented_ae P X hX hm parameters] with x ha heq
  apply (memLp_congr_ae (heq.mono (fun γ h => congrFun (congrFun (h v) i) j))).2
  exact presentedGaussianField_memLp_two parameters (X x).presentation _ ha v i j

theorem constructedZ_second_moment (parameters : Parameters) (v : ℂ × Bool) (i j : Fin 4) :
    ∀ᵐ x ∂P,
      (∫ γ, ‖constructedZ P X hX hm parameters x v γ i j‖ ^ 2
        ∂iidLaw (markLaw parameters.p) I) ≤
      (2 * ‖(parameters.scale : ℂ)‖ ^ 2 * coefficientSquareEnvelope v) *
        (1 + ‖(X x).scalar.val.2‖ ^ 2) := by
  filter_upwards [constructedAnchor_conditional_agreement P X hX hm parameters,
    constructedZ_eq_presented_ae P X hX hm parameters] with x ha heq
  rw [integral_congr_ae (heq.mono (fun γ h =>
    congrArg (fun A : EndpointMatrix => ‖A i j‖ ^ 2) (h v)))]
  exact presentedGaussianField_second_moment_quadratic parameters (X x).presentation _ ha v i j

theorem constructedMarkedMatrix_memLp_two (parameters : Parameters) (w : ℂ) (i j : Fin 4) :
    ∀ᵐ x ∂P, MemLp (fun γ => Marked.markedMatrix parameters
      (fun x => (X x).scalar) (constructedZ P X hX hm parameters) w x γ i j) 2
      (iidLaw (markLaw parameters.p) I) := by
  filter_upwards [constructedZ_memLp_two P X hX hm parameters (w, false) i j] with x hx
  exact (memLp_const _).add hx

theorem constructedMarkedMatrix_second_moment (parameters : Parameters)
    {w : ℂ} (hw : w.im ≠ 0) (i j : Fin 4) :
    ∀ᵐ x ∂P,
      (∫ γ, ‖Marked.markedMatrix parameters (fun x => (X x).scalar)
        (constructedZ P X hX hm parameters) w x γ i j‖ ^ 2
        ∂iidLaw (markLaw parameters.p) I) ≤
      (4 * meanEntryEnvelope parameters w ^ 2 +
        4 * ‖(parameters.scale : ℂ)‖ ^ 2 * coefficientSquareEnvelope (w, false)) *
          (1 + ‖(X x).scalar.val.2‖ ^ 2) := by
  filter_upwards [constructedAnchor_conditional_agreement P X hX hm parameters,
    constructedZ_eq_presented_ae P X hX hm parameters] with x ha heq
  have hmEq : Marked.mean parameters (fun x => (X x).scalar) w x =
      Marked.mean parameters (fun _ : Unit => (X x).scalar) w () := rfl
  have hEq : (fun γ => ‖Marked.markedMatrix parameters (fun x => (X x).scalar)
      (constructedZ P X hX hm parameters) w x γ i j‖ ^ 2)
      =ᵐ[iidLaw (markLaw parameters.p) I]
      (fun γ => ‖Marked.mean parameters (fun _ : Unit => (X x).scalar) w () i j +
        presentedGaussianField parameters (X x).presentation
          (fun η => presentedGlobalAnchorMatrix P X hX hm parameters (x, η))
          (w, false) γ i j‖ ^ 2) := by
    filter_upwards [heq] with γ hγ
    simp only [Marked.markedMatrix, Matrix.add_apply, hmEq, hγ (w, false)]
  rw [integral_congr_ae hEq]
  exact presentedGaussianField_full_second_moment parameters (X x).presentation _ ha hw i j

end GeneralizedBulk.Gaussian
