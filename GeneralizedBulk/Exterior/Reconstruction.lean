import GeneralizedBulk.Exterior.LawSymmetry

/-!
# Measurable reconstruction of the endpoint and scalar fields

The reconstruction uses the exterior value and its spectral derivative. This
makes scalar response accessible by ordinary one-parameter differentiation.
-/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.Exterior

/-- A scalar exterior field together with the value/derivative jet of K. -/
abbrev JetState (I : Type*) := (I → ℂ) × ((I × Bool) → Mat)

/-- Matrix inversion is Borel measurable everywhere, including its totalized
value on singular matrices. The positive-imaginary-part theorem separately
ensures actual inverses on the flow's support. -/
theorem measurable_matrix_inverse : Measurable (fun A : Mat => A⁻¹) := by
  have hdet : Measurable (fun A : Mat => A.det) := continuous_id.matrix_det.measurable
  have hadj : Measurable (fun A : Mat => A.adjugate) := continuous_id.matrix_adjugate.measurable
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv] using hdet.inv.smul hadj

def reconstructedMatrix {I : Type*} (state : JetState I) (w : I) : Mat :=
  ((GeneralizedSwitching.edgeMatrix : Mat) - state.2 (w, false))⁻¹

def reconstructedScalar {I : Type*} (state : JetState I) (w : I) : ℂ :=
  state.1 w + Matrix.trace (reconstructedMatrix state w * state.2 (w, true))

/-- The spectral derivative reconstructed by the inverse derivative formula. -/
def reconstructedDerivative {I : Type*} (state : JetState I) (w : I) : Mat :=
  reconstructedMatrix state w * state.2 (w, true) * reconstructedMatrix state w

def reconstruction {I : Type*} (state : JetState I) : (I → ℂ) × (I → Mat) :=
  (reconstructedScalar state, reconstructedMatrix state)

theorem measurable_reconstructedMatrix {I : Type*} (w : I) :
    Measurable (fun state : JetState I => reconstructedMatrix state w) := by
  exact measurable_matrix_inverse.comp
    (measurable_const.sub ((measurable_pi_apply (w, false)).comp measurable_snd))

theorem measurable_reconstructedScalar {I : Type*} (w : I) :
    Measurable (fun state : JetState I => reconstructedScalar state w) := by
  have htrace : Measurable (Matrix.trace : Mat → ℂ) := continuous_id.matrix_trace.measurable
  exact ((measurable_pi_apply w).comp measurable_fst).add
    (htrace.comp ((measurable_reconstructedMatrix w).mul
      ((measurable_pi_apply (w, true)).comp measurable_snd)))

theorem measurable_reconstructedDerivative {I : Type*} (w : I) :
    Measurable (fun state : JetState I => reconstructedDerivative state w) := by
  exact ((measurable_reconstructedMatrix w).mul
    ((measurable_pi_apply (w, true)).comp measurable_snd)).mul (measurable_reconstructedMatrix w)

theorem measurable_reconstruction {I : Type*} :
    Measurable (reconstruction (I := I)) := by
  exact (measurable_pi_lambda _ fun w => measurable_reconstructedScalar w).prodMk
    (measurable_pi_lambda _ fun w => measurable_reconstructedMatrix w)

/-- Joint scalar/matrix stationarity follows from the derived exterior symmetry.
No conditional stationarity on the scalar state is asserted. -/
theorem reconstructed_field_stationary
    {I : Type*} (μ : Measure (JetState I)) (t : ℝ)
    (hswitch : Measure.map (action GeneralizedSwitching.endpointPermutation) μ = μ)
    (hordinary : Measure.map (action (ordinaryRotation t)) μ = μ) :
    Measure.map (reconstruction ∘ action (rotation t)) μ = Measure.map reconstruction μ :=
  reconstructed_rotation_law μ t hswitch hordinary _ measurable_reconstruction

/-- Any measurable observable of exterior jets has the stationary distribution
needed by the expectation/FTC theorem. -/
theorem observable_identDistrib
    {I E : Type*} [MeasurableSpace E] (μ : Measure (JetState I)) (t : ℝ)
    (hswitch : Measure.map (action GeneralizedSwitching.endpointPermutation) μ = μ)
    (hordinary : Measure.map (action (ordinaryRotation t)) μ = μ)
    (F : JetState I → E) (hF : Measurable F) :
    ProbabilityTheory.IdentDistrib (F ∘ action (rotation t)) F μ μ := by
  constructor
  · exact (hF.comp (measurable_action _)).aemeasurable
  · exact hF.aemeasurable
  · exact reconstructed_rotation_law μ t hswitch hordinary F hF

/-- Stationarity can be pulled back to an original probability space without
requiring any measurability of an uncountable positivity event in jet space. -/
theorem observable_pullback_identDistrib
    {Ω I E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (jet : Ω → JetState I) (hjet : Measurable jet) (t : ℝ)
    (hswitch : Measure.map (action GeneralizedSwitching.endpointPermutation) (Measure.map jet P) =
      Measure.map jet P)
    (hordinary : Measure.map (action (ordinaryRotation t)) (Measure.map jet P) = Measure.map jet P)
    (F : JetState I → E) (hF : Measurable F) :
    ProbabilityTheory.IdentDistrib
      (fun ω => F (action (rotation t) (jet ω))) (fun ω => F (jet ω)) P P := by
  have hQ := measurable_action (A := I → ℂ) (I := I × Bool) (rotation (t : ℂ))
  constructor
  · exact ((hF.comp hQ).comp hjet).aemeasurable
  · exact (hF.comp hjet).aemeasurable
  · change Measure.map (F ∘ action (rotation t) ∘ jet) P = Measure.map (F ∘ jet) P
    rw [← Measure.map_map hF (hQ.comp hjet), ← Measure.map_map hQ hjet,
      rotation_invariance_of_switch_and_ordinary (Measure.map jet P) t hswitch hordinary,
      Measure.map_map hF hjet]

end GeneralizedBulk.Exterior
