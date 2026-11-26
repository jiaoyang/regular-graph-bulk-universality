import GeneralizedBulk.Exterior.Rotation

/-!
# Deriving the conjugated rotation symmetry of the exterior state

The exterior scalar coordinate is left fixed. The only distribution hypotheses
are the switch symmetry and the ordinary Gaussian-rotation symmetry. Their
composition proves the new rotation symmetry; stationarity is not assumed.
-/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.Exterior

/-- Simultaneous conjugation of every spectral value, preserving the full
exterior scalar coordinate. The index type may encode any collection of
spectral parameters. -/
def action {A I : Type*} (Q : Mat) (state : A × (I → Mat)) : A × (I → Mat) :=
  (state.1, fun w => Q * state.2 w * Q.transpose)

theorem action_mul {A I : Type*} (Q R : Mat) (state : A × (I → Mat)) :
    action Q (action R state) = action (Q * R) state := by
  apply Prod.ext
  · rfl
  · funext w
    simp only [action, Matrix.transpose_mul, Matrix.mul_assoc]

theorem measurable_action {A I : Type*} [MeasurableSpace A] (Q : Mat) :
    Measurable (action (A := A) (I := I) Q) := by
  refine measurable_fst.prodMk (measurable_pi_lambda _ fun w => ?_)
  have h : Measurable (fun state : A × (I → Mat) => state.2 w) :=
    (measurable_pi_apply w).comp measurable_snd
  exact (h.const_mul Q).mul_const Q.transpose

theorem switch_ordinary_switch (z : ℂ) :
    (GeneralizedSwitching.endpointPermutation : Mat) * ordinaryRotation z *
      GeneralizedSwitching.endpointPermutation = rotation z := by
  simp only [ordinaryRotation]
  calc
    _ = (GeneralizedSwitching.endpointPermutation * GeneralizedSwitching.endpointPermutation) *
      rotation z * (GeneralizedSwitching.endpointPermutation * GeneralizedSwitching.endpointPermutation) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [endpointPermutation_sq, one_mul, mul_one]

/-- The joint exterior law inherits the conjugated symmetry by applying
switch, ordinary rotation, and reverse switch. -/
theorem rotation_invariance_of_switch_and_ordinary
    {A I : Type*} [MeasurableSpace A]
    (μ : Measure (A × (I → Mat))) (z : ℂ)
    (hswitch : Measure.map (action GeneralizedSwitching.endpointPermutation) μ = μ)
    (hordinary : Measure.map (action (ordinaryRotation z)) μ = μ) :
    Measure.map (action (rotation z)) μ = μ := by
  have hπ := measurable_action (A := A) (I := I)
    (GeneralizedSwitching.endpointPermutation : Mat)
  have hO := measurable_action (A := A) (I := I) (ordinaryRotation z)
  have hcomp : action (A := A) (I := I) (rotation z) =
      action GeneralizedSwitching.endpointPermutation ∘
        action (ordinaryRotation z) ∘ action GeneralizedSwitching.endpointPermutation := by
    funext state
    simp only [Function.comp_apply, action_mul]
    rw [← Matrix.mul_assoc, switch_ordinary_switch]
  calc
    _ = Measure.map (action GeneralizedSwitching.endpointPermutation)
        (Measure.map (action (ordinaryRotation z))
          (Measure.map (action GeneralizedSwitching.endpointPermutation) μ)) := by
      rw [Measure.map_map hO hπ, Measure.map_map hπ (hO.comp hπ), hcomp]
    _ = μ := by rw [hswitch, hordinary, hswitch]

/-- Any measurable reconstruction of the exterior state consequently has a
stationary law along the derived rotation. -/
theorem reconstructed_rotation_law
    {A I E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (μ : Measure (A × (I → Mat))) (z : ℂ)
    (hswitch : Measure.map (action GeneralizedSwitching.endpointPermutation) μ = μ)
    (hordinary : Measure.map (action (ordinaryRotation z)) μ = μ)
    (reconstruct : A × (I → Mat) → E) (hr : Measurable reconstruct) :
    Measure.map (reconstruct ∘ action (rotation z)) μ = Measure.map reconstruct μ := by
  rw [← Measure.map_map hr (measurable_action (rotation z)),
    rotation_invariance_of_switch_and_ordinary μ z hswitch hordinary]

end GeneralizedBulk.Exterior
