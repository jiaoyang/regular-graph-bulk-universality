import BourgadeHuang.NevanlinnaPositivity
import BourgadeHuang.AnchoredStateBorel

/-!
# Concrete compensated particle states

This adapter constructs the imported anchored counting state from a locally
finite counting measure and its exact imaginary anchor mass. The resulting
state has zero affine Nevanlinna coefficient. No validity or measurability
certificate is postulated: both are proved from the displayed hypotheses.
-/
noncomputable section
open MeasureTheory
open BourgadeHuang

namespace GeneralizedBulk

/-- Exact weighted mass implies every compact-cutoff validity inequality. -/
theorem valid_particleState (ξ : LocalCountingMeasure) (anchor : ℂ)
    (hweight : Integrable nevanlinnaWeight ξ.measure)
    (hanchor : (∫ x, nevanlinnaWeight x ∂ξ.measure) = anchor.im) :
    ValidAnchoredCountingState (ξ, anchor) := by
  intro n
  have hcut : Integrable (fun x => nevanlinnaWeightCutoff n x) ξ.measure :=
    (nevanlinnaWeightCutoff n).continuous.integrable_of_hasCompactSupport
      (nevanlinnaWeightCutoff n).hasCompactSupport
  calc
    (∫ x, nevanlinnaWeightCutoff n x ∂ξ.measure) ≤
        ∫ x, nevanlinnaWeight x ∂ξ.measure :=
      integral_mono hcut hweight (nevanlinnaWeightCutoff_le n)
    _ = anchor.im := hanchor

/-- The concrete state used to import a compensated particle transform. -/
def particleState (ξ : LocalCountingMeasure) (anchor : ℂ)
    (hweight : Integrable nevanlinnaWeight ξ.measure)
    (hanchor : (∫ x, nevanlinnaWeight x ∂ξ.measure) = anchor.im) :
    AnchoredCountingState :=
  ⟨(ξ, anchor), valid_particleState ξ anchor hweight hanchor⟩

@[simp] theorem particleState_counting (ξ : LocalCountingMeasure) (anchor : ℂ)
    (hweight : Integrable nevanlinnaWeight ξ.measure)
    (hanchor : (∫ x, nevanlinnaWeight x ∂ξ.measure) = anchor.im) :
    (particleState ξ anchor hweight hanchor).val.1 = ξ := rfl

@[simp] theorem particleState_anchor (ξ : LocalCountingMeasure) (anchor : ℂ)
    (hweight : Integrable nevanlinnaWeight ξ.measure)
    (hanchor : (∫ x, nevanlinnaWeight x ∂ξ.measure) = anchor.im) :
    (particleState ξ anchor hweight hanchor).val.2 = anchor := rfl

/-- The exact imaginary anchor removes all linear mass at infinity. -/
@[simp] theorem particleState_linearCoefficient_zero
    (ξ : LocalCountingMeasure) (anchor : ℂ)
    (hweight : Integrable nevanlinnaWeight ξ.measure)
    (hanchor : (∫ x, nevanlinnaWeight x ∂ξ.measure) = anchor.im) :
    anchoredLinearCoefficient (particleState ξ anchor hweight hanchor) = 0 := by
  simp [anchoredLinearCoefficient, particleState, hanchor]

/-- The imported reconstruction is the compensated transform with this anchor. -/
theorem particleState_regularized (ξ : LocalCountingMeasure) (anchor : ℂ)
    (hweight : Integrable nevanlinnaWeight ξ.measure)
    (hanchor : (∫ x, nevanlinnaWeight x ∂ξ.measure) = anchor.im)
    {z : ℂ} (hz : z.im ≠ 0) :
    anchoredNevanlinna (particleState ξ anchor hweight hanchor) z =
      (anchor.re : ℂ) + ∫ x, regularizedResolventKernel z x ∂ξ.measure := by
  rw [anchoredNevanlinna_eq_regularized _ hz, particleState_linearCoefficient_zero]
  simp

/-- Literal compensated representation from the manuscript, without a linear term. -/
theorem particleState_compensated (ξ : LocalCountingMeasure) (anchor : ℂ)
    (hweight : Integrable nevanlinnaWeight ξ.measure)
    (hanchor : (∫ x, nevanlinnaWeight x ∂ξ.measure) = anchor.im)
    {z : ℂ} (hz : z.im ≠ 0) :
    anchoredNevanlinna (particleState ξ anchor hweight hanchor) z =
      (anchor.re : ℂ) + ∫ x : ℝ,
        (((x : ℂ) - z)⁻¹ - ((x / (1 + x ^ 2) : ℝ) : ℂ)) ∂ξ.measure := by
  simpa only [regularizedResolventKernel, nevanlinnaWeight, div_eq_mul_inv] using
    particleState_regularized ξ anchor hweight hanchor hz

/-- The literal compensated kernel is integrable, so reconstruction does not
rely on the totalized value of an undefined Bochner integral. -/
theorem integrable_particleState_compensated (ξ : LocalCountingMeasure) (anchor : ℂ)
    (hweight : Integrable nevanlinnaWeight ξ.measure)
    (hanchor : (∫ x, nevanlinnaWeight x ∂ξ.measure) = anchor.im)
    {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun x : ℝ =>
      (((x : ℂ) - z)⁻¹ - ((x / (1 + x ^ 2) : ℝ) : ℂ))) ξ.measure := by
  simpa only [regularizedResolventKernel, nevanlinnaWeight, div_eq_mul_inv,
    particleState_counting] using
    integrable_regularizedResolventKernel (particleState ξ anchor hweight hanchor) hz

/-- The scalar data equal the anchor at the normalization point `i`. -/
@[simp] theorem particleState_at_I (ξ : LocalCountingMeasure) (anchor : ℂ)
    (hweight : Integrable nevanlinnaWeight ξ.measure)
    (hanchor : (∫ x, nevanlinnaWeight x ∂ξ.measure) = anchor.im) :
    anchoredNevanlinna (particleState ξ anchor hweight hanchor) Complex.I = anchor := by
  simp

/-- A measurable counting configuration and complex anchor give a genuinely
measurable subtype-valued state. The integrability and mass conditions occur
only in the proof of its validity. -/
theorem measurable_particleState {Ω : Type*} [MeasurableSpace Ω]
    (ξ : Ω → LocalCountingMeasure) (anchor : Ω → ℂ)
    (hξ : Measurable ξ) (ha : Measurable anchor)
    (hweight : ∀ ω, Integrable nevanlinnaWeight (ξ ω).measure)
    (hanchor : ∀ ω, (∫ x, nevanlinnaWeight x ∂(ξ ω).measure) = (anchor ω).im) :
    Measurable (fun ω => particleState (ξ ω) (anchor ω) (hweight ω) (hanchor ω)) := by
  exact (hξ.prodMk ha).subtype_mk

end GeneralizedBulk
