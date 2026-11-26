import BourgadeHuang.RationalBulk.Foundation

/-! Exact agreement with the already checked orthogonal/unitary hierarchy.
These are identities of actual loop observables and hypotheses. -/
noncomputable section
open MeasureTheory
namespace BourgadeHuang.RationalBulk

@[simp] theorem loopIntegrand_one {n : ℕ} (s : AnchoredCountingState)
    (w : ℂ) (aux : Fin n → ℂ) :
    loopIntegrand 1 s w aux = anchoredLoopIntegrand .one s w aux := by
  simp [loopIntegrand, anchoredLoopIntegrand, Beta.value]

@[simp] theorem loopIntegrand_two {n : ℕ} (s : AnchoredCountingState)
    (w : ℂ) (aux : Fin n → ℂ) :
    loopIntegrand 2 s w aux = anchoredLoopIntegrand .two s w aux := by
  simp [loopIntegrand, anchoredLoopIntegrand, Beta.value]

theorem exactHierarchy_one_iff (ν : Measure AnchoredCountingState) :
    ExactHierarchy ν 1 ↔ ExactAnchoredHierarchy ν .one := by
  simp only [ExactHierarchy, ExactAnchoredHierarchy, loopIntegrand_one]

theorem exactHierarchy_two_iff (ν : Measure AnchoredCountingState) :
    ExactHierarchy ν 2 ↔ ExactAnchoredHierarchy ν .two := by
  simp only [ExactHierarchy, ExactAnchoredHierarchy, loopIntegrand_two]

theorem vanishingHierarchy_one_iff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → AnchoredCountingState) :
    VanishingHierarchy μ 1 X ↔ VanishingAnchoredHierarchy μ .one X := by
  simp only [VanishingHierarchy, VanishingAnchoredHierarchy, loopIntegrand_one]

theorem vanishingHierarchy_two_iff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → AnchoredCountingState) :
    VanishingHierarchy μ 2 X ↔ VanishingAnchoredHierarchy μ .two X := by
  simp only [VanishingHierarchy, VanishingAnchoredHierarchy, loopIntegrand_two]

end BourgadeHuang.RationalBulk
