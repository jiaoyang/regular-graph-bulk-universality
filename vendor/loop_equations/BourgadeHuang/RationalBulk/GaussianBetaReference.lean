import BourgadeHuang.RationalBulk.GaussianReferenceBridge
import BourgadeHuang.RationalBulk.CharacterizationReduction

/-! Gaussian beta references are genuine subsequential limits of the explicit
Lebesgue-density ensembles. The subsequent uniqueness theorem upgrades this
reference to the full Gaussian beta bulk limit. -/
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

structure GaussianBetaReference (β : ℝ) (hβ : 0 < β) where
  law : ProbabilityMeasure AnchoredCountingState
  subsequence : ℕ → ℕ
  strictMono : StrictMono subsequence
  converges : WeakLawConverges (gaussianBetaProduct β hβ)
    (fun N => gaussianBetaState (subsequence N)) (law : Measure AnchoredCountingState)
  hierarchy : ExactHierarchy (law : Measure AnchoredCountingState) β
  exponentialSquare : ∃ a : ℝ, 0 < a ∧ Integrable
    (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2))
    (law : Measure AnchoredCountingState)

theorem exists_gaussianBetaReference_of_finite_identity (β : ℝ) (hβ : 0 < β)
    (hloop : ∀ N n (w : ℂ), w.im ≠ 0 → ∀ aux : Fin n → ℂ,
      (∀ a, (aux a).im ≠ 0) →
      (∫ x, loopIntegrand β (finiteAnchoredState x 0) w aux
        ∂gaussianBetaMeasure β (N+1)) =
        -(w / (N+1:ℂ)) * ∫ x, resolventMonomial (finiteAnchoredState x 0) w aux
          ∂gaussianBetaMeasure β (N+1)) : Nonempty (GaussianBetaReference β hβ) := by
  obtain ⟨ν,r,hr,hw,hh,he⟩ := gaussianBeta_exact_subsequence_of_finite_identity β hβ hloop
  exact ⟨⟨ν,r,hr,hw,hh,he⟩⟩

namespace GaussianBetaReference
variable {β : ℝ} {hβ : 0 < β} (R : GaussianBetaReference β hβ)

def countingLaw : ProbabilityMeasure LocalCountingMeasure := anchoredCountingLaw R.law

theorem vague_subsequence : VagueLawConverges (gaussianBetaProduct β hβ)
    (fun N ω => (gaussianBetaState (R.subsequence N) ω).val.1)
    (R.countingLaw : Measure LocalCountingMeasure) :=
  anchored_sequence_vagueLawConverges (gaussianBetaProduct β hβ)
    (fun N => gaussianBetaState (R.subsequence N)) R.law R.converges

/-- If the exact hierarchy is unique, this specific finite-ensemble reference
is the full Gaussian beta bulk scaling limit. -/
theorem full_convergence_of_uniqueness
    (hv : VanishingHierarchy (gaussianBetaProduct β hβ) β gaussianBetaState)
    (hunique : ∀ ρ : ProbabilityMeasure AnchoredCountingState,
      ExactHierarchy (ρ : Measure AnchoredCountingState) β →
      (∃ a : ℝ, 0 < a ∧ Integrable
        (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2))
          (ρ : Measure AnchoredCountingState)) → ρ = R.law) :
    WeakLawConverges (gaussianBetaProduct β hβ) gaussianBetaState
      (R.law : Measure AnchoredCountingState) :=
  weakLawConverges_of_vanishingHierarchy_and_uniqueness
    (gaussianBetaProduct β hβ) β gaussianBetaState measurable_gaussianBetaState
    (gaussianBetaState_moment β hβ) hv R.law hunique

theorem vague_full_convergence_of_uniqueness
    (hv : VanishingHierarchy (gaussianBetaProduct β hβ) β gaussianBetaState)
    (hunique : ∀ ρ : ProbabilityMeasure AnchoredCountingState,
      ExactHierarchy (ρ : Measure AnchoredCountingState) β →
      (∃ a : ℝ, 0 < a ∧ Integrable
        (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2))
          (ρ : Measure AnchoredCountingState)) → ρ = R.law) :
    VagueLawConverges (gaussianBetaProduct β hβ)
      (fun N ω => (gaussianBetaState N ω).val.1)
      (R.countingLaw : Measure LocalCountingMeasure) :=
  anchored_sequence_vagueLawConverges (gaussianBetaProduct β hβ) gaussianBetaState
    R.law (R.full_convergence_of_uniqueness hv hunique)

end GaussianBetaReference
end BourgadeHuang.RationalBulk
