import GeneralizedBulk.Entropy.ColoredObservationSymmetry
import GeneralizedBulk.Entropy.NormalizedFiniteSignal

/-! Actual finite projected-signal reversibility implies Gaussian admissibility. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Entropy.Hermite GeneralizedBulk.Entropy.Mehler

/-- The actual correlated-star Gaussian conditional densities inherit endpoint
reversal from the finite empirical edge signals. The premise is only a finite
weighted identity; no Gaussian analytic symmetry is assumed. -/
theorem constructed_reversal_admissibility {S : Type*} [Fintype S]
    (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ) (hc : ∀ a, |c a| < 1)
    (D : NormalizedFiniteSignal (ScalarCoordinate d k) S) (sample : S → ColoredStar d k)
    (hsignal : ∀ s, D.signal s = scalarCoordinates d k (sample s))
    (hsym : ∀ i : Fin d, ∀ F : ColoredStar d k → ℝ,
      (∑ s, D.weight s * F (coloredReversal d k hd c i (coloredEdgeProjection d k hd i (sample s)))) =
        ∑ s, D.weight s * F (coloredEdgeProjection d k hd i (sample s)))
    (a : ℝ) (ha : 0 < 1 - a ^ 2) (f : Lp ℝ 2 (standardGaussian (ScalarCoordinate d k)))
    (hf : (f : (ScalarCoordinate d k → ℝ) → ℝ) =ᵐ[standardGaussian (ScalarCoordinate d k)]
      (fun x => D.density a x - 1)) :
    (coloredGaussianFrameSystem d k hd c hc).Admissible f := by
  intro i
  have hproj (s : S) : coordinateProjection (coloredObserved d k hd i)
      ((coloredObservationMatrix d k hd i).transpose.mulVec (D.signal s)) =
        coloredObservationCoordinates d k hd i (coloredEdgeProjection d k hd i (sample s)) := by
    rw [hsignal s, ← coloredObservationCoordinates_eq, ← coloredObservationCoordinates_projection]
  have hsig : ∀ F : (ScalarCoordinate d k → ℝ) → ℝ,
      (∑ s, D.weight s * F ((coloredObservationReversal d k hd c i).mulVec
        (coordinateProjection (coloredObserved d k hd i)
          ((coloredObservationMatrix d k hd i).transpose.mulVec (D.signal s))))) =
      ∑ s, D.weight s * F (coordinateProjection (coloredObserved d k hd i)
        ((coloredObservationMatrix d k hd i).transpose.mulVec (D.signal s))) := by
    intro F
    simp_rw [hproj, coloredObservationReversal_action]
    exact hsym i (fun x => F (coloredObservationCoordinates d k hd i x))
  exact subspaceConditionalL2_centered_mixture_symmetry
    (coloredObservationMatrix d k hd i) (coloredReversalMatrix d k hd c i)
    (coloredObservationReversal d k hd c i) (coloredObservationMatrix_orthogonal d k hd i)
    (isometryMatrix_orthogonal _ _) (coloredObservationReversal_orthogonal d k hd c i)
    (coloredObserved d k hd i) (coloredObservationReversal_involutive d k hd c i)
    (coloredObservationReversal_projection d k hd c hc i)
    (coloredObservationReversal_coordinates d k hd c i) D.weight D.signal hsig a ha f hf

end GeneralizedBulk.Entropy.Channel
