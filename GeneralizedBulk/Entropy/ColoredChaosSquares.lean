import GeneralizedBulk.Entropy.ColoredGaussianChannels
import GeneralizedBulk.Entropy.FourthChaosKernel
import GeneralizedBulk.Entropy.MixedDerivativeCancellation

/-! Zero Gaussian star defect gives the actual mixed differential kernel. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Entropy.Hermite GeneralizedBulk.Entropy.Tensor

variable (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ) (hc : ∀ a, |c a| < 1)

def coloredProjectedStarFunction (degree : ℕ)
    (coeff : DegreeIndex (ScalarCoordinate d k) degree → ℝ) (i : Fin d) : ColoredStar d k → ℝ :=
  starChaosFunction d k (degreeIndexNat (ScalarCoordinate d k))
    ((coloredGaussianFrameSystem d k hd c hc).projectedCoeff degree coeff i)

/-- Actual directional chain rule for the fixed orthonormal star coordinates. -/
theorem fderiv_starChaosFunction {K : Type*} [Fintype K]
    (a : K → ScalarCoordinate d k → ℕ) (coeff : K → ℝ) (x v : ColoredStar d k) :
    fderiv ℝ (starChaosFunction d k a coeff) x v =
      fderiv ℝ (chaosFunction a coeff) (scalarCoordinates d k x) (scalarCoordinates d k v) := by
  have hf : Differentiable ℝ (chaosFunction a coeff) :=
    (contDiff_chaosFunction a coeff).differentiable (by simp)
  have hh := ((hf (scalarCoordinates d k x)).hasFDerivAt).comp x
    (scalarCoordinates d k).toContinuousLinearMap.hasFDerivAt
  change fderiv ℝ (chaosFunction a coeff ∘ scalarCoordinates d k) x v = _
  rw [hh.fderiv]
  rfl

/-- The actual conditional polynomial has zero derivative in every discarded
geometric direction, at every point. -/
theorem coloredProjectedStarFunction_discarded (degree : ℕ)
    (coeff : DegreeIndex (ScalarCoordinate d k) degree → ℝ) (i : Fin d) (x u : ColoredStar d k) :
    fderiv ℝ (coloredProjectedStarFunction d k hd c hc degree coeff i) x
      (u - coloredEdgeProjection d k hd i u) = 0 := by
  let G := coloredGaussianFrameSystem d k hd c hc
  have hz := subspaceConditionalL2_directional_eq_zero (G.coordinates i) (G.orthogonal i) (G.observed i)
    (degreeIndexNat (ScalarCoordinate d k)) coeff (degreeIndexNat (ScalarCoordinate d k))
    (G.projectedCoeff degree coeff i) degree
    (fun a => (degreeIndexNat_sum (ScalarCoordinate d k) a).le)
    (fun a => (degreeIndexNat_sum (ScalarCoordinate d k) a).le)
    (G.projectedCoeff_spec degree coeff i)
    (scalarCoordinates d k (u - coloredEdgeProjection d k hd i u))
    (colored_discarded_coordinates d k hd i u)
  have hp := fderiv_eq_zero_of_directionalLp_eq_zero (degreeIndexNat (ScalarCoordinate d k))
    (G.projectedCoeff degree coeff i) (scalarCoordinates d k (u - coloredEdgeProjection d k hd i u))
    degree (fun a => (degreeIndexNat_sum (ScalarCoordinate d k) a).le) hz (scalarCoordinates d k x)
  exact (fderiv_starChaosFunction d k _ _ x _).trans hp

/-- Zero defect forces every retained derivative to coincide with that of
the actual conditional polynomial. The complete edge projector is reconstructed
from the concrete adapted frame, so no span hypothesis is needed. -/
theorem colored_zero_defect_retained (degree : ℕ)
    (coeff : DegreeIndex (ScalarCoordinate d k) degree → ℝ)
    (hadm : (coloredGaussianFrameSystem d k hd c hc).Admissible
      (chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff))
    (hA : ∀ a, 0 < weightA d (c a)) (hB : ∀ a, 0 < weightB d (c a))
    (hzero : (coloredGaussianFrameSystem d k hd c hc).defect
      (chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff) = 0)
    (i : Fin d) (x v : ColoredStar d k) :
    fderiv ℝ (starChaosFunction d k (degreeIndexNat (ScalarCoordinate d k)) coeff) x
      (coloredEdgeProjection d k hd i v) =
    fderiv ℝ (coloredProjectedStarFunction d k hd c hc degree coeff i) x
      (coloredEdgeProjection d k hd i v) := by
  let G := coloredGaussianFrameSystem d k hd c hc
  have hbasis (a : Fin k) := G.zero_defect_pointwise degree coeff hadm
    (fun _ a => hA a) (fun _ a => hB a) hzero i a (scalarCoordinates d k x)
  have hdirA (a : Fin k) :
      fderiv ℝ (starChaosFunction d k (degreeIndexNat (ScalarCoordinate d k)) coeff) x (coloredDirectionA d k hd c i a) =
      fderiv ℝ (coloredProjectedStarFunction d k hd c hc degree coeff i) x (coloredDirectionA d k hd c i a) := by
    unfold coloredProjectedStarFunction
    rw [fderiv_starChaosFunction, fderiv_starChaosFunction]
    exact (hbasis a).1
  have hdirB (a : Fin k) :
      fderiv ℝ (starChaosFunction d k (degreeIndexNat (ScalarCoordinate d k)) coeff) x (coloredDirectionB d k hd c i a) =
      fderiv ℝ (coloredProjectedStarFunction d k hd c hc degree coeff i) x (coloredDirectionB d k hd c i a) := by
    unfold coloredProjectedStarFunction
    rw [fderiv_starChaosFunction, fderiv_starChaosFunction]
    exact (hbasis a).2
  rw [coloredEdgeProjection_reconstruction d k hd c hc i v]
  simp only [map_sum, map_add, map_smul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [hdirA a, hdirB a]

/-- The genuine Gaussian zero-defect condition implies exactly the source
mixed third-derivative condition, with actual Fréchet derivatives. -/
theorem colored_zero_defect_mixedThird (degree : ℕ)
    (coeff : DegreeIndex (ScalarCoordinate d k) degree → ℝ)
    (hadm : (coloredGaussianFrameSystem d k hd c hc).Admissible
      (chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff))
    (hA : ∀ a, 0 < weightA d (c a)) (hB : ∀ a, 0 < weightB d (c a))
    (hzero : (coloredGaussianFrameSystem d k hd c hc).defect
      (chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff) = 0)
    (x : ColoredStar d k) (i : Fin d) (u v w : ColoredStar d k) :
    thirdDifferential (starChaosFunction d k (degreeIndexNat (ScalarCoordinate d k)) coeff) x
      (u - coloredEdgeProjection d k hd i u) (coloredEdgeProjection d k hd i v) w = 0 := by
  exact mixedThird_zero_of_derivative_projection _ _ (contDiff_starChaosFunction d k _ coeff)
    (contDiff_starChaosFunction d k _ _) (coloredEdgeProjection d k hd i).toContinuousLinearMap
    (colored_zero_defect_retained d k hd c hc degree coeff hadm hA hB hzero i)
    (coloredProjectedStarFunction_discarded d k hd c hc degree coeff i) x u v w

end GeneralizedBulk.Entropy.Channel
