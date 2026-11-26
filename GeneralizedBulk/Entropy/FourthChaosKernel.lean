import GeneralizedBulk.Entropy.ScalarCoordinates
import GeneralizedBulk.Entropy.DifferentialKernel
import GeneralizedBulk.Entropy.TopDerivativeSupport

/-! The concrete mixed differential kernel on fourth Gaussian chaos is scalar-only. -/
noncomputable section
open scoped BigOperators Topology ContDiff

namespace GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Entropy.Hermite GeneralizedBulk.Entropy.Tensor

variable (d k : ℕ) (hd : 3 ≤ d)
variable {K : Type*} [Fintype K]
variable (a : K → ScalarCoordinate d k → ℕ) (ha : Function.Injective a) (coeff : K → ℝ)
variable (hdegree : ∀ t, ∑ j, a t j = 4)

/-- A literal Hermite polynomial on the star, using a fixed scalar-adapted
orthonormal basis. No leading-term or tensor identification is postulated. -/
def starChaosFunction : ColoredStar d k → ℝ :=
  fun x => chaosFunction a coeff (scalarCoordinates d k x)

theorem contDiff_starChaosFunction : ContDiff ℝ ω (starChaosFunction d k a coeff) :=
  (contDiff_chaosFunction a coeff).comp (scalarCoordinates d k).contDiff

variable (hmixed : ∀ x, ∀ i : Fin d, ∀ u v w,
  thirdDifferential (starChaosFunction d k a coeff) x
    (u - coloredEdgeProjection d k (by omega) i u)
    (coloredEdgeProjection d k (by omega) i v) w = 0)

include hd hmixed in
theorem fourthChaos_unobserved_top_zero (i : ScalarCoordinate d k)
    (hi : i ∉ scalarObserved d k) (x : ScalarCoordinate d k → ℝ)
    (m : Fin 3 → (ScalarCoordinate d k → ℝ)) :
    iteratedFDeriv ℝ 4 (chaosFunction a coeff) x (Fin.snoc m (Pi.single i 1)) = 0 := by
  let g := (scalarCoordinates d k).symm.toContinuousLinearMap
  have hf := contDiff_starChaosFunction d k a coeff
  have hcomp : starChaosFunction d k a coeff ∘ g = chaosFunction a coeff := by
    funext y
    exact congrArg (chaosFunction a coeff) ((scalarCoordinates d k).apply_symm_apply y)
  have hc := g.iteratedFDeriv_comp_right hf x (i := 4) (by simp)
  rw [hcomp] at hc
  rw [hc, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change iteratedFDeriv ℝ 4 (starChaosFunction d k a coeff) (g x)
    ((fun y => g y) ∘ Fin.snoc m (Pi.single i 1)) = 0
  have he := Fin.comp_snoc (fun y : ScalarCoordinate d k → ℝ => g y) m (Pi.single i 1)
  rw [he]
  exact fourthDifferential_last_transverse_zero d k hd _ hf hmixed _ _ _
    (transversePart_scalarCoordinates_symm_basis d k i hi)

include hd ha hdegree hmixed in
/-- The mixed-kernel condition forces the whole fourth-chaos polynomial,
including every lower Hermite term, to depend only on scalar coordinates. -/
theorem fourthChaos_scalarPart (x : ColoredStar d k) :
    starChaosFunction d k a coeff x =
      starChaosFunction d k a coeff (scalarPart d k x) := by
  apply chaosFunction_eq_of_eq_on_observed (scalarObserved d k) a ha coeff 3 hdegree
    (fourthChaos_unobserved_top_zero d k hd a coeff hmixed)
  intro i hi
  rw [scalarCoordinates_scalarPart]
  exact (if_pos hi).symm

theorem scalarPart_coloredEdgeProjection (i : Fin d) (x : ColoredStar d k) :
    scalarPart d k (coloredEdgeProjection d k (by omega) i x) = scalarPart d k x := by
  ext b
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext <;> simp [scalarPart, coloredEdgeProjection, edgeProjection]

include hd ha hdegree hmixed in
/-- Every actual edge projection fixes a fourth-chaos polynomial in the
mixed differential kernel. -/
theorem fourthChaos_edgeProjection (i : Fin d) (x : ColoredStar d k) :
    starChaosFunction d k a coeff (coloredEdgeProjection d k (by omega) i x) =
      starChaosFunction d k a coeff x := by
  rw [fourthChaos_scalarPart d k hd a ha coeff hdegree hmixed,
    scalarPart_coloredEdgeProjection d k hd]
  exact (fourthChaos_scalarPart d k hd a ha coeff hdegree hmixed x).symm

end GeneralizedBulk.Entropy.Channel
