import GeneralizedBulk.Entropy.ColoredChaosSquares
import GeneralizedBulk.Entropy.GaussianChannelFixed

/-! The actual correlated-star fourth-chaos defect has zero kernel. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Entropy.Hermite GeneralizedBulk.Entropy.Tensor

/-- The geometric edge projector written in the fixed scalar-adapted
coordinates used by the actual Gaussian polynomial. -/
def coloredProjectionCoordinates (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    (ScalarCoordinate d k → ℝ) →L[ℝ] (ScalarCoordinate d k → ℝ) :=
  (scalarCoordinates d k).toContinuousLinearMap.comp
    ((coloredEdgeProjection d k hd i).toContinuousLinearMap.comp
      (scalarCoordinates d k).symm.toContinuousLinearMap)

@[simp] theorem coloredProjectionCoordinates_apply (d k : ℕ) (hd : 2 ≤ d) (i : Fin d)
    (x : ScalarCoordinate d k → ℝ) :
    coloredProjectionCoordinates d k hd i x =
      scalarCoordinates d k (coloredEdgeProjection d k hd i ((scalarCoordinates d k).symm x)) := rfl

/-- A literal polynomial invariant under the actual edge projection is fixed
by the genuine Gaussian edge conditional expectation. -/
theorem colored_channel_eq_self_of_projection_invariant {K : Type*} [Fintype K]
    (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ) (hc : ∀ a, |c a| < 1)
    (a : K → ScalarCoordinate d k → ℕ) (coeff : K → ℝ) (degree : ℕ)
    (hdegree : ∀ t, (∑ j, a t j) ≤ degree) (i : Fin d)
    (hinv : ∀ x, starChaosFunction d k a coeff (coloredEdgeProjection d k hd i x) = starChaosFunction d k a coeff x) :
    (coloredGaussianFrameSystem d k hd c hc).channel i (chaosLp a coeff) = chaosLp a coeff := by
  apply subspaceConditionalL2_eq_self_of_discarded_derivatives_zero _ _ _ a coeff degree hdegree
  intro v hv
  apply directionalLp_eq_zero_of_linear_invariance a coeff (coloredProjectionCoordinates d k hd i)
  · intro x
    have hh := hinv ((scalarCoordinates d k).symm x)
    simpa only [starChaosFunction, coloredProjectionCoordinates_apply,
      ContinuousLinearEquiv.apply_symm_apply] using hh
  · have hp : coloredEdgeProjection d k hd i ((scalarCoordinates d k).symm v) = 0 := by
      apply colored_projection_zero_of_discarded_coordinates d k hd i
      intro j hj
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hv j hj
    rw [coloredProjectionCoordinates_apply, hp, map_zero]

/-- The source's fourth homogeneous Gaussian defect has no nonzero admissible
zero vector. All channel geometry, differentiation, and tensor algebra have
been discharged against actual Gaussian polynomials. -/
theorem coloredGaussian_fourth_zero_kernel (d k : ℕ) (hd : 3 ≤ d) (c : Fin k → ℝ)
    (hbulk : ∀ a, (c a) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (coeff : DegreeIndex (ScalarCoordinate d k) 4 → ℝ)
    (hadm : (coloredGaussianFrameSystem d k (by omega) c
      (fun a => (bulk_rho_lower d hd (c a) (hbulk a)).1)).Admissible
        (chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff))
    (hzero : (coloredGaussianFrameSystem d k (by omega) c
      (fun a => (bulk_rho_lower d hd (c a) (hbulk a)).1)).defect
        (chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff) = 0) :
    chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff = 0 := by
  let hc := fun a => (bulk_rho_lower d hd (c a) (hbulk a)).1
  let G := coloredGaussianFrameSystem d k (by omega) c hc
  have hA (a : Fin k) : 0 < weightA d (c a) := (bulk_weights_pos d hd (c a) (hbulk a)).1
  have hB (a : Fin k) : 0 < weightB d (c a) := (bulk_weights_pos d hd (c a) (hbulk a)).2
  have hmixed := colored_zero_defect_mixedThird d k (by omega) c hc 4 coeff hadm hA hB hzero
  have hfix (i : Fin d) : G.channel i (chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff) =
      chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff := by
    apply colored_channel_eq_self_of_projection_invariant d k (by omega) c hc _ coeff 4
      (fun a => (degreeIndexNat_sum (ScalarCoordinate d k) a).le) i
    exact fourthChaos_edgeProjection d k hd (degreeIndexNat (ScalarCoordinate d k))
      (degreeIndexNat_injective (ScalarCoordinate d k) 4) coeff (degreeIndexNat_sum (ScalarCoordinate d k)) hmixed i
  change ‖chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff‖ ^ 2 - (1 / 2 : ℝ) *
    (∑ i : Fin d, ‖G.channel i (chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff)‖ ^ 2) = 0 at hzero
  simp_rw [hfix] at hzero
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hzero
  have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hn := sq_nonneg ‖chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff‖
  have hsq : ‖chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff‖ ^ 2 = 0 := by nlinarith
  exact norm_eq_zero.mp (pow_eq_zero hsq)

/-- Strict pointwise positivity in degree four, with the actual inherited
Gaussian L² norm. A compact-parameter argument can now make this uniform. -/
theorem coloredGaussian_fourth_defect_pos (d k : ℕ) (hd : 3 ≤ d) (c : Fin k → ℝ)
    (hbulk : ∀ a, (c a) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (coeff : DegreeIndex (ScalarCoordinate d k) 4 → ℝ)
    (hadm : (coloredGaussianFrameSystem d k (by omega) c
      (fun a => (bulk_rho_lower d hd (c a) (hbulk a)).1)).Admissible
        (chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff))
    (hne : chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff ≠ 0) :
    0 < (coloredGaussianFrameSystem d k (by omega) c
      (fun a => (bulk_rho_lower d hd (c a) (hbulk a)).1)).defect
        (chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff) := by
  have hn := coloredGaussian_defect_nonneg d k hd c hbulk 4 (by decide) coeff hadm
  refine lt_of_le_of_ne hn ?_
  intro heq
  exact hne (coloredGaussian_fourth_zero_kernel d k hd c hbulk coeff hadm heq.symm)

end GeneralizedBulk.Entropy.Channel
