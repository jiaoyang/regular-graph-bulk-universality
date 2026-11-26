import BourgadeHuang.EdgeCMS.RadialTerminal
import BourgadeHuang.CMS.CoupledVolterraBounds

/-! Explicit admissible tail radii for an actual constant finite radial system.
Every coefficient bound is a norm of the supplied continuous linear map. -/
noncomputable section
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.EdgeCMS
set_option linter.unusedSectionVars false
open CMS

variable {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K]

/-- A common bound for all four genuine matrix blocks. -/
def constantBlockBound
    (N : (J → ℂ) →L[ℂ] (J → ℂ)) (C01 : (J → ℂ) →L[ℂ] (K → ℂ))
    (C10 : (K → ℂ) →L[ℂ] (J → ℂ)) (C11 : (J → ℂ) →L[ℂ] (J → ℂ)) : ℝ :=
  ‖N‖ + ‖C01‖ + ‖C10‖ + ‖C11‖

theorem constantBlockBound_nonneg
    (N : (J → ℂ) →L[ℂ] (J → ℂ)) (C01 : (J → ℂ) →L[ℂ] (K → ℂ))
    (C10 : (K → ℂ) →L[ℂ] (J → ℂ)) (C11 : (J → ℂ) →L[ℂ] (J → ℂ)) :
    0 ≤ constantBlockBound N C01 C10 C11 := by unfold constantBlockBound; positivity

/-- A concrete starting radius, with an additional requested lower bound. -/
def constantRadialRadius (a : ℝ) (H : ℕ) (r : ℝ)
    (N : (J → ℂ) →L[ℂ] (J → ℂ)) (C01 : (J → ℂ) →L[ℂ] (K → ℂ))
    (C10 : (K → ℂ) →L[ℂ] (J → ℂ)) (C11 : (J → ℂ) →L[ℂ] (J → ℂ)) : ℝ :=
  let M := constantBlockBound N C01 C10 C11
  max (max r 0) (triangularInverseBound a M H * a⁻¹ * (M * M + M)) + 1

theorem constantRadialRadius_pos (a : ℝ) (H : ℕ) (r : ℝ)
    (N : (J → ℂ) →L[ℂ] (J → ℂ)) (C01 : (J → ℂ) →L[ℂ] (K → ℂ))
    (C10 : (K → ℂ) →L[ℂ] (J → ℂ)) (C11 : (J → ℂ) →L[ℂ] (J → ℂ)) :
    0 < constantRadialRadius a H r N C01 C10 C11 := by
  unfold constantRadialRadius
  have hh := (le_max_right r 0).trans (le_max_left (max r 0)
    (triangularInverseBound a (constantBlockBound N C01 C10 C11) H * a⁻¹ *
      (constantBlockBound N C01 C10 C11 * constantBlockBound N C01 C10 C11 +
        constantBlockBound N C01 C10 C11)))
  linarith

theorem lt_constantRadialRadius (a : ℝ) (H : ℕ) (r : ℝ)
    (N : (J → ℂ) →L[ℂ] (J → ℂ)) (C01 : (J → ℂ) →L[ℂ] (K → ℂ))
    (C10 : (K → ℂ) →L[ℂ] (J → ℂ)) (C11 : (J → ℂ) →L[ℂ] (J → ℂ)) :
    r < constantRadialRadius a H r N C01 C10 C11 := by
  unfold constantRadialRadius
  have hh := (le_max_left r 0).trans (le_max_left (max r 0)
    (triangularInverseBound a (constantBlockBound N C01 C10 C11) H * a⁻¹ *
      (constantBlockBound N C01 C10 C11 * constantBlockBound N C01 C10 C11 +
        constantBlockBound N C01 C10 C11)))
  linarith


/-- The chosen radius strictly exceeds the genuine elimination bound. -/
theorem constantRadialRadius_large (a : ℝ) (H : ℕ) (r : ℝ)
    (N : (J → ℂ) →L[ℂ] (J → ℂ)) (C01 : (J → ℂ) →L[ℂ] (K → ℂ))
    (C10 : (K → ℂ) →L[ℂ] (J → ℂ)) (C11 : (J → ℂ) →L[ℂ] (J → ℂ)) :
    triangularInverseBound a (constantBlockBound N C01 C10 C11) H * a⁻¹ *
      (constantBlockBound N C01 C10 C11 * constantBlockBound N C01 C10 C11 +
        constantBlockBound N C01 C10 C11) <
    constantRadialRadius a H r N C01 C10 C11 := by
  unfold constantRadialRadius
  have hh := le_max_right (max r 0)
    (triangularInverseBound a (constantBlockBound N C01 C10 C11) H * a⁻¹ *
      (constantBlockBound N C01 C10 C11 * constantBlockBound N C01 C10 C11 +
        constantBlockBound N C01 C10 C11))
  linarith

/-- For fixed matrices the genuine Volterra remainder is contractive at every
radius exceeding the explicit finite triangular bound. -/
theorem constant_radial_smallness {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (lam : J → ℂ) (hlam : ∀ i, a ≤ (lam i).re) (H : ℕ)
    (N : (J → ℂ) →L[ℂ] (J → ℂ)) (C01 : (J → ℂ) →L[ℂ] (K → ℂ))
    (C10 : (K → ℂ) →L[ℂ] (J → ℂ)) (C11 : (J → ℂ) →L[ℂ] (J → ℂ))
    (hlarge : triangularInverseBound a (constantBlockBound N C01 C10 C11) H * a⁻¹ *
      (constantBlockBound N C01 C10 C11 * constantBlockBound N C01 C10 C11 +
        constantBlockBound N C01 C10 C11) < R) :
    ‖triangularInverse ((freeForcingOperator hR ha lam hlam).comp
        (complexBoundedCoefficientOperator (BoundedContinuousFunction.const (Tail R) N))) H *
      coupledVolterraRemainder (freeRemainderOperator hR ha lam hlam)
        (complexPrimitiveOperator (E := K → ℂ) hR)
        (complexBoundedCoefficientOperator (BoundedContinuousFunction.const (Tail R) C01))
        (complexBoundedCoefficientOperator (BoundedContinuousFunction.const (Tail R) C10))
        (complexBoundedCoefficientOperator (BoundedContinuousFunction.const (Tail R) C11))‖ < 1 := by
  have hN : ‖N‖ ≤ constantBlockBound N C01 C10 C11 := by unfold constantBlockBound; linarith [norm_nonneg C01, norm_nonneg C10, norm_nonneg C11]
  have h01 : ‖C01‖ ≤ constantBlockBound N C01 C10 C11 := by unfold constantBlockBound; linarith [norm_nonneg N, norm_nonneg C10, norm_nonneg C11]
  have h10 : ‖C10‖ ≤ constantBlockBound N C01 C10 C11 := by unfold constantBlockBound; linarith [norm_nonneg N, norm_nonneg C01, norm_nonneg C11]
  have h11 : ‖C11‖ ≤ constantBlockBound N C01 C10 C11 := by unfold constantBlockBound; linarith [norm_nonneg N, norm_nonneg C01, norm_nonneg C10]
  apply eliminated_coupledVolterra_lt_one_of_radius hR ha
    (constantBlockBound_nonneg N C01 C10 C11)
    _ _ _ _ _ _ _
    (norm_freeForcingOperator_le hR ha lam hlam)
    (norm_freeRemainderOperator_le hR ha lam hlam)
    (norm_complexPrimitiveOperator_le hR)
    _ _ _ _ H hlarge
  · exact (norm_complexBoundedCoefficientOperator_le _).trans
      ((BoundedContinuousFunction.norm_const_le _).trans hN)
  · exact (norm_complexBoundedCoefficientOperator_le _).trans
      ((BoundedContinuousFunction.norm_const_le _).trans h01)
  · exact (norm_complexBoundedCoefficientOperator_le _).trans
      ((BoundedContinuousFunction.norm_const_le _).trans h10)
  · exact (norm_complexBoundedCoefficientOperator_le _).trans
      ((BoundedContinuousFunction.norm_const_le _).trans h11)

end BourgadeHuang.EdgeCMS
