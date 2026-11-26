import BourgadeHuang.CMS.VolterraEquation
import BourgadeHuang.CMS.TriangularTail

/-! The constructed weighted fixed point satisfies the actual radial ODE. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 800000
variable {J : Type*} [Fintype J] [DecidableEq J]

lemma triangularKernel_eq_principal {R : ℝ} (lam : J → ℂ)
    (N : Tail R →ᵇ (J → J → ℂ)) (H : ℕ) (t : Tail R) {u : ℝ} (hu : 0<u) :
    triangularKernel lam N H t u = principalOperator lam N H t.val (t.val+u) := by
  simp only [triangularKernel,principalOperator,tailShift,max_eq_right hu.le]

section FixedPoint
variable {R a : ℝ} (hR : 0<R) (ha : 0<a) (lam : J → ℂ)
  (N : Tail R →ᵇ (J → J → ℂ)) (degree : J → ℕ)
  (hN : ∀ x i j, ¬ degree j<degree i → N x i j=0)
  (H : ℕ) (hH : ∀ i, degree i<H) (hlam : ∀ i, 2*a≤(lam i).re)
  (C01 : Tail R →ᵇ ((J → ℂ) →L[ℝ] ℂ))
  (C10 : Tail R →ᵇ (ℂ →L[ℝ] (J → ℂ)))
  (C11 : Tail R →ᵇ ((J → ℂ) →L[ℝ] (J → ℂ)))

local notation "D" => triangularVolterraData ha lam N H hlam C01 C10 C11
local notation "hC" => triangularDecayConstant_nonneg ha (norm_nonneg N) H
include degree hN hH

/-- The fixed point is the genuine improper variation-of-constants integral. -/
theorem triangular_fixedPoint_eq_backwardTail
    (Z : Tail R →ᵇ (J → ℂ)) (hZ : (D).map hR ha hC Z=Z) (t : Tail R) :
    unweight Z t = backwardTail (principalOperator lam N H) R
      (tailExtension ((D).source hR Z)) t.val := by
  rw [backwardTail_eq_integral _ _ _
    (principalOperator_comp lam N degree hN H hH)
    (integrable_principalOperator_tail ha lam N H hlam _) t.property]
  have he := (D).unweight_map_eq_integral hR ha hC Z t
  rw [hZ] at he
  rw [he]
  congr 1
  rw [←integral_shift_tail (fun s => principalOperator lam N H t.val s
    (tailExtension ((D).source hR Z) s)) t.val]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change 0<u at hu
  change triangularKernel lam N H t u ((D).source hR Z (tailShift t u)) = _
  rw [triangularKernel_eq_principal lam N H t hu]
  congr 1
  have ht : (tailShift t u).val=t.val+u := by simp [tailShift,max_eq_right hu.le]
  rw [←ht,tailExtension_apply]

/-- On the interior half-line, the unweighted fixed point solves the nonempty
component equation. Its forcing contains the constructed empty component. -/
theorem hasDerivAt_triangular_fixedPoint
    (Z : Tail R →ᵇ (J → ℂ)) (hZ : (D).map hR ha hC Z=Z) {t : ℝ} (ht : R<t) :
    HasDerivAt (tailExtension (boundedUnweight hR Z))
      (triangularGenerator lam N t (tailExtension (boundedUnweight hR Z) t)+
        tailExtension ((D).source hR Z) t) t := by
  have he : ∀ x, R≤x → tailExtension (boundedUnweight hR Z) x =
      backwardTail (principalOperator lam N H) R (tailExtension ((D).source hR Z)) x := by
    intro x hx
    have hh := triangular_fixedPoint_eq_backwardTail hR ha lam N degree hN H hH hlam
      C01 C10 C11 Z hZ ⟨x,hx⟩
    change tailExtension (boundedUnweight hR Z) (⟨x,hx⟩ : Tail R).val = _
    rw [tailExtension_apply]
    exact hh
  have hd := hasDerivAt_triangularBackwardTail ha lam N degree hN H hH hlam
    (tailExtension ((D).source hR Z)) ht
  rw [←he t ht.le] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with x hx
  exact he x hx.le

end FixedPoint
end BourgadeHuang.CMS
