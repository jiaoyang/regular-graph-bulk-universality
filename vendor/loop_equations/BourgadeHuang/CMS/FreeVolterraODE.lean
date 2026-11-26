import BourgadeHuang.CMS.FreeTriangularEvolution
import BourgadeHuang.CMS.VolterraEquation

/-! The weighted free Volterra equation implies the actual radial ODE. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

section Unweight
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E] {R : ℝ}

/-- Division by the radial parameter as a genuine bounded complex-linear map. -/
def complexUnweightOperator (hR : 0<R) : (Tail R →ᵇ E) →L[ℂ] (Tail R →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := boundedUnweight hR
      map_add' := by intro f g; ext t; exact smul_add _ _ _
      map_smul' := by intro c f; ext t; exact smul_comm _ _ _ }
    R⁻¹ (fun f => by
      apply (BoundedContinuousFunction.norm_le (mul_nonneg (inv_nonneg.mpr hR.le) (norm_nonneg f))).mpr
      intro t
      exact (norm_unweight_le hR f t).trans (by
        rw [div_eq_mul_inv,mul_comm R⁻¹]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ hR t.property) (norm_nonneg f)))

@[simp] theorem complexUnweightOperator_apply (hR : 0<R) (f : Tail R →ᵇ E) (t : Tail R) :
    complexUnweightOperator hR f t=t.val⁻¹ • f t := rfl

end Unweight

variable {J : Type*} [Fintype J] [DecidableEq J] {R a : ℝ}
  (hR : 0<R) (ha : 0<a) (lam : J → ℂ) (hlam : ∀i,a≤(lam i).re)

/-- The extra inverse-power convolution is the forcing convolution applied
to the actual unweighted function. -/
theorem freeRemainder_eq_forcing_unweight (f : Tail R →ᵇ (J → ℂ)) :
    freeRemainderOperator hR ha lam hlam f=
      freeForcingOperator hR ha lam hlam (boundedUnweight hR f) := by
  apply BoundedContinuousFunction.ext
  intro t
  change (∫u,(-(t.val*(tailShift t u).val⁻¹^2):ℝ) •
      freeDiagonalEvolution lam u (f (tailShift t u)) ∂(volume.restrict (Ioi (0:ℝ))))=
    (∫u,(-(t.val*(tailShift t u).val⁻¹):ℝ) •
      freeDiagonalEvolution lam u ((tailShift t u).val⁻¹ • f (tailShift t u))
      ∂(volume.restrict (Ioi (0:ℝ))))
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  ext j
  change (-(t.val*(tailShift t u).val⁻¹^2):ℝ) •
      (Complex.exp (-lam j*(u:ℂ))*f (tailShift t u) j)=
    (-(t.val*(tailShift t u).val⁻¹):ℝ) •
      (Complex.exp (-lam j*(u:ℂ))*((tailShift t u).val⁻¹ • f (tailShift t u) j))
  simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

/-- Unweighting the actual forcing convolution gives the genuine improper
free backward integral; no integral representation is assumed. -/
theorem unweight_freeForcing_eq_backward (f : Tail R →ᵇ (J → ℂ)) (t : Tail R) :
    boundedUnweight hR (freeForcingOperator hR ha lam hlam f) t=
      freeBackwardTail lam (tailExtension (boundedUnweight hR f)) t.val := by
  unfold freeBackwardTail
  rw [← integral_shift_tail (fun s => freeDiagonalEvolution lam (s-t.val)
    (tailExtension (boundedUnweight hR f) s)) t.val]
  change t.val⁻¹ • (∫u,(-(t.val*(tailShift t u).val⁻¹):ℝ) •
    freeDiagonalEvolution lam u (f (tailShift t u)) ∂(volume.restrict (Ioi (0:ℝ))))=_
  rw [← integral_smul,← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change 0<u at hu
  have he : (tailShift t u).val=t.val+u := by simp [tailShift,max_eq_right hu.le]
  dsimp only
  rw [←he,tailExtension_apply,boundedUnweight_apply]
  rw [he,add_sub_cancel_left]
  ext j
  change t.val⁻¹ • ((-(t.val*(t.val+u)⁻¹):ℝ) •
      (Complex.exp (-lam j*(u:ℂ))*f (tailShift t u) j))=
    -(Complex.exp (-lam j*(u:ℂ))*((t.val+u)⁻¹ • f (tailShift t u) j))
  rw [smul_smul]
  have hc : t.val⁻¹ * (-(t.val*(t.val+u)⁻¹))= -((t.val+u)⁻¹) := by
    field_simp [(hR.trans_le t.property).ne']
  rw [hc]
  simp only [Complex.real_smul,Complex.ofReal_neg]
  ring

/-- The unweighted solution of the constructed free convolution satisfies
its inhomogeneous diagonal differential equation. -/
theorem hasDerivAt_unweight_freeForcing (f : Tail R →ᵇ (J → ℂ))
    {t : ℝ} (ht : R<t) :
    HasDerivAt (tailExtension (boundedUnweight hR (freeForcingOperator hR ha lam hlam f)))
      (complexDiagonalOperator lam
        (tailExtension (boundedUnweight hR (freeForcingOperator hR ha lam hlam f)) t)+
        tailExtension (boundedUnweight hR f) t) t := by
  have he (s : ℝ) (hs : R≤s) :
      tailExtension (boundedUnweight hR (freeForcingOperator hR ha lam hlam f)) s=
        freeBackwardTail lam (tailExtension (boundedUnweight hR f)) s := by
    have hh := unweight_freeForcing_eq_backward hR ha lam hlam f ⟨s,hs⟩
    change tailExtension (boundedUnweight hR (freeForcingOperator hR ha lam hlam f)) (⟨s,hs⟩ : Tail R).val=_
    rw [tailExtension_apply]
    exact hh
  have hd := hasDerivAt_freeBackwardTail ha lam hlam (tailExtension (boundedUnweight hR f)) t
  rw [←he t ht.le] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with s hs
  exact he s hs.le

end BourgadeHuang.CMS
