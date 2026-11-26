import BourgadeHuang.CMS.ComplexPrimitiveOperator
import BourgadeHuang.CMS.VolterraEquation

/-! The actual weighted primitive satisfies the empty-component radial ODE. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E] {R : ℝ}
  (hR : 0<R)

/-- The actual square-weighted source is integrable on the infinite tail. -/
theorem integrable_doubleUnweight_tail (f : Tail R →ᵇ E) :
    IntegrableOn (tailExtension (boundedUnweight hR (boundedUnweight hR f))) (Ioi R) := by
  have hi : IntegrableOn (fun s : ℝ => s⁻¹^2) (Ioi R) := by
    apply (integrableOn_Ioi_rpow_of_lt (a:=-(2:ℝ)) (by norm_num) hR).congr_fun _ measurableSet_Ioi
    intro s hs
    dsimp only
    rw [Real.rpow_neg (hR.trans hs).le,Real.rpow_two,inv_pow]
  apply (hi.const_mul ‖f‖).mono'
  · exact (tailExtension (boundedUnweight hR (boundedUnweight hR f))).continuous.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change R<s at hs
    change ‖tailExtension (boundedUnweight hR (boundedUnweight hR f)) (⟨s,hs.le⟩ : Tail R).val‖≤_
    rw [tailExtension_apply,boundedUnweight_apply,boundedUnweight_apply,smul_smul,norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (hR.trans hs).le)
        (inv_nonneg.mpr (hR.trans hs).le))]
    calc
      _≤(s⁻¹*s⁻¹)*‖f‖ := mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (mul_self_nonneg _)
      _=‖f‖*s⁻¹^2 := by ring

/-- Cancellation of the radial prefactor gives the true improper tail. -/
theorem unweight_complexPrimitive_eq_tail (f : Tail R →ᵇ E) (t : Tail R) :
    boundedUnweight hR (complexPrimitiveOperator hR f) t=
      -(∫s in Ioi t.val,tailExtension (boundedUnweight hR (boundedUnweight hR f)) s) := by
  rw [boundedUnweight_apply,complexPrimitiveOperator_apply,←integral_smul,←integral_neg,
    ←integral_shift_tail (fun s => -tailExtension (boundedUnweight hR (boundedUnweight hR f)) s) t.val]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change 0<u at hu
  have he : (tailShift t u).val=t.val+u := by simp [tailShift,max_eq_right hu.le]
  dsimp only
  rw [←he,tailExtension_apply,boundedUnweight_apply,boundedUnweight_apply]
  simp only [smul_smul,←neg_smul]
  match_scalars
  field_simp [(hR.trans_le t.property).ne']
  ring

/-- Differentiability is derived from the constructed integral, without a
regularity assumption on the fixed point. -/
theorem hasDerivAt_unweight_complexPrimitive (f : Tail R →ᵇ E)
    {t : ℝ} (ht : R<t) :
    HasDerivAt (tailExtension (boundedUnweight hR (complexPrimitiveOperator hR f)))
      (tailExtension (boundedUnweight hR (boundedUnweight hR f)) t) t := by
  have hd := (hasDerivAt_tailIntegral ht
    (tailExtension (boundedUnweight hR (boundedUnweight hR f))).continuous
    (integrable_doubleUnweight_tail hR f)).neg
  simp only [neg_neg] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with s hs
  change tailExtension (boundedUnweight hR (complexPrimitiveOperator hR f)) (⟨s,hs.le⟩ : Tail R).val=_
  rw [tailExtension_apply]
  exact unweight_complexPrimitive_eq_tail hR f ⟨s,hs.le⟩

end BourgadeHuang.CMS
