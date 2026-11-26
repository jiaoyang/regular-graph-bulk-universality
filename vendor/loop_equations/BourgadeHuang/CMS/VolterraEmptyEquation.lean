import BourgadeHuang.CMS.VolterraEquation

/-! The eliminated empty component satisfies its original radial equation. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 600000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
namespace VolterraData
variable {R a C : ℝ} (D : VolterraData (E:=E) R a C) (hR : 0<R)

/-- The right-hand side of the empty-component differential equation. -/
def emptySource (Z : Tail R →ᵇ E) : Tail R →ᵇ ℂ :=
  boundedUnweight hR (boundedCoefficientOperator D.C01 (boundedUnweight hR Z))

@[simp] lemma emptySource_apply (Z : Tail R →ᵇ E) (t : Tail R) :
    D.emptySource hR Z t = (t.val⁻¹^2) • D.C01 t (Z t) := by
  simp only [emptySource,boundedUnweight_apply,boundedCoefficientOperator_apply,map_smul,smul_smul,pow_two]

lemma norm_emptySource_le (Z : Tail R →ᵇ E) (t : Tail R) :
    ‖D.emptySource hR Z t‖ ≤ (‖D.C01‖*‖Z‖)*t.val⁻¹^2 := by
  rw [D.emptySource_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ t.val⁻¹^2*(‖D.C01 t‖*‖Z t‖) :=
      mul_le_mul_of_nonneg_left ((D.C01 t).le_opNorm (Z t)) (sq_nonneg _)
    _ ≤ t.val⁻¹^2*(‖D.C01‖*‖Z‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul (D.C01.norm_coe_le_norm t) (Z.norm_coe_le_norm t)
        (norm_nonneg (Z t)) (norm_nonneg D.C01)) (sq_nonneg _)
    _ = _ := mul_comm _ _

lemma integrable_emptySource_tail (Z : Tail R →ᵇ E) :
    IntegrableOn (tailExtension (D.emptySource hR Z)) (Ioi R) := by
  have hi : IntegrableOn (fun s : ℝ => s⁻¹^2) (Ioi R) := by
    apply (integrableOn_Ioi_rpow_of_lt (a:=-(2:ℝ)) (by norm_num) hR).congr_fun _ measurableSet_Ioi
    intro s hs
    dsimp only
    rw [Real.rpow_neg (hR.trans hs).le,Real.rpow_two,inv_pow]
  apply (hi.const_mul (‖D.C01‖*‖Z‖)).mono'
  · exact (tailExtension (D.emptySource hR Z)).continuous.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change R<s at hs
    have hb := D.norm_emptySource_le hR Z ⟨s,hs.le⟩
    simpa only [←tailExtension_apply] using hb

/-- The inverse weight cancels the prefactor in the actual primitive kernel. -/
lemma unweight_primitive_eq_tail (Z : Tail R →ᵇ E) (t : Tail R) :
    unweight (D.primitive hR Z) t =
      -(∫ s in Ioi t.val, tailExtension (D.emptySource hR Z) s) := by
  rw [unweight,D.primitive_apply,←integral_smul,←integral_neg,
    ←integral_shift_tail (fun s => -tailExtension (D.emptySource hR Z) s) t.val]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change 0<u at hu
  have he : (tailShift t u).val=t.val+u := by simp [tailShift,max_eq_right hu.le]
  dsimp only
  rw [←he,tailExtension_apply,D.emptySource_apply]
  simp only [smul_smul]
  match_scalars; field_simp [(hR.trans_le t.property).ne']

/-- The eliminated component has the exact derivative required by the full
radial system, without assuming differentiability of the fixed point. -/
theorem hasDerivAt_emptyComponent (Z : Tail R →ᵇ E) {t : ℝ} (ht : R<t) :
    HasDerivAt (fun s => (1:ℂ)+tailExtension (boundedUnweight hR (D.primitive hR Z)) s)
      (tailExtension (D.emptySource hR Z) t) t := by
  have hd := (hasDerivAt_tailIntegral ht
    (tailExtension (D.emptySource hR Z)).continuous
    (D.integrable_emptySource_tail hR Z)).neg.const_add (1:ℂ)
  simp only [neg_neg] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with x hx
  congr 1
  have he := D.unweight_primitive_eq_tail hR Z ⟨x,hx.le⟩
  change tailExtension (boundedUnweight hR (D.primitive hR Z)) (⟨x,hx.le⟩ : Tail R).val = _
  rw [tailExtension_apply]
  exact he

end VolterraData
end BourgadeHuang.CMS
