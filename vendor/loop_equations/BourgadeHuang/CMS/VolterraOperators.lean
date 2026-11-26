import BourgadeHuang.CMS.VolterraTail

/-! The two actual weighted tail integral operators in the CMS Volterra equation. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option linter.unusedSectionVars false
variable {R : ℝ} {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private lemma continuous_weight (hR : 0<R) :
    Continuous (fun p : Tail R × ℝ => p.1.val * (tailShift p.1 p.2).val⁻¹^2) := by
  exact (continuous_subtype_val.comp continuous_fst).mul
    (((continuous_subtype_val.comp continuous_tailShift).inv₀
      (fun p => (tailShift_pos hR p.1 p.2).ne')).pow 2)

private lemma norm_inverseSquareKernel_le (hR : 0<R)
    (A : Tail R →ᵇ (E →L[ℝ] F)) (t : Tail R) (u : ℝ) :
    ‖(-(t.val * (tailShift t u).val⁻¹^2)) • A (tailShift t u)‖ ≤
      t.val * ‖A‖ * (tailShift t u).val⁻¹^2 := by
  rw [norm_smul (-(t.val * (tailShift t u).val⁻¹^2)) (A (tailShift t u)),
    Real.norm_eq_abs,abs_neg,abs_of_nonneg
    (mul_nonneg (hR.trans_le t.property).le (sq_nonneg _))]
  calc
    _ ≤ (t.val * (tailShift t u).val⁻¹^2) * ‖A‖ :=
      mul_le_mul_of_nonneg_left (A.norm_coe_le_norm _) (mul_nonneg (hR.trans_le t.property).le (sq_nonneg _))
    _ = _ := by ring

/-- The weighted primitive operator has norm at most the coefficient norm.
It is `Z ↦ -t ∫ C01(s)Z(s)/s² ds`, in shifted tail coordinates. -/
def inverseSquareKernel (hR : 0<R) (A : Tail R →ᵇ (E →L[ℝ] F)) :
    ContinuousIntegralKernel (X:=Tail R) (E:=E) (F:=F)
      (volume.restrict (Ioi (0:ℝ))) ‖A‖ where
  kernel t u := (-(t.val * (tailShift t u).val⁻¹^2)) • A (tailShift t u)
  shift := tailShift
  continuous_kernel := (continuous_weight hR).neg.smul (A.continuous.comp continuous_tailShift)
  continuous_shift := continuous_tailShift
  bound t u := t.val * ‖A‖ * (tailShift t u).val⁻¹^2
  integrable_bound t := (integrable_tailShift_inv_sq hR t).const_mul _
  norm_le_bound t := Filter.Eventually.of_forall (norm_inverseSquareKernel_le hR A t)
  integral_bound_le t := by
    rw [integral_const_mul,integral_tailShift_inv_sq hR t]
    exact le_of_eq (by field_simp [(hR.trans_le t.property).ne'])
  locally_dominated t := by
    refine ⟨fun u => (t.val+1)*‖A‖*(R+u)⁻¹^2,
      (integrable_inv_shift_sq hR).const_mul _,?_⟩
    have ht : ∀ᶠ y : Tail R in 𝓝 t, y.val < t.val+1 :=
      (continuous_subtype_val.continuousAt.eventually (gt_mem_nhds (by linarith)))
    filter_upwards [ht] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0<u at hu
    apply (norm_inverseSquareKernel_le hR A y u).trans
    have hpos : 0<R+u := add_pos hR hu
    have hi : (tailShift y u).val⁻¹ ≤ (R+u)⁻¹ := by
      apply inv_anti₀ hpos
      simpa [tailShift,max_eq_right hu.le] using add_le_add_right y.property u
    have his : (tailShift y u).val⁻¹^2 ≤ (R+u)⁻¹^2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr (tailShift_pos hR y u).le) hi 2
    exact mul_le_mul (mul_le_mul_of_nonneg_right hy.le (norm_nonneg A)) his
      (sq_nonneg _) (mul_nonneg (by linarith [hR.trans_le t.property]) (norm_nonneg A))

/-- The exponentially decaying backward evolution, in shifted coordinates. -/
def exponentialTailKernel (hR : 0<R) {a C : ℝ} (ha : 0<a) (_hC : 0≤C)
    (V : Tail R → ℝ → E →L[ℝ] F)
    (hV : Continuous (Function.uncurry V))
    (hVbound : ∀ t u, 0<u → ‖V t u‖ ≤ C*Real.exp (-a*u)) :
    ContinuousIntegralKernel (X:=Tail R) (E:=E) (F:=F)
      (volume.restrict (Ioi (0:ℝ))) (C*R⁻¹*a⁻¹) where
  kernel t u := (-(t.val * (tailShift t u).val⁻¹^2)) • V t u
  shift := tailShift
  continuous_kernel := (continuous_weight hR).neg.smul hV
  continuous_shift := continuous_tailShift
  bound _ u := C*R⁻¹*Real.exp (-a*u)
  integrable_bound _ := (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).const_mul _
  norm_le_bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0<u at hu
    rw [norm_smul (-(t.val * (tailShift t u).val⁻¹^2)) (V t u),
      Real.norm_eq_abs,abs_neg,abs_of_nonneg
      (mul_nonneg (hR.trans_le t.property).le (sq_nonneg _))]
    calc
      _ ≤ R⁻¹ * (C*Real.exp (-a*u)) := mul_le_mul
        (tailShift_sq_ratio_le_inv hR t u) (hVbound t u hu) (norm_nonneg (V t u))
        (inv_nonneg.mpr hR.le)
      _ = _ := by ring
  integral_bound_le _ := by rw [integral_const_mul,integral_exp_decay ha]
  locally_dominated t := by
    refine ⟨fun u => C*R⁻¹*Real.exp (-a*u),
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).const_mul _,?_⟩
    apply Filter.Eventually.of_forall
    intro y
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0<u at hu
    rw [norm_smul (-(y.val * (tailShift y u).val⁻¹^2)) (V y u),
      Real.norm_eq_abs,abs_neg,abs_of_nonneg
      (mul_nonneg (hR.trans_le y.property).le (sq_nonneg _))]
    calc
      _ ≤ R⁻¹ * (C*Real.exp (-a*u)) := mul_le_mul
        (tailShift_sq_ratio_le_inv hR y u) (hVbound y u hu) (norm_nonneg (V y u))
        (inv_nonneg.mpr hR.le)
      _ = _ := by ring

/-- The inhomogeneous tail operator has one inverse power instead of two. -/
def exponentialForcingKernel (hR : 0<R) {a C : ℝ} (ha : 0<a) (_hC : 0≤C)
    (V : Tail R → ℝ → E →L[ℝ] F)
    (hV : Continuous (Function.uncurry V))
    (hVbound : ∀ t u, 0<u → ‖V t u‖ ≤ C*Real.exp (-a*u)) :
    ContinuousIntegralKernel (X:=Tail R) (E:=E) (F:=F)
      (volume.restrict (Ioi (0:ℝ))) (C*a⁻¹) where
  kernel t u := (-(t.val * (tailShift t u).val⁻¹)) • V t u
  shift := tailShift
  continuous_kernel := ((continuous_subtype_val.comp continuous_fst).mul
    ((continuous_subtype_val.comp continuous_tailShift).inv₀
      (fun p => (tailShift_pos hR p.1 p.2).ne'))).neg.smul hV
  continuous_shift := continuous_tailShift
  bound _ u := C*Real.exp (-a*u)
  integrable_bound _ := (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).const_mul _
  norm_le_bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0<u at hu
    rw [norm_smul (-(t.val * (tailShift t u).val⁻¹)) (V t u),
      Real.norm_eq_abs,abs_neg,abs_of_nonneg
      (mul_nonneg (hR.trans_le t.property).le (inv_nonneg.mpr (tailShift_pos hR t u).le))]
    exact (mul_le_mul (tailShift_ratio_le_one hR t u) (hVbound t u hu)
      (norm_nonneg (V t u)) zero_le_one).trans_eq (one_mul _)
  integral_bound_le _ := by rw [integral_const_mul,integral_exp_decay ha]
  locally_dominated t := by
    refine ⟨fun u => C*Real.exp (-a*u),
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).const_mul _,?_⟩
    apply Filter.Eventually.of_forall
    intro y
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0<u at hu
    rw [norm_smul (-(y.val * (tailShift y u).val⁻¹)) (V y u),
      Real.norm_eq_abs,abs_neg,abs_of_nonneg
      (mul_nonneg (hR.trans_le y.property).le (inv_nonneg.mpr (tailShift_pos hR y u).le))]
    exact (mul_le_mul (tailShift_ratio_le_one hR y u) (hVbound y u hu)
      (norm_nonneg (V y u)) zero_le_one).trans_eq (one_mul _)

end BourgadeHuang.CMS

