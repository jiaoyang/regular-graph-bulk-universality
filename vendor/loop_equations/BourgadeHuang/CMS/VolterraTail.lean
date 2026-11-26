import BourgadeHuang.CMS.VolterraKernel

/-! Explicit half-line weights for the Volterra construction. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS

abbrev Tail (R : ℝ) := {t : ℝ // R ≤ t}

def tailShift {R : ℝ} (t : Tail R) (u : ℝ) : Tail R :=
  ⟨t.val + max 0 u, t.property.trans (le_add_of_nonneg_right (le_max_left _ _))⟩

lemma continuous_tailShift {R : ℝ} :
    Continuous (Function.uncurry (@tailShift R)) := by
  exact ((continuous_subtype_val.comp continuous_fst).add
    (continuous_const.max continuous_snd)).subtype_mk _

lemma tailShift_pos {R : ℝ} (hR : 0<R) (t : Tail R) (u : ℝ) :
    0 < (tailShift t u).val := hR.trans_le (tailShift t u).property

lemma integrable_inv_shift_sq {t : ℝ} (ht : 0<t) :
    IntegrableOn (fun u : ℝ => (t+u)⁻¹^2) (Ioi 0) := by
  have hd : ∀ u ∈ Ioi (0:ℝ), HasDerivAt (fun u : ℝ => -(t+u)⁻¹) ((t+u)⁻¹^2) u := by
    intro u hu
    change 0<u at hu
    convert ((hasDerivAt_id u).const_add t |>.inv (by dsimp; linarith)).neg using 1 <;>
      simp [div_eq_mul_inv, inv_pow]
  have hlim : Tendsto (fun u : ℝ => -(t+u)⁻¹) atTop (𝓝 0) := by
    simpa only [neg_zero] using (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_left atTop t tendsto_id)).neg
  apply integrableOn_Ioi_deriv_of_nonneg _ hd (fun _ _=>sq_nonneg _) hlim
  exact (((hasDerivAt_id (0:ℝ)).const_add t).inv (by simpa using ht.ne')).neg.continuousAt.continuousWithinAt

lemma integral_inv_shift_sq {t : ℝ} (ht : 0<t) :
    (∫ u : ℝ in Ioi 0, (t+u)⁻¹^2) = t⁻¹ := by
  have hd : ∀ u ∈ Ioi (0:ℝ), HasDerivAt (fun u : ℝ => -(t+u)⁻¹) ((t+u)⁻¹^2) u := by
    intro u hu
    change 0<u at hu
    convert ((hasDerivAt_id u).const_add t |>.inv (by dsimp; linarith)).neg using 1 <;>
      simp [div_eq_mul_inv, inv_pow]
  have hlim : Tendsto (fun u : ℝ => -(t+u)⁻¹) atTop (𝓝 0) := by
    simpa only [neg_zero] using (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_left atTop t tendsto_id)).neg
  have hc : ContinuousWithinAt (fun u : ℝ => -(t+u)⁻¹) (Ici 0) 0 :=
    (((hasDerivAt_id (0:ℝ)).const_add t).inv (by simpa using ht.ne')).neg.continuousAt.continuousWithinAt
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto hc hd (integrable_inv_shift_sq ht) hlim

lemma integrable_tailShift_inv_sq {R : ℝ} (hR : 0<R) (t : Tail R) :
    IntegrableOn (fun u => (tailShift t u).val⁻¹^2) (Ioi 0) := by
  apply (integrable_inv_shift_sq (hR.trans_le t.property)).congr_fun _ measurableSet_Ioi
  intro u hu
  change 0<u at hu
  simp [tailShift,max_eq_right hu.le]

lemma integral_tailShift_inv_sq {R : ℝ} (hR : 0<R) (t : Tail R) :
    (∫ u : ℝ in Ioi 0, (tailShift t u).val⁻¹^2) = t.val⁻¹ := by
  rw [← integral_inv_shift_sq (hR.trans_le t.property)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change 0<u at hu
  simp [tailShift,max_eq_right hu.le]

lemma integral_exp_decay {a : ℝ} (ha : 0<a) :
    (∫ u : ℝ in Ioi 0, Real.exp (-a*u)) = a⁻¹ := by
  simpa using integral_exp_mul_Ioi (a:=-a) (neg_neg_of_pos ha) 0

lemma tailShift_ratio_le_one {R : ℝ} (hR : 0<R) (t : Tail R) (u : ℝ) :
    t.val * (tailShift t u).val⁻¹ ≤ 1 := by
  rw [← div_eq_mul_inv,div_le_one (tailShift_pos hR t u)]
  exact le_add_of_nonneg_right (le_max_left _ _)

lemma tailShift_sq_ratio_le_inv {R : ℝ} (hR : 0<R) (t : Tail R) (u : ℝ) :
    t.val * (tailShift t u).val⁻¹^2 ≤ R⁻¹ := by
  calc
    _ = (t.val * (tailShift t u).val⁻¹) * (tailShift t u).val⁻¹ := by ring
    _ ≤ 1 * (tailShift t u).val⁻¹ := mul_le_mul_of_nonneg_right
      (tailShift_ratio_le_one hR t u) (inv_nonneg.mpr (tailShift_pos hR t u).le)
    _ ≤ R⁻¹ := by simpa using inv_anti₀ hR (tailShift t u).property

end BourgadeHuang.CMS
