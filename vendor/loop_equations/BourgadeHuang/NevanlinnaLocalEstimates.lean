import BourgadeHuang.NevanlinnaInteraction

/-! Classical Nevanlinna estimates in terms of the value at the tested parameter,
not a fixed anchor. These are the input to the large-height local law. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem norm_reciprocal_sq_eq (a : ℝ) (z : ℂ) :
    ‖(((a:ℂ)-z)⁻¹)^2‖ = (Complex.normSq ((a:ℂ)-z))⁻¹ := by
  rw [norm_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_inv]

theorem integrable_poissonMass (s : AnchoredCountingState) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun a : ℝ => (Complex.normSq ((a:ℂ)-z))⁻¹) s.val.1.measure := by
  simpa only [norm_reciprocal_sq_eq] using (integrable_reciprocal_sq s hz).norm

theorem anchored_im_eq_poissonMass (s : AnchoredCountingState) {z : ℂ} (hz : z.im ≠ 0) :
    (anchoredNevanlinna s z).im = z.im * (anchoredLinearCoefficient s +
      ∫ a : ℝ, (Complex.normSq ((a:ℂ)-z))⁻¹ ∂s.val.1.measure) := by
  rw [anchoredNevanlinna_im_eq s hz]
  simp only [div_eq_mul_inv, integral_const_mul]
  ring

theorem poissonMass_le_im (s : AnchoredCountingState) {z : ℂ} (hz : z.im ≠ 0) :
    (∫ a : ℝ, (Complex.normSq ((a:ℂ)-z))⁻¹ ∂s.val.1.measure) ≤
      |(anchoredNevanlinna s z).im| / |z.im| := by
  have hM : 0 ≤ ∫ a : ℝ, (Complex.normSq ((a:ℂ)-z))⁻¹ ∂s.val.1.measure :=
    integral_nonneg (fun a => inv_nonneg.mpr (Complex.normSq_nonneg _))
  have hb := anchoredLinearCoefficient_nonneg s
  rw [anchored_im_eq_poissonMass s hz, abs_mul, abs_of_nonneg (add_nonneg hb hM)]
  field_simp
  nlinarith [abs_pos.mpr hz]

theorem norm_anchoredDerivative_le_im (s : AnchoredCountingState) {z : ℂ} (hz : z.im ≠ 0) :
    ‖anchoredDerivative s z‖ ≤ |(anchoredNevanlinna s z).im| / |z.im| := by
  have hM : 0 ≤ ∫ a : ℝ, (Complex.normSq ((a:ℂ)-z))⁻¹ ∂s.val.1.measure :=
    integral_nonneg (fun a => inv_nonneg.mpr (Complex.normSq_nonneg _))
  have hb := anchoredLinearCoefficient_nonneg s
  have he : |(anchoredNevanlinna s z).im| / |z.im| = anchoredLinearCoefficient s +
      ∫ a : ℝ, (Complex.normSq ((a:ℂ)-z))⁻¹ ∂s.val.1.measure := by
    rw [anchored_im_eq_poissonMass s hz, abs_mul, abs_of_nonneg (add_nonneg hb hM)]
    exact mul_div_cancel_left₀ _ (abs_ne_zero.mpr hz)
  rw [he, anchoredDerivative_eq_integral s hz]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · simp [Complex.norm_real, abs_of_nonneg hb]
  · calc
      _ ≤ ∫ a : ℝ, ‖(((a:ℂ)-z)⁻¹)^2‖ ∂s.val.1.measure :=
        norm_integral_le_integral_norm _
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun a => norm_reciprocal_sq_eq a z))

theorem norm_anchoredInteraction_le_im (s : AnchoredCountingState)
    {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    ‖anchoredInteraction s w v‖ ≤ |(anchoredNevanlinna s v).im| / (|w.im| * |v.im|) := by
  rw [anchoredInteraction_eq_integral s hw hv]
  calc
    _ ≤ ∫ a : ℝ, (1/|w.im|)*(Complex.normSq ((a:ℂ)-v))⁻¹ ∂s.val.1.measure := by
      apply norm_integral_le_of_norm_le ((integrable_poissonMass s hv).const_mul _)
      apply Filter.Eventually.of_forall
      intro a
      rw [norm_mul, ← norm_reciprocal_sq_eq a v]
      exact mul_le_mul_of_nonneg_right (norm_reciprocal_le_im a hw) (norm_nonneg _)
    _ = (1/|w.im|)*(∫ a : ℝ, (Complex.normSq ((a:ℂ)-v))⁻¹ ∂s.val.1.measure) := integral_const_mul _ _
    _ ≤ (1/|w.im|)*(|(anchoredNevanlinna s v).im|/|v.im|) :=
      mul_le_mul_of_nonneg_left (poissonMass_le_im s hv) (by positivity)
    _ = _ := by ring

theorem norm_anchoredInteraction_same_or_conj (s : AnchoredCountingState)
    {w v : ℂ} (hw : 0 < w.im) (hv : v = w ∨ v = starRingEnd ℂ w) :
    ‖anchoredInteraction s w v‖ ≤ ‖anchoredNevanlinna s w‖ / w.im^2 := by
  rcases hv with rfl | rfl
  · apply (norm_anchoredInteraction_le_im s hw.ne' hw.ne').trans
    simp only [abs_of_pos hw, pow_two]
    exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) (mul_nonneg hw.le hw.le)
  · have hvc : (starRingEnd ℂ w).im ≠ 0 := by simpa using neg_ne_zero.mpr hw.ne'
    apply (norm_anchoredInteraction_le_im s hw.ne' hvc).trans
    rw [anchoredNevanlinna_conj]
    simp only [Complex.conj_im, abs_neg, abs_of_pos hw, pow_two]
    exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) (mul_nonneg hw.le hw.le)

end BourgadeHuang
