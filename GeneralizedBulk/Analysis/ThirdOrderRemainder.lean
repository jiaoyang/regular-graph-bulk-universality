import Mathlib

/-! A third-order Taylor estimate from actual derivative chains. -/
noncomputable section
open Set

namespace GeneralizedBulk.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Three applications of the mean-value inequality suffice after the first
two smoothing coefficients cancel. The deliberately coarse constant avoids
any choice of scalar Taylor remainder point. -/
theorem third_order_remainder (f f1 f2 f3 : ℝ → E) (a M : ℝ)
    (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hd : ∀ t ∈ Icc 0 a, HasDerivAt f (f1 t) t)
    (hd1 : ∀ t ∈ Icc 0 a, HasDerivAt f1 (f2 t) t)
    (hd2 : ∀ t ∈ Icc 0 a, HasDerivAt f2 (f3 t) t)
    (hbound : ∀ t ∈ Icc 0 a, ‖f3 t‖ ≤ M) (hzero1 : f1 0 = 0) (hzero2 : f2 0 = 0) :
    ‖f a - f 0‖ ≤ M * a ^ 3 := by
  have hb2 (t : ℝ) (ht : t ∈ Icc 0 a) : ‖f2 t‖ ≤ M * a := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht => (hd2 t ht).hasDerivWithinAt)
      (fun t ht => hbound t (Ico_subset_Icc_self ht)) t ht
    rw [hzero2, sub_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left ht.2 hM)
  have hb1 (t : ℝ) (ht : t ∈ Icc 0 a) : ‖f1 t‖ ≤ M * a * a := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht => (hd1 t ht).hasDerivWithinAt)
      (fun t ht => hb2 t (Ico_subset_Icc_self ht)) t ht
    rw [hzero1, sub_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hM ha))
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (fun t ht => hb1 t (Ico_subset_Icc_self ht)) a ⟨ha, le_rfl⟩
  simpa only [sub_zero, pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using h

end GeneralizedBulk.Analysis
