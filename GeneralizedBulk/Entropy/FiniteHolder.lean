import GeneralizedBulk.Entropy.FiniteContinuity

/-! A dimension-logarithmic Hölder modulus for finite entropy. -/
noncomputable section
open scoped BigOperators

namespace GeneralizedBulk.Entropy.Finite

lemma negMulLog_le_one_sub (x : ℝ) (hx : 0 ≤ x) : Real.negMulLog x ≤ 1-x := by
  by_cases hx0 : x = 0
  · subst x; norm_num
  have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx')
  rw [Real.log_inv] at h
  have hm := mul_le_mul_of_nonneg_left h hx
  rw [mul_sub,mul_inv_cancel₀ hx0,mul_one] at hm
  unfold Real.negMulLog
  linarith

lemma negMulLog_le_two_sqrt (x : ℝ) (hx : 0 ≤ x) : Real.negMulLog x ≤ 2*Real.sqrt x := by
  have hy : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hs : (Real.sqrt x)^2 = x := Real.sq_sqrt hx
  have h := negMulLog_le_one_sub (Real.sqrt x) hy
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*Real.sqrt x by positivity)
  have hl : Real.log x = 2*Real.log (Real.sqrt x) := by
    calc
      _ = Real.log ((Real.sqrt x)^2) := congrArg Real.log hs.symm
      _ = _ := by rw [Real.log_pow]; norm_num
  unfold Real.negMulLog at h hm ⊢
  rw [hl]
  have he : -x*(2*Real.log (Real.sqrt x)) =
      2*Real.sqrt x*(-Real.sqrt x*Real.log (Real.sqrt x)) := by
    calc
      _ = -(Real.sqrt x)^2*(2*Real.log (Real.sqrt x)) := by rw [hs]
      _ = _ := by ring
  rw [he]
  nlinarith

lemma binEntropy_le_three_sqrt (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Real.binEntropy δ ≤ 3*Real.sqrt δ := by
  have h1 := negMulLog_le_two_sqrt δ hδ
  have h2 := negMulLog_le_one_sub (1-δ) (sub_nonneg.mpr hδ1)
  have h3 : δ ≤ Real.sqrt δ := Real.le_sqrt_of_sq_le (by nlinarith)
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  linarith

theorem entropy_holder {A : Type*} [Fintype A] (p q : A → ℝ)
    (hp : ∀ a,0 ≤ p a) (hq : ∀ a,0 ≤ q a) (hpsum : ∑ a,p a = 1) (hqsum : ∑ a,q a = 1) :
    |entropy p-entropy q| ≤
      (3+Real.log (Fintype.card A))*Real.sqrt (totalVariation p q) := by
  have hδ := totalVariation_nonneg p q
  have hδ1 := totalVariation_le_one p q hp hq hpsum hqsum
  have h := entropy_continuity p q hp hq hpsum hqsum
  have h1 := binEntropy_le_three_sqrt (totalVariation p q) hδ hδ1
  have h2 : totalVariation p q ≤ Real.sqrt (totalVariation p q) := Real.le_sqrt_of_sq_le (by nlinarith)
  have h3 := mul_le_mul_of_nonneg_right h2 (Real.log_natCast_nonneg (Fintype.card A))
  nlinarith

end GeneralizedBulk.Entropy.Finite
