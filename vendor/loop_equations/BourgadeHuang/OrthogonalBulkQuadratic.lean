import BourgadeHuang.BulkLocalLaw

/-! The additional derivative term of the β = 1 hierarchy is retained and
absorbed explicitly in the quadratic-moment estimate. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgadeHuang

private def orthogonalQuadraticTest (i : Fin 2) : LoopTest 2 :=
  .add (.mulVar i (.mulVar i (.const 1))) (.const 1)

private lemma eval_orthogonalQuadraticTest (i : Fin 2) (X : Fin 2 → ℂ) :
    (orthogonalQuadraticTest i).eval X = X i^2+1 := by
  simp only [orthogonalQuadraticTest,LoopTest.eval]
  ring

private lemma directional_orthogonalQuadraticTest (i : Fin 2) (X J : Fin 2 → ℂ) :
    (orthogonalQuadraticTest i).directional X J = 2*X i*J i := by
  simp only [orthogonalQuadraticTest,LoopTest.eval,LoopTest.directional]
  ring

def orthogonalQuadraticRemainder (s : AnchoredCountingState) (w : ℂ) (n : ℕ) : ℂ :=
  anchoredDerivative s w * bulkQuadratic s w^n *
    (starRingEnd ℂ (bulkQuadratic s w))^(n+1) + 2*bulkQuadraticRemainder s w n

/-- The β = 1 high quadratic test is an actual consequence of the mixed-word
hierarchy, including its single-derivative term and interaction coefficient 2. -/
theorem exactHierarchy_orthogonalBulkQuadratic_test
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .one)
    {w : ℂ} (hw : w.im ≠ 0) (n : ℕ) :
    Integrable (fun s => bulkQuadratic s w^(n+1)*(starRingEnd ℂ (bulkQuadratic s w))^(n+1)+
      orthogonalQuadraticRemainder s w n) ν ∧
    (∫ s,bulkQuadratic s w^(n+1)*(starRingEnd ℂ (bulkQuadratic s w))^(n+1)+
      orthogonalQuadraticRemainder s w n ∂ν)=0 := by
  let v : Fin 2 → ℂ := ![w,starRingEnd ℂ w]
  have hv : ∀ i,(v i).im ≠ 0 := by
    intro i
    fin_cases i <;> simp [v,hw]
  let P := ((orthogonalQuadraticTest 0).pow n).mul ((orthogonalQuadraticTest 1).pow (n+1))
  have h := exactHierarchy_polynomial_test ν .one hh hw hv P
  have heq (s : AnchoredCountingState) :
      anchoredLoopHead .one s w * P.eval (fun i => anchoredNevanlinna s (v i)) +
      P.directional (fun i => anchoredNevanlinna s (v i))
        (fun i => (2/Beta.value .one)*anchoredInteraction s w (v i)) =
      bulkQuadratic s w^(n+1)*(starRingEnd ℂ (bulkQuadratic s w))^(n+1)+
        orthogonalQuadraticRemainder s w n := by
    simp only [P,LoopTest.eval_mul,LoopTest.directional_mul,LoopTest.eval_pow,LoopTest.directional_pow,
      eval_orthogonalQuadraticTest,directional_orthogonalQuadraticTest,v,
      Matrix.cons_val_zero,Matrix.cons_val_one,anchoredNevanlinna_conj,
      anchoredLoopHead,Beta.value,bulkQuadratic,orthogonalQuadraticRemainder,bulkQuadraticRemainder,
      map_add,map_pow,map_one,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
    norm_num
    ring
  simpa only [heq] using h

lemma norm_anchoredDerivative_le_norm_div_im (s : AnchoredCountingState)
    {w : ℂ} (hw : 0<w.im) : ‖anchoredDerivative s w‖ ≤ ‖anchoredNevanlinna s w‖/w.im := by
  apply (norm_anchoredDerivative_le_im s hw.ne').trans
  rw [abs_of_pos hw]
  exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) hw.le

/-- A pointwise square inequality absorbs one quarter of the leading moment;
the remaining contribution has the same height scaling as the interactions. -/
lemma norm_orthogonalQuadraticRemainder_le (s : AnchoredCountingState)
    {w : ℂ} (hw : 0<w.im) (n : ℕ) :
    ‖orthogonalQuadraticRemainder s w n‖ ≤
      ‖bulkQuadratic s w‖^(2*(n+1))/4 +
      ((8*((n:ℝ)+1)+1)/w.im^2)*‖anchoredNevanlinna s w‖^2*‖bulkQuadratic s w‖^(2*n) := by
  let A := ‖anchoredNevanlinna s w‖
  let B := ‖bulkQuadratic s w‖
  have hd := norm_anchoredDerivative_le_norm_div_im s hw
  have hR := norm_bulkQuadraticRemainder_le s hw n
  have hder : ‖anchoredDerivative s w*bulkQuadratic s w^n*
      (starRingEnd ℂ (bulkQuadratic s w))^(n+1)‖ ≤ (A/w.im)*B^n*B^(n+1) := by
    simp only [norm_mul,norm_pow,Complex.norm_conj]
    gcongr
  have hy : (A/w.im)*B^n*B^(n+1) ≤ B^(2*(n+1))/4 + A^2/w.im^2*B^(2*n) := by
    have hs := sq_nonneg (B^(n+1)/2-(A/w.im)*B^n)
    have hp : (B^(n+1))^2 = B^(2*(n+1)) := by rw [← pow_mul]; congr 1; omega
    have hp' : (B^n)^2 = B^(2*n) := by rw [← pow_mul]; congr 1; omega
    simp only [sub_sq,mul_pow,div_pow,hp,hp'] at hs
    nlinarith
  calc
    _ ≤ ‖anchoredDerivative s w*bulkQuadratic s w^n*
        (starRingEnd ℂ (bulkQuadratic s w))^(n+1)‖+‖2*bulkQuadraticRemainder s w n‖ := norm_add_le _ _
    _ ≤ B^(2*(n+1))/4+A^2/w.im^2*B^(2*n)+
        2*((4*((n:ℝ)+1)/w.im^2)*A^2*B^(2*n)) := by
      rw [norm_mul (2:ℂ),show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
      exact add_le_add (hder.trans hy) (mul_le_mul_of_nonneg_left hR (by norm_num))
    _ = _ := by dsimp [A,B]; ring

/-- The β = 1 derivative is absorbed without weakening the height exponent. -/
theorem integral_orthogonalBulkQuadratic_even_le_mixed
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .one)
    {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w : ℂ} (hw : 0<w.im) (n : ℕ) :
    (∫ s,‖bulkQuadratic s w‖^(2*(n+1)) ∂ν) ≤
      (12*((n:ℝ)+1)/w.im^2) *
        ∫ s,‖anchoredNevanlinna s w‖^2*‖bulkQuadratic s w‖^(2*n) ∂ν := by
  have hQr := integrable_norm_pow_of_anchoredGrowth ν ha he
    (continuous_bulkQuadratic hw.ne') (anchoredGrowth_bulkQuadratic hw.ne') (2*(n+1))
  have hQc : Integrable (fun s : AnchoredCountingState => ((‖bulkQuadratic s w‖^(2*(n+1)):ℝ):ℂ)) ν :=
    hQr.ofReal
  have hmixed : Integrable (fun s => ‖anchoredNevanlinna s w‖^2*‖bulkQuadratic s w‖^(2*n)) ν := by
    simpa only [norm_mul,norm_pow] using (integrable_of_anchoredGrowth ν ha he
      (((continuous_anchoredNevanlinna hw.ne').pow 2).mul ((continuous_bulkQuadratic hw.ne').pow (2*n)))
      (((anchoredGrowth_nevanlinna hw.ne').pow 2).mul ((anchoredGrowth_bulkQuadratic hw.ne').pow (2*n)))).norm
  have h := exactHierarchy_orthogonalBulkQuadratic_test ν hh hw.ne' n
  simp_rw [quadratic_conj_power] at h
  have hRi : Integrable (fun s => orthogonalQuadraticRemainder s w n) ν := by
    convert h.1.sub hQc using 1
    ext s
    exact (add_sub_cancel_left _ _).symm
  have hzero := h.2
  rw [integral_add hQc hRi,integral_complex_ofReal] at hzero
  have hnorm : (∫ s,‖bulkQuadratic s w‖^(2*(n+1)) ∂ν) =
      ‖∫ s,orthogonalQuadraticRemainder s w n ∂ν‖ := by
    have hh : (∫ s,orthogonalQuadraticRemainder s w n ∂ν) =
        -(∫ s,‖bulkQuadratic s w‖^(2*(n+1)) ∂ν : ℝ) := by linear_combination hzero
    rw [hh,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    exact integral_nonneg (fun s => by positivity)
  have hi : Integrable (fun s => ‖bulkQuadratic s w‖^(2*(n+1))/4+
      ((8*((n:ℝ)+1)+1)/w.im^2)*‖anchoredNevanlinna s w‖^2*‖bulkQuadratic s w‖^(2*n)) ν := by
    simpa only [mul_assoc] using (hQr.div_const 4).add
      (hmixed.const_mul ((8*((n:ℝ)+1)+1)/w.im^2))
  have hb : (∫ s,‖bulkQuadratic s w‖^(2*(n+1)) ∂ν) ≤
      (∫ s,‖bulkQuadratic s w‖^(2*(n+1)) ∂ν)/4+
      ((8*((n:ℝ)+1)+1)/w.im^2)*
        (∫ s,‖anchoredNevanlinna s w‖^2*‖bulkQuadratic s w‖^(2*n) ∂ν) := by
    calc
      _ = ‖∫ s,orthogonalQuadraticRemainder s w n ∂ν‖ := hnorm
      _ ≤ ∫ s,‖orthogonalQuadraticRemainder s w n‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ s,‖bulkQuadratic s w‖^(2*(n+1))/4+
          ((8*((n:ℝ)+1)+1)/w.im^2)*‖anchoredNevanlinna s w‖^2*‖bulkQuadratic s w‖^(2*n) ∂ν :=
        integral_mono hRi.norm hi (fun s => norm_orthogonalQuadraticRemainder_le s hw n)
      _ = _ := by
        simp only [mul_assoc]
        rw [integral_add (hQr.div_const 4) (hmixed.const_mul _),integral_div,integral_const_mul]
  have hc : (8*((n:ℝ)+1)+1)/w.im^2 ≤ 9*((n:ℝ)+1)/w.im^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hprod := mul_le_mul_of_nonneg_right hc
    (integral_nonneg (μ := ν) (fun s : AnchoredCountingState =>
      mul_nonneg (sq_nonneg ‖anchoredNevanlinna s w‖) (pow_nonneg (norm_nonneg (bulkQuadratic s w)) (2*n))))
  have heq : (12*((n:ℝ)+1)/w.im^2) = (4/3:ℝ)*(9*((n:ℝ)+1)/w.im^2) := by ring
  rw [heq]
  linarith

end BourgadeHuang
