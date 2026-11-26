import BourgadeHuang.BulkLocalLaw
import BourgadeHuang.RationalEdge.PolynomialTests

/-! The derivative term of the general-beta hierarchy is retained and
absorbed explicitly in the quadratic-moment estimate. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgadeHuang.RationalEdge

/-- The centered algebraic equation at the edge. -/
def edgeQuadratic (s : AnchoredCountingState) (w : ℂ) : ℂ :=
  anchoredNevanlinna s w ^ 2 - w

theorem continuous_edgeQuadratic {w : ℂ} (hw : w.im ≠ 0) :
    Continuous (fun s => edgeQuadratic s w) :=
  ((continuous_anchoredNevanlinna hw).pow 2).sub continuous_const

theorem anchoredGrowth_edgeQuadratic {w : ℂ} (hw : w.im ≠ 0) :
    AnchoredGrowth (fun s => edgeQuadratic s w) 2 :=
  ((anchoredGrowth_nevanlinna hw).pow 2).sub
    ((AnchoredGrowth.const w).mono (by omega))

private def quadraticTest (i : Fin 2) (c : ℂ) : LoopTest 2 :=
  .add (.mulVar i (.mulVar i (.const 1))) (.const (-c))

private lemma eval_quadraticTest (i : Fin 2) (c : ℂ) (X : Fin 2 → ℂ) :
    (quadraticTest i c).eval X = X i^2-c := by
  simp only [quadraticTest,LoopTest.eval]
  ring

private lemma directional_quadraticTest (i : Fin 2) (c : ℂ) (X J : Fin 2 → ℂ) :
    (quadraticTest i c).directional X J = 2*X i*J i := by
  simp only [quadraticTest,LoopTest.eval,LoopTest.directional]
  ring

def edgeQuadraticRemainder (s : AnchoredCountingState) (w : ℂ) (n : ℕ) : ℂ :=
  (2*(n:ℂ))*anchoredNevanlinna s w*anchoredInteraction s w w * edgeQuadratic s w^(n-1) *
    (starRingEnd ℂ (edgeQuadratic s w))^(n+1) +
  (2*((n:ℂ)+1))*(starRingEnd ℂ (anchoredNevanlinna s w))*anchoredInteraction s w (starRingEnd ℂ w) *
    edgeQuadratic s w^n * (starRingEnd ℂ (edgeQuadratic s w))^n

theorem norm_edgeQuadraticRemainder_le (s : AnchoredCountingState)
    {w : ℂ} (hw : 0<w.im) (n : ℕ) :
    ‖edgeQuadraticRemainder s w n‖ ≤
      (4*((n:ℝ)+1)/w.im^2) * ‖anchoredNevanlinna s w‖^2 * ‖edgeQuadratic s w‖^(2*n) := by
  let A := ‖anchoredNevanlinna s w‖
  let B := ‖edgeQuadratic s w‖
  have hi := norm_anchoredInteraction_same_or_conj s hw (Or.inl rfl)
  have hj := norm_anchoredInteraction_same_or_conj s hw (Or.inr rfl)
  have hh : ‖edgeQuadraticRemainder s w n‖ ≤
      (2*(n:ℝ))*A*(A/w.im^2)*B^(n-1)*B^(n+1) +
      (2*((n:ℝ)+1))*A*(A/w.im^2)*B^n*B^n := by
    apply (norm_add_le _ _).trans
    simp only [edgeQuadraticRemainder, norm_mul, norm_pow, Complex.norm_conj,
      Complex.norm_natCast]
    have hn : ‖(n:ℂ)+1‖ = (n:ℝ)+1 := by
      rw [← Nat.cast_one, ← Nat.cast_add, Complex.norm_natCast, Nat.cast_add, Nat.cast_one]
    rw [hn]
    norm_num only [Complex.norm_ofNat]
    apply add_le_add
    · gcongr
    · gcongr
  have hp : (n:ℝ)*B^(n-1)*B^(n+1) = (n:ℝ)*B^(2*n) := by
    cases n with
    | zero => simp
    | succ k =>
      rw [mul_assoc, ← pow_add]
      congr 2 <;> omega
  have hpow : B^n*B^n=B^(2*n) := by rw [← pow_add]; congr 1; omega
  have heq : (2*(n:ℝ))*A*(A/w.im^2)*B^(n-1)*B^(n+1) +
      (2*((n:ℝ)+1))*A*(A/w.im^2)*B^n*B^n =
      ((4*(n:ℝ)+2)/w.im^2)*A^2*B^(2*n) := by
    calc
      _ = (2*A*(A/w.im^2))*((n:ℝ)*B^(n-1)*B^(n+1)) +
          (2*((n:ℝ)+1))*A*(A/w.im^2)*(B^n*B^n) := by ring
      _ = _ := by rw [hp,hpow]; ring
  apply hh.trans
  rw [heq]
  dsimp [A,B]
  gcongr
  linarith

def quadraticRemainder (β : ℝ) (s : AnchoredCountingState) (w : ℂ) (n : ℕ) : ℂ :=
  ((2-(β:ℂ))/(β:ℂ))*anchoredDerivative s w * edgeQuadratic s w^n *
    (starRingEnd ℂ (edgeQuadratic s w))^(n+1) + (2/(β:ℂ))*edgeQuadraticRemainder s w n

/-- The general-beta high quadratic test is an actual consequence of the mixed-word
hierarchy, including its single-derivative term and interaction coefficient 2 / beta. -/
theorem exactHierarchy_edgeQuadratic_test
    (ν : Measure AnchoredCountingState) (β : ℝ) (hh : ExactHierarchy ν β)
    {w : ℂ} (hw : w.im ≠ 0) (n : ℕ) :
    Integrable (fun s => edgeQuadratic s w^(n+1)*(starRingEnd ℂ (edgeQuadratic s w))^(n+1)+
      quadraticRemainder β s w n) ν ∧
    (∫ s,edgeQuadratic s w^(n+1)*(starRingEnd ℂ (edgeQuadratic s w))^(n+1)+
      quadraticRemainder β s w n ∂ν)=0 := by
  let v : Fin 2 → ℂ := ![w,starRingEnd ℂ w]
  have hv : ∀ i,(v i).im ≠ 0 := by
    intro i
    fin_cases i <;> simp [v,hw]
  let P := ((quadraticTest 0 w).pow n).mul
    ((quadraticTest 1 (starRingEnd ℂ w)).pow (n+1))
  have h := exactHierarchy_polynomial_test ν β hh hw hv P
  have heq (s : AnchoredCountingState) :
      loopHead β s w * P.eval (fun i => anchoredNevanlinna s (v i)) +
      P.directional (fun i => anchoredNevanlinna s (v i))
        (fun i => (2/(β:ℂ))*anchoredInteraction s w (v i)) =
      edgeQuadratic s w^(n+1)*(starRingEnd ℂ (edgeQuadratic s w))^(n+1)+
        quadraticRemainder β s w n := by
    simp only [P,LoopTest.eval_mul,LoopTest.directional_mul,LoopTest.eval_pow,LoopTest.directional_pow,
      eval_quadraticTest,directional_quadraticTest,v,
      Matrix.cons_val_zero,Matrix.cons_val_one,anchoredNevanlinna_conj,
      loopHead,edgeQuadratic,quadraticRemainder,edgeQuadraticRemainder,
      map_sub,map_pow,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
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
lemma norm_quadraticRemainder_le (β : ℝ) (s : AnchoredCountingState)
    {w : ℂ} (hw : 0<w.im) (n : ℕ) :
    ‖quadraticRemainder β s w n‖ ≤
      ‖edgeQuadratic s w‖^(2*(n+1))/4 +
      ((4*coefficientBound β*((n:ℝ)+1)+(coefficientBound β)^2)/w.im^2)*
        ‖anchoredNevanlinna s w‖^2*‖edgeQuadratic s w‖^(2*n) := by
  let A := ‖anchoredNevanlinna s w‖
  let B := ‖edgeQuadratic s w‖
  let K := coefficientBound β
  have hK : 0 ≤ K := (coefficientBound_pos β).le
  have hd := norm_anchoredDerivative_le_norm_div_im s hw
  have hR := norm_edgeQuadraticRemainder_le s hw n
  have hder : ‖((2-(β:ℂ))/(β:ℂ))*anchoredDerivative s w*edgeQuadratic s w^n*
      (starRingEnd ℂ (edgeQuadratic s w))^(n+1)‖ ≤ (K*A/w.im)*B^n*B^(n+1) := by
    simp only [norm_mul,norm_pow,Complex.norm_conj]
    have hc := first_coefficient_le β
    have hmul := mul_le_mul hc hd (norm_nonneg _) hK
    calc
      _ ≤ (K*(A/w.im))*B^n*B^(n+1) := by gcongr
      _ = _ := by ring
  have hy : (K*A/w.im)*B^n*B^(n+1) ≤ B^(2*(n+1))/4 + K^2*A^2/w.im^2*B^(2*n) := by
    have hs := sq_nonneg (B^(n+1)/2-(K*A/w.im)*B^n)
    have hp : (B^(n+1))^2 = B^(2*(n+1)) := by rw [← pow_mul]; congr 1; omega
    have hp' : (B^n)^2 = B^(2*n) := by rw [← pow_mul]; congr 1; omega
    simp only [sub_sq,mul_pow,div_pow,hp,hp'] at hs
    nlinarith
  calc
    _ ≤ ‖((2-(β:ℂ))/(β:ℂ))*anchoredDerivative s w*edgeQuadratic s w^n*
        (starRingEnd ℂ (edgeQuadratic s w))^(n+1)‖+‖(2/(β:ℂ))*edgeQuadraticRemainder s w n‖ := norm_add_le _ _
    _ ≤ B^(2*(n+1))/4+K^2*A^2/w.im^2*B^(2*n)+
        K*((4*((n:ℝ)+1)/w.im^2)*A^2*B^(2*n)) := by
      rw [norm_mul (2/(β:ℂ))]
      exact add_le_add (hder.trans hy) (mul_le_mul (second_coefficient_le β) hR (norm_nonneg _) hK)
    _ = _ := by dsimp [A,B,K]; ring

def localLawConstant (β : ℝ) : ℝ := 2*(4*coefficientBound β+(coefficientBound β)^2+1)

theorem localLawConstant_pos (β : ℝ) : 0 < localLawConstant β := by
  unfold localLawConstant
  have := (coefficientBound_pos β).le
  positivity

/-- The general-beta derivative is absorbed without weakening the height exponent. -/
theorem integral_edgeQuadratic_even_le_mixed
    (ν : Measure AnchoredCountingState) (β : ℝ) (hh : ExactHierarchy ν β)
    {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w : ℂ} (hw : 0<w.im) (n : ℕ) :
    (∫ s,‖edgeQuadratic s w‖^(2*(n+1)) ∂ν) ≤
      (localLawConstant β*((n:ℝ)+1)/w.im^2) *
        ∫ s,‖anchoredNevanlinna s w‖^2*‖edgeQuadratic s w‖^(2*n) ∂ν := by
  have hQr := integrable_norm_pow_of_anchoredGrowth ν ha he
    (continuous_edgeQuadratic hw.ne') (anchoredGrowth_edgeQuadratic hw.ne') (2*(n+1))
  have hQc : Integrable (fun s : AnchoredCountingState => ((‖edgeQuadratic s w‖^(2*(n+1)):ℝ):ℂ)) ν :=
    hQr.ofReal
  have hmixed : Integrable (fun s => ‖anchoredNevanlinna s w‖^2*‖edgeQuadratic s w‖^(2*n)) ν := by
    simpa only [norm_mul,norm_pow] using (integrable_of_anchoredGrowth ν ha he
      (((continuous_anchoredNevanlinna hw.ne').pow 2).mul ((continuous_edgeQuadratic hw.ne').pow (2*n)))
      (((anchoredGrowth_nevanlinna hw.ne').pow 2).mul ((anchoredGrowth_edgeQuadratic hw.ne').pow (2*n)))).norm
  have h := exactHierarchy_edgeQuadratic_test ν β hh hw.ne' n
  simp_rw [quadratic_conj_power] at h
  have hRi : Integrable (fun s => quadraticRemainder β s w n) ν := by
    convert h.1.sub hQc using 1
    ext s
    exact (add_sub_cancel_left _ _).symm
  have hzero := h.2
  rw [integral_add hQc hRi,integral_complex_ofReal] at hzero
  have hnorm : (∫ s,‖edgeQuadratic s w‖^(2*(n+1)) ∂ν) =
      ‖∫ s,quadraticRemainder β s w n ∂ν‖ := by
    have hh : (∫ s,quadraticRemainder β s w n ∂ν) =
        -(∫ s,‖edgeQuadratic s w‖^(2*(n+1)) ∂ν : ℝ) := by linear_combination hzero
    rw [hh,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    exact integral_nonneg (fun s => by positivity)
  have hi : Integrable (fun s => ‖edgeQuadratic s w‖^(2*(n+1))/4+
      ((4*coefficientBound β*((n:ℝ)+1)+(coefficientBound β)^2)/w.im^2)*‖anchoredNevanlinna s w‖^2*‖edgeQuadratic s w‖^(2*n)) ν := by
    simpa only [mul_assoc] using (hQr.div_const 4).add
      (hmixed.const_mul ((4*coefficientBound β*((n:ℝ)+1)+(coefficientBound β)^2)/w.im^2))
  have hb : (∫ s,‖edgeQuadratic s w‖^(2*(n+1)) ∂ν) ≤
      (∫ s,‖edgeQuadratic s w‖^(2*(n+1)) ∂ν)/4+
      ((4*coefficientBound β*((n:ℝ)+1)+(coefficientBound β)^2)/w.im^2)*
        (∫ s,‖anchoredNevanlinna s w‖^2*‖edgeQuadratic s w‖^(2*n) ∂ν) := by
    calc
      _ = ‖∫ s,quadraticRemainder β s w n ∂ν‖ := hnorm
      _ ≤ ∫ s,‖quadraticRemainder β s w n‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ s,‖edgeQuadratic s w‖^(2*(n+1))/4+
          ((4*coefficientBound β*((n:ℝ)+1)+(coefficientBound β)^2)/w.im^2)*‖anchoredNevanlinna s w‖^2*‖edgeQuadratic s w‖^(2*n) ∂ν :=
        integral_mono hRi.norm hi (fun s => norm_quadraticRemainder_le β s hw n)
      _ = _ := by
        simp only [mul_assoc]
        rw [integral_add (hQr.div_const 4) (hmixed.const_mul _),integral_div,integral_const_mul]
  have hc : (4*coefficientBound β*((n:ℝ)+1)+(coefficientBound β)^2)/w.im^2 ≤
      ((4*coefficientBound β+(coefficientBound β)^2+1)*((n:ℝ)+1))/w.im^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith [Nat.cast_nonneg (α := ℝ) n,
      mul_nonneg (sq_nonneg (coefficientBound β)) (Nat.cast_nonneg (α := ℝ) n)]
  have hprod := mul_le_mul_of_nonneg_right hc
    (integral_nonneg (μ := ν) (fun s : AnchoredCountingState =>
      mul_nonneg (sq_nonneg ‖anchoredNevanlinna s w‖) (pow_nonneg (norm_nonneg (edgeQuadratic s w)) (2*n))))
  have hnonneg : 0 ≤ ∫ s,‖edgeQuadratic s w‖^(2*(n+1)) ∂ν := integral_nonneg (fun s => by positivity)
  dsimp [localLawConstant]
  have heq : (2*(4*coefficientBound β+(coefficientBound β)^2+1)*((n:ℝ)+1)/w.im^2) =
      2*((4*coefficientBound β+(coefficientBound β)^2+1)*((n:ℝ)+1)/w.im^2) := by ring
  rw [heq]
  linarith

end BourgadeHuang.RationalEdge
