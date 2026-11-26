import BourgadeHuang.PolynomialLoopTests
import BourgadeHuang.LocalLawAlgebra

/-! The genuine quadratic-moment identities behind the bulk local law. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgadeHuang

namespace AnchoredGrowth

theorem pow {F : AnchoredCountingState → ℂ} {d : ℕ}
    (hF : AnchoredGrowth F d) (n : ℕ) : AnchoredGrowth (fun s => F s ^ n) (d*n) := by
  induction n with
  | zero => simpa using const 1
  | succ n ih => simpa [pow_succ, Nat.mul_add] using ih.mul hF

end AnchoredGrowth

theorem integrable_of_anchoredGrowth
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {F : AnchoredCountingState → ℂ} (hF : Continuous F) {d : ℕ} (hg : AnchoredGrowth F d) :
    Integrable F ν := by
  obtain ⟨C,hC,hb⟩ := hg
  have hi : Integrable (fun s : AnchoredCountingState => C*(1+‖s.val.2‖)^d) ν := by
    simpa only [zero_mul,Real.exp_zero,mul_one] using integrable_anchor_polynomial_exp ν ha he hC d 0
  exact hi.mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall hb)

theorem integrable_norm_pow_of_anchoredGrowth
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {F : AnchoredCountingState → ℂ} (hF : Continuous F) {d : ℕ} (hg : AnchoredGrowth F d) (n : ℕ) :
    Integrable (fun s => ‖F s‖^n) ν := by
  simpa only [norm_pow] using (integrable_of_anchoredGrowth ν ha he (hF.pow n) (hg.pow n)).norm

def bulkQuadratic (s : AnchoredCountingState) (w : ℂ) : ℂ := anchoredNevanlinna s w ^ 2 + 1

theorem continuous_bulkQuadratic {w : ℂ} (hw : w.im ≠ 0) :
    Continuous (fun s => bulkQuadratic s w) :=
  ((continuous_anchoredNevanlinna hw).pow 2).add continuous_const

theorem anchoredGrowth_bulkQuadratic {w : ℂ} (hw : w.im ≠ 0) :
    AnchoredGrowth (fun s => bulkQuadratic s w) 2 :=
  ((anchoredGrowth_nevanlinna hw).pow 2).add ((AnchoredGrowth.const 1).mono (by omega))

private def quadraticTest (i : Fin 2) : LoopTest 2 :=
  .add (.mulVar i (.mulVar i (.const 1))) (.const 1)

private theorem eval_quadraticTest (i : Fin 2) (X : Fin 2 → ℂ) :
    (quadraticTest i).eval X = X i ^ 2 + 1 := by
  simp only [quadraticTest,LoopTest.eval]; ring

private theorem directional_quadraticTest (i : Fin 2) (X J : Fin 2 → ℂ) :
    (quadraticTest i).directional X J = 2 * X i * J i := by
  simp only [quadraticTest,LoopTest.eval,LoopTest.directional]; ring

/-- Exact all-order quadratic test, with no moment or PDE identity assumed.
The power `n=0` includes the basic second-moment local-law identity. -/
theorem exactHierarchy_bulkQuadratic_test
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .two)
    {w : ℂ} (hw : w.im ≠ 0) (n : ℕ) :
    let S := fun s : AnchoredCountingState => anchoredNevanlinna s w
    let Q := fun s : AnchoredCountingState => bulkQuadratic s w
    let R := fun s : AnchoredCountingState =>
      (2*(n:ℂ))*S s*anchoredInteraction s w w * Q s^(n-1) * (starRingEnd ℂ (Q s))^(n+1) +
      (2*((n:ℂ)+1))*(starRingEnd ℂ (S s))*anchoredInteraction s w (starRingEnd ℂ w) *
        Q s^n * (starRingEnd ℂ (Q s))^n
    Integrable (fun s => Q s^(n+1)*(starRingEnd ℂ (Q s))^(n+1)+R s) ν ∧
      (∫ s, Q s^(n+1)*(starRingEnd ℂ (Q s))^(n+1)+R s ∂ν)=0 := by
  let v : Fin 2 → ℂ := ![w,starRingEnd ℂ w]
  have hv : ∀ i, (v i).im ≠ 0 := by
    intro i
    fin_cases i <;> simp [v, hw]
  let P := ((quadraticTest 0).pow n).mul ((quadraticTest 1).pow (n+1))
  have h := exactHierarchy_polynomial_test ν .two hh hw hv P
  have heq (s : AnchoredCountingState) :
      anchoredLoopHead .two s w *
          P.eval (fun i => anchoredNevanlinna s (v i)) +
        P.directional (fun i => anchoredNevanlinna s (v i))
          (fun i => (2/Beta.value .two)*anchoredInteraction s w (v i)) =
      bulkQuadratic s w^(n+1)*(starRingEnd ℂ (bulkQuadratic s w))^(n+1) +
      ((2*(n:ℂ))*anchoredNevanlinna s w*anchoredInteraction s w w * bulkQuadratic s w^(n-1) *
          (starRingEnd ℂ (bulkQuadratic s w))^(n+1) +
        (2*((n:ℂ)+1))*(starRingEnd ℂ (anchoredNevanlinna s w))*anchoredInteraction s w (starRingEnd ℂ w) *
          bulkQuadratic s w^n * (starRingEnd ℂ (bulkQuadratic s w))^n) := by
    simp only [P,LoopTest.eval_mul,LoopTest.directional_mul,LoopTest.eval_pow,LoopTest.directional_pow,
      eval_quadraticTest,directional_quadraticTest,v,Matrix.cons_val_zero,Matrix.cons_val_one,
      anchoredNevanlinna_conj,anchoredLoopHead,Beta.value,bulkQuadratic,map_add,map_pow,map_one,
      Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
    norm_num
    ring
  simpa only [heq] using h

def bulkQuadraticRemainder (s : AnchoredCountingState) (w : ℂ) (n : ℕ) : ℂ :=
  (2*(n:ℂ))*anchoredNevanlinna s w*anchoredInteraction s w w * bulkQuadratic s w^(n-1) *
    (starRingEnd ℂ (bulkQuadratic s w))^(n+1) +
  (2*((n:ℂ)+1))*(starRingEnd ℂ (anchoredNevanlinna s w))*anchoredInteraction s w (starRingEnd ℂ w) *
    bulkQuadratic s w^n * (starRingEnd ℂ (bulkQuadratic s w))^n

theorem quadratic_conj_power (z : ℂ) (n : ℕ) :
    z^n*(starRingEnd ℂ z)^n = (‖z‖^(2*n):ℝ) := by
  rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow, ← pow_mul]

theorem norm_bulkQuadraticRemainder_le (s : AnchoredCountingState)
    {w : ℂ} (hw : 0<w.im) (n : ℕ) :
    ‖bulkQuadraticRemainder s w n‖ ≤
      (4*((n:ℝ)+1)/w.im^2) * ‖anchoredNevanlinna s w‖^2 * ‖bulkQuadratic s w‖^(2*n) := by
  let A := ‖anchoredNevanlinna s w‖
  let B := ‖bulkQuadratic s w‖
  have hi := norm_anchoredInteraction_same_or_conj s hw (Or.inl rfl)
  have hj := norm_anchoredInteraction_same_or_conj s hw (Or.inr rfl)
  have hh : ‖bulkQuadraticRemainder s w n‖ ≤
      (2*(n:ℝ))*A*(A/w.im^2)*B^(n-1)*B^(n+1) +
      (2*((n:ℝ)+1))*A*(A/w.im^2)*B^n*B^n := by
    apply (norm_add_le _ _).trans
    simp only [bulkQuadraticRemainder, norm_mul, norm_pow, Complex.norm_conj,
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

/-- The high quadratic moment is bounded by the lower mixed moment. This is
an inequality of actual expectations, obtained from the exact hierarchy. -/
theorem integral_bulkQuadratic_even_le_mixed
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .two)
    {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w : ℂ} (hw : 0<w.im) (n : ℕ) :
    (∫ s, ‖bulkQuadratic s w‖^(2*(n+1)) ∂ν) ≤
      (4*((n:ℝ)+1)/w.im^2) *
        ∫ s, ‖anchoredNevanlinna s w‖^2 * ‖bulkQuadratic s w‖^(2*n) ∂ν := by
  have hQr := integrable_norm_pow_of_anchoredGrowth ν ha he
    (continuous_bulkQuadratic hw.ne') (anchoredGrowth_bulkQuadratic hw.ne') (2*(n+1))
  have hQc : Integrable (fun s : AnchoredCountingState => ((‖bulkQuadratic s w‖^(2*(n+1)):ℝ):ℂ)) ν :=
    hQr.ofReal
  have hmixed : Integrable (fun s => ‖anchoredNevanlinna s w‖^2 * ‖bulkQuadratic s w‖^(2*n)) ν := by
    simpa only [norm_mul,norm_pow] using (integrable_of_anchoredGrowth ν ha he
      (((continuous_anchoredNevanlinna hw.ne').pow 2).mul ((continuous_bulkQuadratic hw.ne').pow (2*n)))
      (((anchoredGrowth_nevanlinna hw.ne').pow 2).mul ((anchoredGrowth_bulkQuadratic hw.ne').pow (2*n)))).norm
  have h := exactHierarchy_bulkQuadratic_test ν hh hw.ne' n
  change Integrable (fun s => bulkQuadratic s w^(n+1)*(starRingEnd ℂ (bulkQuadratic s w))^(n+1)+
      bulkQuadraticRemainder s w n) ν ∧ _ at h
  simp_rw [quadratic_conj_power] at h
  have hRi : Integrable (fun s => bulkQuadraticRemainder s w n) ν := by
    convert h.1.sub hQc using 1
    ext s
    exact (add_sub_cancel_left _ _).symm
  have hzero := h.2
  change (∫ s, ((‖bulkQuadratic s w‖^(2*(n+1)):ℝ):ℂ)+bulkQuadraticRemainder s w n ∂ν)=0 at hzero
  rw [integral_add hQc hRi,integral_complex_ofReal] at hzero
  have hnorm : (∫ s, ‖bulkQuadratic s w‖^(2*(n+1)) ∂ν) =
      ‖∫ s, bulkQuadraticRemainder s w n ∂ν‖ := by
    have hh : (∫ s, bulkQuadraticRemainder s w n ∂ν) =
        -(∫ s, ‖bulkQuadratic s w‖^(2*(n+1)) ∂ν : ℝ) := by linear_combination hzero
    rw [hh,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    exact integral_nonneg (fun s => by positivity)
  rw [hnorm]
  calc
    _ ≤ ∫ s, ‖bulkQuadraticRemainder s w n‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ s, (4*((n:ℝ)+1)/w.im^2) * ‖anchoredNevanlinna s w‖^2 *
        ‖bulkQuadratic s w‖^(2*n) ∂ν := by
      apply integral_mono hRi.norm
        (by simpa only [mul_assoc] using hmixed.const_mul (4*((n:ℝ)+1)/w.im^2))
      exact fun s => norm_bulkQuadraticRemainder_le s hw n
    _ = _ := by simp only [mul_assoc,integral_const_mul]

end BourgadeHuang
