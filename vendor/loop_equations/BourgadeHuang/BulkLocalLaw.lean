import BourgadeHuang.BulkQuadraticMoments

/-! Large-height local laws derived from the actual limiting loop hierarchy. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgadeHuang

/-- Cauchy--Schwarz against the constant function on a probability space,
proved directly by integrating a nonnegative square. -/
theorem integral_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x^2) μ)
    (hfn : ∀ x, 0≤f x) :
    (∫ x, f x ∂μ) ≤ Real.sqrt (∫ x, f x^2 ∂μ) := by
  let c := ∫ x, f x ∂μ
  have hc : 0≤c := integral_nonneg hfn
  have hsq : 0≤∫ x, (f x-c)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have heq : (fun x => (f x-c)^2) = (fun x => f x^2 - (2*c)*f x + c^2) := by
    funext x
    ring
  rw [heq] at hsq
  have hsplit := integral_add (hf2.sub (hf.const_mul (2*c))) (integrable_const (c^2))
  dsimp only [Pi.sub_apply] at hsplit
  rw [hsplit,integral_sub hf2 (hf.const_mul (2*c)),integral_const_mul] at hsq
  simp only [integral_const,measureReal_univ_eq_one,one_smul] at hsq
  apply (Real.le_sqrt hc (integral_nonneg (fun x => sq_nonneg _))).mpr
  dsimp [c] at hsq ⊢
  nlinarith

/-- The quadratic moment satisfies a scalar self-consistency estimate.
Only the exact hierarchy and one actual exponential-square anchor moment enter. -/
theorem bulkQuadratic_moment_bootstrap
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w : ℂ} (hw : 0<w.im) (n : ℕ) :
    let A := ∫ s, ‖bulkQuadratic s w‖^(2*(n+1)) ∂ν
    A ≤ 2 * (32*((n:ℝ)+1)/w.im^2)^(n+1) * (1+Real.sqrt A) := by
  let A := ∫ s, ‖bulkQuadratic s w‖^(2*(n+1)) ∂ν
  let C := 4*((n:ℝ)+1)/w.im^2
  have hC : 0≤C := by dsimp [C]; positivity
  have hQ (k : ℕ) := integrable_norm_pow_of_anchoredGrowth ν ha he
    (continuous_bulkQuadratic hw.ne') (anchoredGrowth_bulkQuadratic hw.ne') k
  have hS (k : ℕ) := integrable_norm_pow_of_anchoredGrowth ν ha he
    (continuous_anchoredNevanlinna hw.ne') (anchoredGrowth_nevanlinna hw.ne') k
  have hM : Integrable (fun s => ‖anchoredNevanlinna s w‖^2 * ‖bulkQuadratic s w‖^(2*n)) ν := by
    simpa only [norm_mul,norm_pow] using (integrable_of_anchoredGrowth ν ha he
      (((continuous_anchoredNevanlinna hw.ne').pow 2).mul ((continuous_bulkQuadratic hw.ne').pow (2*n)))
      (((anchoredGrowth_nevanlinna hw.ne').pow 2).mul ((anchoredGrowth_bulkQuadratic hw.ne').pow (2*n)))).norm
  have hpoint (s : AnchoredCountingState) :
      C*(‖anchoredNevanlinna s w‖^2 * ‖bulkQuadratic s w‖^(2*n)) ≤
      ‖bulkQuadratic s w‖^(2*(n+1))/2 +
        (2*C)^(n+1)*‖anchoredNevanlinna s w‖^(2*(n+1)) := by
    have ht := localLaw_young_nat n (mul_nonneg hC (sq_nonneg ‖anchoredNevanlinna s w‖))
      (sq_nonneg ‖bulkQuadratic s w‖)
    convert ht using 1 <;> simp only [mul_pow,pow_mul] <;> ring
  have hyoung := integral_mono (hM.const_mul C)
    ((hQ (2*(n+1))).div_const 2 |>.add ((hS (2*(n+1))).const_mul ((2*C)^(n+1)))) hpoint
  simp only [Pi.add_apply] at hyoung
  rw [integral_const_mul,integral_add ((hQ (2*(n+1))).div_const 2)
    ((hS (2*(n+1))).const_mul ((2*C)^(n+1))),integral_div,integral_const_mul] at hyoung
  have hboot0 := integral_bulkQuadratic_even_le_mixed ν hh ha he hw n
  change A ≤ C*(∫ s, ‖anchoredNevanlinna s w‖^2 * ‖bulkQuadratic s w‖^(2*n) ∂ν) at hboot0
  have hboot1 : A ≤ 2*(2*C)^(n+1)*(∫ s, ‖anchoredNevanlinna s w‖^(2*(n+1)) ∂ν) := by
    dsimp only [A] at *
    linarith
  have hsbound : (∫ s, ‖anchoredNevanlinna s w‖^(2*(n+1)) ∂ν) ≤
      4^(n+1)*(1+∫ s, ‖bulkQuadratic s w‖^(n+1) ∂ν) := by
    calc
      _ ≤ ∫ s, 4^(n+1)*(1+‖bulkQuadratic s w‖^(n+1)) ∂ν := by
        apply integral_mono (hS (2*(n+1))) (((integrable_const 1).add (hQ (n+1))).const_mul _)
        exact fun s => nevanlinna_norm_pow_le _ (anchoredNevanlinna_im_nonneg s hw) (n+1)
      _ = _ := by rw [integral_const_mul,integral_add (integrable_const 1) (hQ (n+1))]; simp
  have hcs : (∫ s, ‖bulkQuadratic s w‖^(n+1) ∂ν) ≤ Real.sqrt A := by
    have ht := integral_le_sqrt_integral_sq ν (hQ (n+1))
      (show Integrable (fun s => (‖bulkQuadratic s w‖^(n+1))^2) ν from
        by simpa only [← pow_mul, Nat.mul_comm (n+1) 2] using hQ (2*(n+1)))
      (fun s => by positivity)
    simpa only [A,← pow_mul,Nat.mul_comm (n+1) 2] using ht
  calc
    A ≤ 2*(2*C)^(n+1)*(4^(n+1)*(1+∫ s, ‖bulkQuadratic s w‖^(n+1) ∂ν)) :=
      hboot1.trans (mul_le_mul_of_nonneg_left hsbound (by positivity))
    _ ≤ 2*(2*C)^(n+1)*(4^(n+1)*(1+Real.sqrt A)) := by gcongr
    _ = 2*((2*C)*4)^(n+1)*(1+Real.sqrt A) := by simp only [mul_pow]; ring
    _ = _ := by
      have hc : (2*C)*4 = 32*((n:ℝ)+1)/w.im^2 := by dsimp [C]; ring
      rw [hc]

/-- All centered even moments satisfy the bulk local law, uniformly over the
upper half-plane. The numerical constant is explicit and independent of the law. -/
theorem bulk_localLaw_even_moment
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w : ℂ} (hw : 0<w.im) (n : ℕ) :
    Integrable (fun s => ‖anchoredNevanlinna s w-Complex.I‖^(2*(n+1))) ν ∧
    (∫ s, ‖anchoredNevanlinna s w-Complex.I‖^(2*(n+1)) ∂ν) ≤
      (128*((n:ℝ)+1))^(n+1)/w.im^(2*(n+1)) := by
  let A := ∫ s, ‖bulkQuadratic s w‖^(2*(n+1)) ∂ν
  let B := ∫ s, ‖anchoredNevanlinna s w-Complex.I‖^(2*(n+1)) ∂ν
  let D := 2*(32*((n:ℝ)+1)/w.im^2)^(n+1)
  have hD : 0≤D := by dsimp [D]; positivity
  have hA : 0≤A := integral_nonneg (fun s => by positivity)
  have hQ (k : ℕ) := integrable_norm_pow_of_anchoredGrowth ν ha he
    (continuous_bulkQuadratic hw.ne') (anchoredGrowth_bulkQuadratic hw.ne') k
  have hBint := integrable_norm_pow_of_anchoredGrowth ν ha he
    ((continuous_anchoredNevanlinna hw.ne').sub continuous_const)
    ((anchoredGrowth_nevanlinna hw.ne').sub ((AnchoredGrowth.const Complex.I).mono (by omega))) (2*(n+1))
  refine ⟨hBint, ?_⟩
  have hBA : B≤A := by
    apply integral_mono hBint (hQ (2*(n+1)))
    intro s
    exact pow_le_pow_left₀ (norm_nonneg _)
      (nevanlinna_norm_sub_I_le _ (anchoredNevanlinna_im_nonneg s hw)) _
  have hBR : B≤Real.sqrt A := by
    calc
      B ≤ ∫ s, ‖bulkQuadratic s w‖^(n+1) ∂ν := by
        apply integral_mono hBint (hQ (n+1))
        intro s
        dsimp only
        rw [pow_mul]
        exact pow_le_pow_left₀ (sq_nonneg _)
          (nevanlinna_norm_sub_I_sq_le _ (anchoredNevanlinna_im_nonneg s hw)) _
      _ ≤ Real.sqrt A := by
        have ht := integral_le_sqrt_integral_sq ν (hQ (n+1))
          (show Integrable (fun s => (‖bulkQuadratic s w‖^(n+1))^2) ν from
            by simpa only [← pow_mul, Nat.mul_comm (n+1) 2] using hQ (2*(n+1)))
          (fun s => by positivity)
        simpa only [A,← pow_mul,Nat.mul_comm (n+1) 2] using ht
  have hboot : (Real.sqrt A)^2 ≤ D*(1+Real.sqrt A) := by
    rw [Real.sq_sqrt hA]
    exact bulkQuadratic_moment_bootstrap ν hh ha he hw n
  have hb : B≤2*D := by
    by_cases hr : Real.sqrt A≤1
    · have ht := localLaw_absorption_small hD hr hboot
      rw [Real.sq_sqrt hA] at ht
      exact hBA.trans ht
    · exact hBR.trans (localLaw_absorption_large hD (le_of_not_ge hr) hboot)
  calc
    B ≤ 4*(32*((n:ℝ)+1)/w.im^2)^(n+1) := by convert hb using 1; dsimp [D]; ring
    _ ≤ 4^(n+1)*(32*((n:ℝ)+1)/w.im^2)^(n+1) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤4) (show 1≤n+1 by omega)
    _ = _ := by
      rw [← mul_pow]
      have hc : 4*(32*((n:ℝ)+1)/w.im^2) = (128*((n:ℝ)+1))/w.im^2 := by ring
      rw [hc,div_pow,pow_mul]

end BourgadeHuang
