import BourgadeHuang.RationalBulk.BulkLocalLaw
import BourgadeHuang.BulkExponentialControl

/-! Centered sub-Gaussian control derived from the exact general-beta hierarchy. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgadeHuang.RationalBulk

theorem bulk_centered_factorial_moments
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w : ℂ} (hw : 0<w.im) (q : ℕ) :
    Integrable (fun s => (w.im*‖anchoredNevanlinna s w-Complex.I‖)^(2*q)) ν ∧
      (∫ s, (w.im*‖anchoredNevanlinna s w-Complex.I‖)^(2*q) ∂ν) ≤
        ((32*localLawConstant β)*Real.exp 1)^q*(q.factorial:ℝ) := by
  have hconstant := (localLawConstant_pos β).le
  cases q with
  | zero => simp
  | succ n =>
    obtain ⟨hi,hb⟩ := bulk_localLaw_even_moment ν β hh ha he hw n
    constructor
    · simpa only [mul_pow] using hi.const_mul (w.im^(2*(n+1)))
    · simp only [mul_pow,integral_const_mul]
      have hc : w.im^(2*(n+1))≠0 := pow_ne_zero _ hw.ne'
      calc
        _ ≤ w.im^(2*(n+1))*(((32*localLawConstant β)*((n:ℝ)+1))^(n+1)/w.im^(2*(n+1))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        _ = ((32*localLawConstant β)*((n:ℝ)+1))^(n+1) := by field_simp
        _ ≤ (32*localLawConstant β)^(n+1)*((Real.exp 1)^(n+1)*((n+1).factorial:ℝ)) := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add,Nat.cast_one] using nat_pow_le_exp_factorial (n+1)) (by positivity)
        _ = _ := by ring

def bulkExponentialScale (β : ℝ) : ℝ := (2*((32*localLawConstant β)*Real.exp 1))⁻¹

theorem bulkExponentialScale_pos (β : ℝ) : 0<bulkExponentialScale β := by
  unfold bulkExponentialScale
  have := localLawConstant_pos β
  positivity

/-- A uniform sub-Gaussian expectation bound at every spectral parameter. -/
theorem bulk_centered_exp_square
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w : ℂ} (hw : 0<w.im) :
    Integrable (fun s => Real.exp (bulkExponentialScale β*(w.im*‖anchoredNevanlinna s w-Complex.I‖)^2)) ν ∧
      (∫ s, Real.exp (bulkExponentialScale β*(w.im*‖anchoredNevanlinna s w-Complex.I‖)^2) ∂ν) ≤ 2 := by
  have hconstant := (localLawConstant_pos β).le
  have hconstant_ne := (localLawConstant_pos β).ne'
  have hc : bulkExponentialScale β*((32*localLawConstant β)*Real.exp 1)=1/2 := by
    dsimp [bulkExponentialScale]
    field_simp
    <;> ring
  have h := integral_exp_sq_le_of_factorial_moments ν
    (fun s => w.im*‖anchoredNevanlinna s w-Complex.I‖)
    (continuous_const.mul ((continuous_anchoredNevanlinna hw.ne').sub continuous_const).norm).aestronglyMeasurable
    (by positivity : 0≤(32*localLawConstant β)*Real.exp 1) (bulkExponentialScale_pos β).le (by rw [hc]; norm_num)
    (fun q => (bulk_centered_factorial_moments ν β hh ha he hw q).1)
    (fun q => (bulk_centered_factorial_moments ν β hh ha he hw q).2)
  simpa only [hc,show (1-(1:ℝ)/2)⁻¹=2 by norm_num] using h

/-- Linear exponential moments are uniformly bounded by the same beta-dependent
centered sub-Gaussian estimate. -/
theorem bulk_centered_exp_linear
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w : ℂ} (hw : 0<w.im) (L : ℝ) :
    Integrable (fun s => Real.exp (L*(w.im*‖anchoredNevanlinna s w-Complex.I‖))) ν ∧
      (∫ s, Real.exp (L*(w.im*‖anchoredNevanlinna s w-Complex.I‖)) ∂ν) ≤
        2*Real.exp (L^2/(4*bulkExponentialScale β)) := by
  have hscale := bulkExponentialScale_pos β
  let X := fun s : AnchoredCountingState => w.im*‖anchoredNevanlinna s w-Complex.I‖
  have hX : Continuous X := continuous_const.mul
    ((continuous_anchoredNevanlinna hw.ne').sub continuous_const).norm
  have hXn (s) : 0≤X s := mul_nonneg hw.le (norm_nonneg _)
  obtain ⟨hi,hb⟩ := bulk_centered_exp_square ν β hh ha he hw
  have hlin : Integrable (fun s => Real.exp (L*X s)) ν := by
    simpa only [abs_of_nonneg (hXn _)] using
      integrable_exp_mul_abs_of_exp_sq hX.aestronglyMeasurable (bulkExponentialScale_pos β) hi L
  refine ⟨hlin, ?_⟩
  have hp (s) : Real.exp (L*X s) ≤
      Real.exp (L^2/(4*bulkExponentialScale β))*Real.exp (bulkExponentialScale β*X s^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc := bulkExponentialScale_pos β
    have hs := sq_nonneg (2*bulkExponentialScale β*X s-L)
    apply (mul_le_mul_left (by positivity : 0<4*bulkExponentialScale β)).mp
    field_simp
    nlinarith only [hs]
  calc
    _ ≤ ∫ s, Real.exp (L^2/(4*bulkExponentialScale β))*Real.exp (bulkExponentialScale β*X s^2) ∂ν :=
      integral_mono hlin (hi.const_mul _) hp
    _ = Real.exp (L^2/(4*bulkExponentialScale β))*(∫ s, Real.exp (bulkExponentialScale β*X s^2) ∂ν) := integral_const_mul _ _
    _ ≤ _ := by nlinarith [Real.exp_pos (L^2/(4*bulkExponentialScale β))]


end BourgadeHuang.RationalBulk
