import BourgadeHuang.OrthogonalBulkLocalLaw
import BourgadeHuang.BulkExponentialControl

/-! Centered sub-Gaussian control derived from the exact β = 1 hierarchy. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgadeHuang

theorem orthogonal_bulk_centered_factorial_moments
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .one) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w : ℂ} (hw : 0<w.im) (q : ℕ) :
    Integrable (fun s => (w.im*‖anchoredNevanlinna s w-Complex.I‖)^(2*q)) ν ∧
      (∫ s, (w.im*‖anchoredNevanlinna s w-Complex.I‖)^(2*q) ∂ν) ≤
        (384*Real.exp 1)^q*(q.factorial:ℝ) := by
  cases q with
  | zero => simp
  | succ n =>
    obtain ⟨hi,hb⟩ := orthogonal_bulk_localLaw_even_moment ν hh ha he hw n
    constructor
    · simpa only [mul_pow] using hi.const_mul (w.im^(2*(n+1)))
    · simp only [mul_pow,integral_const_mul]
      have hc : w.im^(2*(n+1))≠0 := pow_ne_zero _ hw.ne'
      calc
        _ ≤ w.im^(2*(n+1))*((384*((n:ℝ)+1))^(n+1)/w.im^(2*(n+1))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        _ = (384*((n:ℝ)+1))^(n+1) := by field_simp
        _ ≤ 384^(n+1)*((Real.exp 1)^(n+1)*((n+1).factorial:ℝ)) := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add,Nat.cast_one] using nat_pow_le_exp_factorial (n+1)) (by positivity)
        _ = _ := by ring

def orthogonalBulkExponentialScale : ℝ := (2*(384*Real.exp 1))⁻¹

theorem orthogonalBulkExponentialScale_pos : 0<orthogonalBulkExponentialScale := by
  unfold orthogonalBulkExponentialScale
  positivity

/-- A uniform sub-Gaussian expectation bound at every spectral parameter. -/
theorem orthogonal_bulk_centered_exp_square
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .one) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w : ℂ} (hw : 0<w.im) :
    Integrable (fun s => Real.exp (orthogonalBulkExponentialScale*(w.im*‖anchoredNevanlinna s w-Complex.I‖)^2)) ν ∧
      (∫ s, Real.exp (orthogonalBulkExponentialScale*(w.im*‖anchoredNevanlinna s w-Complex.I‖)^2) ∂ν) ≤ 2 := by
  have hc : orthogonalBulkExponentialScale*(384*Real.exp 1)=1/2 := by
    dsimp [orthogonalBulkExponentialScale]
    field_simp
    ring
  have h := integral_exp_sq_le_of_factorial_moments ν
    (fun s => w.im*‖anchoredNevanlinna s w-Complex.I‖)
    (continuous_const.mul ((continuous_anchoredNevanlinna hw.ne').sub continuous_const).norm).aestronglyMeasurable
    (by positivity : 0≤384*Real.exp 1) orthogonalBulkExponentialScale_pos.le (by rw [hc]; norm_num)
    (fun q => (orthogonal_bulk_centered_factorial_moments ν hh ha he hw q).1)
    (fun q => (orthogonal_bulk_centered_factorial_moments ν hh ha he hw q).2)
  simpa only [hc,show (1-(1:ℝ)/2)⁻¹=2 by norm_num] using h

/-- Linear exponential moments are uniformly bounded by the same universal
centered sub-Gaussian estimate. -/
theorem orthogonal_bulk_centered_exp_linear
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .one) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w : ℂ} (hw : 0<w.im) (L : ℝ) :
    Integrable (fun s => Real.exp (L*(w.im*‖anchoredNevanlinna s w-Complex.I‖))) ν ∧
      (∫ s, Real.exp (L*(w.im*‖anchoredNevanlinna s w-Complex.I‖)) ∂ν) ≤
        2*Real.exp (L^2/(4*orthogonalBulkExponentialScale)) := by
  let X := fun s : AnchoredCountingState => w.im*‖anchoredNevanlinna s w-Complex.I‖
  have hX : Continuous X := continuous_const.mul
    ((continuous_anchoredNevanlinna hw.ne').sub continuous_const).norm
  have hXn (s) : 0≤X s := mul_nonneg hw.le (norm_nonneg _)
  obtain ⟨hi,hb⟩ := orthogonal_bulk_centered_exp_square ν hh ha he hw
  have hlin : Integrable (fun s => Real.exp (L*X s)) ν := by
    simpa only [abs_of_nonneg (hXn _)] using
      integrable_exp_mul_abs_of_exp_sq hX.aestronglyMeasurable orthogonalBulkExponentialScale_pos hi L
  refine ⟨hlin, ?_⟩
  have hp (s) : Real.exp (L*X s) ≤
      Real.exp (L^2/(4*orthogonalBulkExponentialScale))*Real.exp (orthogonalBulkExponentialScale*X s^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc := orthogonalBulkExponentialScale_pos
    have hs := sq_nonneg (2*orthogonalBulkExponentialScale*X s-L)
    apply (mul_le_mul_left (by positivity : 0<4*orthogonalBulkExponentialScale)).mp
    field_simp
    nlinarith only [hs]
  calc
    _ ≤ ∫ s, Real.exp (L^2/(4*orthogonalBulkExponentialScale))*Real.exp (orthogonalBulkExponentialScale*X s^2) ∂ν :=
      integral_mono hlin (hi.const_mul _) hp
    _ = Real.exp (L^2/(4*orthogonalBulkExponentialScale))*(∫ s, Real.exp (orthogonalBulkExponentialScale*X s^2) ∂ν) := integral_const_mul _ _
    _ ≤ _ := by nlinarith [Real.exp_pos (L^2/(4*orthogonalBulkExponentialScale))]


end BourgadeHuang
