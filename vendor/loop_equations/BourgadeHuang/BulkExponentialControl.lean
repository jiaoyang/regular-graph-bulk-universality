import BourgadeHuang.BulkLocalLaw

/-! Uniform exponential control of the centered Nevanlinna values. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

/-- A factorial lower bound obtained from a single positive term of the
exponential series, avoiding any asymptotic form of Stirling's formula. -/
theorem nat_pow_le_exp_factorial (q : ℕ) :
    (q:ℝ)^q ≤ (Real.exp 1)^q*(q.factorial:ℝ) := by
  have hs : HasSum (fun k : ℕ => (q:ℝ)^k/(k.factorial:ℝ)) (Real.exp (q:ℝ)) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp ℝ (q:ℝ)
  have ht := hs.summable.le_tsum q (fun k _ => by positivity)
  rw [hs.tsum_eq] at ht
  have hfac : (0:ℝ)<q.factorial := by exact_mod_cast Nat.factorial_pos q
  apply (div_le_iff₀ hfac).mp
  simpa only [← Real.exp_nat_mul, mul_one] using ht

/-- The quantitative form of the factorial-moment exponential estimate. -/
theorem integral_exp_sq_le_of_factorial_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : AEStronglyMeasurable X μ) {C t : ℝ} (hC : 0≤C) (ht : 0≤t)
    (htC : t*C<1)
    (hm : ∀ q : ℕ, Integrable (fun ω => X ω^(2*q)) μ)
    (hb : ∀ q : ℕ, (∫ ω, X ω^(2*q) ∂μ) ≤ C^q*(q.factorial:ℝ)) :
    Integrable (fun ω => Real.exp (t*X ω^2)) μ ∧
      (∫ ω, Real.exp (t*X ω^2) ∂μ) ≤ (1-t*C)⁻¹ := by
  refine ⟨integrable_exp_sq_of_factorial_moments μ X hX hC ht htC hm hb, ?_⟩
  let f : ℕ → Ω → ℝ := fun q ω => (t*X ω^2)^q/(q.factorial:ℝ)
  have hfn (q : ℕ) (ω : Ω) : 0≤f q ω := by dsimp [f]; positivity
  have hfeq (q : ℕ) : f q = fun ω => (t^q/(q.factorial:ℝ))*X ω^(2*q) := by
    funext ω
    simp only [f,mul_pow,pow_mul]
    ring
  have hfi (q : ℕ) : Integrable (f q) μ := by rw [hfeq]; exact (hm q).const_mul _
  have hmean (q : ℕ) : (∫ ω, f q ω ∂μ) ≤ (t*C)^q := by
    rw [hfeq,integral_const_mul]
    calc
      _ ≤ (t^q/(q.factorial:ℝ))*(C^q*(q.factorial:ℝ)) :=
        mul_le_mul_of_nonneg_left (hb q) (by positivity)
      _ = _ := by
        have hfac : (q.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero q
        field_simp
        ring
  have hg := hasSum_geometric_of_lt_one (mul_nonneg ht hC) htC
  have hsum : Summable (fun q => ∫ ω, f q ω ∂μ) :=
    hg.summable.of_nonneg_of_le (fun q => integral_nonneg (hfn q)) hmean
  have hnorm : Summable (fun q => ∫ ω, ‖f q ω‖ ∂μ) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hfn _ _)] using hsum
  have hseries (ω : Ω) : (∑' q, f q ω) = Real.exp (t*X ω^2) := by
    exact (show HasSum (fun q => f q ω) (Real.exp (t*X ω^2)) from by
      simpa only [f,Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp ℝ (t*X ω^2)).tsum_eq
  calc
    _ = ∑' q, ∫ ω, f q ω ∂μ := by
      rw [integral_tsum_of_summable_integral_norm hfi hnorm]
      simp only [hseries]
    _ ≤ ∑' q, (t*C)^q := hsum.tsum_le_tsum hmean hg.summable
    _ = _ := hg.tsum_eq

/-- Factorial growth is uniform in the point of the upper half-plane after
multiplication by its height. -/
theorem bulk_centered_factorial_moments
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w : ℂ} (hw : 0<w.im) (q : ℕ) :
    Integrable (fun s => (w.im*‖anchoredNevanlinna s w-Complex.I‖)^(2*q)) ν ∧
      (∫ s, (w.im*‖anchoredNevanlinna s w-Complex.I‖)^(2*q) ∂ν) ≤
        (128*Real.exp 1)^q*(q.factorial:ℝ) := by
  cases q with
  | zero => simp
  | succ n =>
    obtain ⟨hi,hb⟩ := bulk_localLaw_even_moment ν hh ha he hw n
    constructor
    · simpa only [mul_pow] using hi.const_mul (w.im^(2*(n+1)))
    · simp only [mul_pow,integral_const_mul]
      have hc : w.im^(2*(n+1))≠0 := pow_ne_zero _ hw.ne'
      calc
        _ ≤ w.im^(2*(n+1))*((128*((n:ℝ)+1))^(n+1)/w.im^(2*(n+1))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        _ = (128*((n:ℝ)+1))^(n+1) := by field_simp
        _ ≤ 128^(n+1)*((Real.exp 1)^(n+1)*((n+1).factorial:ℝ)) := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add,Nat.cast_one] using nat_pow_le_exp_factorial (n+1)) (by positivity)
        _ = _ := by ring

def bulkExponentialScale : ℝ := (2*(128*Real.exp 1))⁻¹

theorem bulkExponentialScale_pos : 0<bulkExponentialScale := by
  unfold bulkExponentialScale
  positivity

/-- A uniform sub-Gaussian expectation bound at every spectral parameter. -/
theorem bulk_centered_exp_square
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w : ℂ} (hw : 0<w.im) :
    Integrable (fun s => Real.exp (bulkExponentialScale*(w.im*‖anchoredNevanlinna s w-Complex.I‖)^2)) ν ∧
      (∫ s, Real.exp (bulkExponentialScale*(w.im*‖anchoredNevanlinna s w-Complex.I‖)^2) ∂ν) ≤ 2 := by
  have hc : bulkExponentialScale*(128*Real.exp 1)=1/2 := by
    dsimp [bulkExponentialScale]
    field_simp
    ring
  have h := integral_exp_sq_le_of_factorial_moments ν
    (fun s => w.im*‖anchoredNevanlinna s w-Complex.I‖)
    (continuous_const.mul ((continuous_anchoredNevanlinna hw.ne').sub continuous_const).norm).aestronglyMeasurable
    (by positivity : 0≤128*Real.exp 1) bulkExponentialScale_pos.le (by rw [hc]; norm_num)
    (fun q => (bulk_centered_factorial_moments ν hh ha he hw q).1)
    (fun q => (bulk_centered_factorial_moments ν hh ha he hw q).2)
  simpa only [hc,show (1-(1:ℝ)/2)⁻¹=2 by norm_num] using h

/-- Linear exponential moments are uniformly bounded by the same universal
centered sub-Gaussian estimate. -/
theorem bulk_centered_exp_linear
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {w : ℂ} (hw : 0<w.im) (L : ℝ) :
    Integrable (fun s => Real.exp (L*(w.im*‖anchoredNevanlinna s w-Complex.I‖))) ν ∧
      (∫ s, Real.exp (L*(w.im*‖anchoredNevanlinna s w-Complex.I‖)) ∂ν) ≤
        2*Real.exp (L^2/(4*bulkExponentialScale)) := by
  let X := fun s : AnchoredCountingState => w.im*‖anchoredNevanlinna s w-Complex.I‖
  have hX : Continuous X := continuous_const.mul
    ((continuous_anchoredNevanlinna hw.ne').sub continuous_const).norm
  have hXn (s) : 0≤X s := mul_nonneg hw.le (norm_nonneg _)
  obtain ⟨hi,hb⟩ := bulk_centered_exp_square ν hh ha he hw
  have hlin : Integrable (fun s => Real.exp (L*X s)) ν := by
    simpa only [abs_of_nonneg (hXn _)] using
      integrable_exp_mul_abs_of_exp_sq hX.aestronglyMeasurable bulkExponentialScale_pos hi L
  refine ⟨hlin, ?_⟩
  have hp (s) : Real.exp (L*X s) ≤
      Real.exp (L^2/(4*bulkExponentialScale))*Real.exp (bulkExponentialScale*X s^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc := bulkExponentialScale_pos
    have hs := sq_nonneg (2*bulkExponentialScale*X s-L)
    apply (mul_le_mul_left (by positivity : 0<4*bulkExponentialScale)).mp
    field_simp
    nlinarith only [hs]
  calc
    _ ≤ ∫ s, Real.exp (L^2/(4*bulkExponentialScale))*Real.exp (bulkExponentialScale*X s^2) ∂ν :=
      integral_mono hlin (hi.const_mul _) hp
    _ = Real.exp (L^2/(4*bulkExponentialScale))*(∫ s, Real.exp (bulkExponentialScale*X s^2) ∂ν) := integral_const_mul _ _
    _ ≤ _ := by nlinarith [Real.exp_pos (L^2/(4*bulkExponentialScale))]

/-- Jensen's exponential inequality on a probability space, proved directly
from the tangent-line inequality for the real exponential. -/
theorem exp_integral_le_integral_exp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (he : Integrable (fun x => Real.exp (f x)) μ) :
    Real.exp (∫ x, f x ∂μ) ≤ ∫ x, Real.exp (f x) ∂μ := by
  let c := ∫ x, f x ∂μ
  have hp (x : Ω) : Real.exp c*(1+f x-c) ≤ Real.exp (f x) := by
    have ht := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (f x-c)) (Real.exp_nonneg c)
    rw [← Real.exp_add] at ht
    convert ht using 1 <;> congr 1 <;> ring
  have hi : Integrable (fun x => Real.exp c*(1+f x-c)) μ :=
    (((integrable_const 1).add hf).sub (integrable_const c)).const_mul _
  have ht := integral_mono hi he hp
  have hsp := integral_sub ((integrable_const 1).add hf) (integrable_const c)
  dsimp only [Pi.add_apply] at hsp
  rw [integral_const_mul,hsp,integral_add (integrable_const 1) hf] at ht
  simpa [c] using ht

end BourgadeHuang
