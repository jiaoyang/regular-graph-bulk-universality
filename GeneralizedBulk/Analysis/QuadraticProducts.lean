import Mathlib

/-! Second moments control correlated products and their vanishing L1 limits. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Analysis

/-- Products are integrable from their actual second moments; independence
is unnecessary. -/
theorem integrable_real_product_of_squares
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f g : Ω → ℝ)
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P)
    (hf2 : Integrable (fun x => f x ^ 2) P) (hg2 : Integrable (fun x => g x ^ 2) P) :
    Integrable (fun x => f x * g x) P := by
  apply ((hf2.add hg2).div_const 2).mono' (hf.mul hg)
  filter_upwards [] with x
  dsimp only [Pi.mul_apply, Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]

/-- The genuine Cauchy--Schwarz bound in the scalar second-moment form. -/
theorem integral_nonnegative_mul_le_sqrt
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f g : Ω → ℝ)
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P)
    (hfnonneg : ∀ᵐ x ∂P, 0 ≤ f x) (hgnonneg : ∀ᵐ x ∂P, 0 ≤ g x)
    (hf2 : Integrable (fun x => f x ^ 2) P) (hg2 : Integrable (fun x => g x ^ 2) P) :
    (∫ x, f x * g x ∂P) ≤ Real.sqrt (∫ x, f x ^ 2 ∂P) * Real.sqrt (∫ x, g x ^ 2 ∂P) := by
  have hflp : MemLp f 2 P := (memLp_two_iff_integrable_sq hf).mpr hf2
  have hglp : MemLp g 2 P := (memLp_two_iff_integrable_sq hg).mpr hg2
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    hfnonneg hgnonneg (by simpa using hflp) (by simpa using hglp)
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow, one_div] using h

/-- A vanishing second moment and a uniformly bounded second moment give
vanishing L1 products even for maximally correlated random variables. -/
theorem integral_product_tendsto_zero_of_square_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f g : ℕ → Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) P) (hg : ∀ n, AEStronglyMeasurable (g n) P)
    (hfnonneg : ∀ n, ∀ᵐ x ∂P, 0 ≤ f n x) (hgnonneg : ∀ n, ∀ᵐ x ∂P, 0 ≤ g n x)
    (hf2 : ∀ n, Integrable (fun x => f n x ^ 2) P)
    (hg2 : ∀ n, Integrable (fun x => g n x ^ 2) P)
    (hzero : Tendsto (fun n => ∫ x, f n x ^ 2 ∂P) atTop (𝓝 0))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, (∫ x, g n x ^ 2 ∂P) ≤ C) :
    Tendsto (fun n => ∫ x, f n x * g n x ∂P) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun n => Real.sqrt (∫ x, f n x ^ 2 ∂P)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hzero
  apply squeeze_zero (fun n => integral_nonneg_of_ae (by
    filter_upwards [hfnonneg n,hgnonneg n] with x hfx hgx
    exact mul_nonneg hfx hgx)) _ (by
      simpa only [zero_mul] using hsqrt.mul_const (Real.sqrt C))
  intro n
  exact (integral_nonnegative_mul_le_sqrt P (f n) (g n) (hf n) (hg n)
    (hfnonneg n) (hgnonneg n) (hf2 n) (hg2 n)).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hbound n)) (Real.sqrt_nonneg _))

/-- In a probability space a vanishing second moment also gives a
vanishing first moment. -/
theorem integral_tendsto_zero_of_square_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (hf : ∀ n, AEStronglyMeasurable (f n) P)
    (hfnonneg : ∀ n, ∀ᵐ x ∂P, 0 ≤ f n x)
    (hf2 : ∀ n, Integrable (fun x => f n x ^ 2) P)
    (hzero : Tendsto (fun n => ∫ x, f n x ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ∂P) atTop (𝓝 0) := by
  have h := integral_product_tendsto_zero_of_square_tendsto P f (fun _ _ => 1) hf
    (fun n => aestronglyMeasurable_const) hfnonneg
    (fun n => Eventually.of_forall (fun x => zero_le_one)) hf2
    (fun n => by simpa only [one_pow] using integrable_const (μ := P) (1 : ℝ)) hzero
    1 zero_le_one (fun n => by simp)
  simpa only [mul_one] using h

end GeneralizedBulk.Analysis
