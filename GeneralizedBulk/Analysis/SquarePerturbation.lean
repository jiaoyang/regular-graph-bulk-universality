import GeneralizedBulk.Analysis.QuadraticProducts

/-! Vanishing second moments survive deterministic perturbations tending to zero. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Analysis

theorem integrable_square_add_const
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f P)
    (hf2 : Integrable (fun x => f x ^ 2) P) (c : ℝ) :
    Integrable (fun x => (f x + c) ^ 2) P := by
  apply ((hf2.const_mul 2).add (integrable_const (2 * c ^ 2))).mono'
    ((hf.add aestronglyMeasurable_const).pow 2)
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  dsimp only [Pi.add_apply,Pi.pow_apply]
  nlinarith [sq_nonneg (f x - c)]

theorem integral_square_add_const_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (hf : ∀ n, AEStronglyMeasurable (f n) P)
    (hf2 : ∀ n, Integrable (fun x => f n x ^ 2) P)
    (hzero : Tendsto (fun n => ∫ x, f n x ^ 2 ∂P) atTop (𝓝 0))
    (c : ℕ → ℝ) (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, (f n x + c n) ^ 2 ∂P) atTop (𝓝 0) := by
  have hbound (n) : (∫ x, (f n x + c n) ^ 2 ∂P) ≤
      2 * (∫ x, f n x ^ 2 ∂P) + 2 * c n ^ 2 := by
    have hp (x) : (f n x + c n) ^ 2 ≤ 2 * f n x ^ 2 + 2 * c n ^ 2 := by
      nlinarith [sq_nonneg (f n x - c n)]
    have h := integral_mono (integrable_square_add_const P (f n) (hf n) (hf2 n) (c n))
      (((hf2 n).const_mul 2).add (integrable_const (2 * c n ^ 2))) hp
    simp only [Pi.add_apply] at h
    rw [integral_add ((hf2 n).const_mul 2) (integrable_const _),integral_const_mul,
      integral_const,measureReal_univ_eq_one,one_smul] at h
    exact h
  have ht : Tendsto (fun n => 2 * (∫ x, f n x ^ 2 ∂P) + 2 * c n ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero,add_zero] using
      (hzero.const_mul 2).add ((hc.pow 2).const_mul 2)
  exact squeeze_zero (fun n => integral_nonneg (fun x => sq_nonneg _)) hbound ht

end GeneralizedBulk.Analysis
