import Mathlib

/-! Uniqueness identifies pointwise series versions with their actual L² sums. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace GeneralizedBulk.Analysis

theorem lp_finset_sum_ae {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ι → Lp ℂ 2 μ) (s : Finset ι) :
    (fun ω => (∑ i ∈ s, f i) ω) =ᵐ[μ] (fun ω => ∑ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Lp.coeFn_zero ℂ 2 μ)
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with ω hω hsum
      simp only [Pi.add_apply] at hω
      rw [hω, hsum]

/-- If the same partial sums converge in L² and almost surely, the pointwise
version agrees with the L² representative. No convergence assertion is assumed
for an unrelated candidate: both limits use the same finite partial sums. -/
theorem lp_tsum_eq_ae_of_hasSum
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : ι → Lp ℂ 2 μ) (g : Ω → ℂ)
    (hf : Summable f)
    (hg : ∀ᵐ ω ∂μ, HasSum (fun i => f i ω) (g ω)) :
    (fun ω => (∑' i, f i) ω) =ᵐ[μ] g := by
  classical
  obtain ⟨u, hu⟩ := exists_seq_tendsto (atTop : Filter (Finset ι))
  have hL2 : Tendsto (fun n => ∑ i ∈ u n, f i) atTop (𝓝 (∑' i, f i)) := hf.hasSum.comp hu
  have hmeasure := tendstoInMeasure_of_tendsto_Lp hL2
  have hpoint : TendstoInMeasure μ (fun n ω => ∑ i ∈ u n, f i ω) atTop g := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact (u n).aestronglyMeasurable_sum (fun i _ => Lp.aestronglyMeasurable (f i))
    · filter_upwards [hg] with ω hω
      exact hω.comp hu
  have hmeasure' : TendstoInMeasure μ (fun n ω => ∑ i ∈ u n, f i ω) atTop
      (fun ω => (∑' i, f i) ω) :=
    hmeasure.congr_left (fun n => lp_finset_sum_ae μ f (u n))
  exact tendstoInMeasure_ae_unique hmeasure' hpoint

end GeneralizedBulk.Analysis
