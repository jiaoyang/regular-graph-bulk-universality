import GeneralizedBulk.Analysis.StratumMoments

/-! Dominated fiber integral convergence through the actual countable mixture. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace GeneralizedBulk.Analysis
variable {E I : Type*} [MeasurableSpace E] [MeasurableSpace I]
variable [Countable I] [MeasurableSingletonClass I]
variable (ν : Measure E) [IsProbabilityMeasure ν] (c : E → I) (hc : Measurable c)
variable (T : ActiveStratum ν c → Type*) [∀ i, MeasurableSpace (T i)]
variable (Q : ∀ i, Measure (T i)) [∀ i, IsProbabilityMeasure (Q i)]

theorem integral_stratumMarkedLaw (f : StratumSample ν c T → ℝ) (hf : Measurable f)
    (hi : Integrable f (stratumMarkedLaw ν c hc T Q)) :
    (∫ z, f z ∂stratumMarkedLaw ν c hc T Q) =
      ∑' i : ActiveStratum ν c, (ν (stratumSet c i.val)).toReal *
        ∫ z, f ⟨i,z⟩ ∂(stratumProbability ν c hc i : Measure (stratumSet c i.val)).prod (Q i) := by
  rw [stratumMarkedLaw,integral_sum_measure hi]
  apply tsum_congr
  intro i
  rw [integral_smul_measure,integral_map (measurable_sigma_mk i).aemeasurable hf.aestronglyMeasurable]
  rfl

theorem integral_stratumMarkedLaw_tendsto_zero
    (f : ℕ → StratumSample ν c T → ℝ) (u : StratumSample ν c T → ℝ)
    (hf : ∀ n, Measurable (f n)) (hu : Measurable u)
    (hf0 : ∀ n z, 0 ≤ f n z) (hu0 : ∀ z, 0 ≤ u z)
    (hiu : Integrable u (stratumMarkedLaw ν c hc T Q))
    (hif : ∀ n i, Integrable (fun z => f n ⟨i,z⟩)
      ((stratumProbability ν c hc i : Measure (stratumSet c i.val)).prod (Q i)))
    (hiuf : ∀ i, Integrable (fun z => u ⟨i,z⟩)
      ((stratumProbability ν c hc i : Measure (stratumSet c i.val)).prod (Q i)))
    (hbound : ∀ n i, (∫ z, f n ⟨i,z⟩
      ∂(stratumProbability ν c hc i : Measure (stratumSet c i.val)).prod (Q i)) ≤
      ∫ z, u ⟨i,z⟩ ∂(stratumProbability ν c hc i : Measure (stratumSet c i.val)).prod (Q i))
    (hzero : ∀ i, Tendsto (fun n => ∫ z, f n ⟨i,z⟩
      ∂(stratumProbability ν c hc i : Measure (stratumSet c i.val)).prod (Q i)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, f n z ∂stratumMarkedLaw ν c hc T Q) atTop (𝓝 0) := by
  let W := fun i : ActiveStratum ν c => (ν (stratumSet c i.val)).toReal
  let P := fun i : ActiveStratum ν c =>
    (stratumProbability ν c hc i : Measure (stratumSet c i.val)).prod (Q i)
  let B := fun i : ActiveStratum ν c => W i * ∫ z, u ⟨i,z⟩ ∂P i
  have hsum : Summable B := by
    have hi : Integrable u (Measure.sum (fun i : ActiveStratum ν c =>
      ν (stratumSet c i.val) • Measure.map (Sigma.mk i) (P i))) := hiu
    have hs := (hasSum_integral_measure hi).summable
    have heq (i : ActiveStratum ν c) : (∫ z, u z
        ∂ν (stratumSet c i.val) • Measure.map (Sigma.mk i) (P i)) = B i := by
      rw [integral_smul_measure,integral_map (measurable_sigma_mk i).aemeasurable hu.aestronglyMeasurable]
      rfl
    simpa only [heq] using hs
  have hifull (n) : Integrable (f n) (stratumMarkedLaw ν c hc T Q) :=
    (integrable_stratumMarkedLaw_of_fiber_bound ν c hc T Q (f n) u (hf n) hu
      (hf0 n) hu0 hiu (hif n) hiuf (hbound n)).1
  have ht := tendsto_tsum_of_dominated_convergence hsum
    (fun i => by simpa only [mul_zero] using (hzero i).const_mul (W i))
    (Eventually.of_forall (fun n i => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg
        (integral_nonneg (fun z => hf0 n _)))]
      exact mul_le_mul_of_nonneg_left (hbound n i) ENNReal.toReal_nonneg))
  have hzeroSum : Tendsto (fun n => ∑' i, W i * (∫ z, f n ⟨i,z⟩ ∂P i)) atTop (𝓝 0) := by
    simpa only [tsum_zero] using ht
  convert hzeroSum using 1
  funext n
  exact integral_stratumMarkedLaw ν c hc T Q (f n) (hf n) (hifull n)

end GeneralizedBulk.Analysis
