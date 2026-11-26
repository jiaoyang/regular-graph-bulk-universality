import GaussianWave.BS.Reused.Entropy.CountableLaw

/-! Integral identities for actual finite laws, including arbitrary coding
equivalences and the literal finite pushforward used in graph counting. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Entropy

variable {Ω A B : Type*} [MeasurableSpace Ω] [Fintype A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

theorem integrable_finite_observable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (hX : Measurable X) (f : A → ℝ) : Integrable (fun x => f (X x)) μ := by
  apply (MemLp.of_bound (p := (1 : ENNReal))
    ((measurable_of_finite f).comp hX).aestronglyMeasurable (∑ a,|f a|) _).integrable (by norm_num)
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun a : A => |f a|) (fun a ha => abs_nonneg _) (Finset.mem_univ (X x))

theorem finite_law_expectation (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (hX : Measurable X) (f : A → ℝ) :
    (∑ a,lawMass μ X a*f a) = ∫ x,f (X x) ∂μ := by
  simpa only [tsum_fintype] using
    (lawMass_weighted_hasSum μ X hX f (integrable_finite_observable μ X hX f)).tsum_eq

theorem finite_pushMass_lawMass (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (hX : Measurable X) (f : A → B) (b : B) :
    Finite.pushMass f (lawMass μ X) b = μ.real ((f ∘ X) ⁻¹' {b}) := by
  rw [← countablePush_lawMass μ X hX f b,countablePush_eq_tsum_indicator,tsum_fintype]
  simp only [Finite.pushMass,Finset.sum_filter]

theorem finite_entropy_law_equiv [Fintype B] (μ : Measure Ω) (X : Ω → A) (e : A ≃ B) :
    Finite.entropy (fun b => μ.real ((e ∘ X) ⁻¹' {b})) = Finite.entropy (lawMass μ X) := by
  have he (a : A) : μ.real ((e ∘ X) ⁻¹' {e a}) = lawMass μ X a := by
    congr 1
    ext x
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Function.comp_apply,EmbeddingLike.apply_eq_iff_eq,lawMass]
  unfold Finite.entropy
  rw [← e.sum_comp]
  simp only [he]

end GaussianWave.BS.Reused.Entropy
