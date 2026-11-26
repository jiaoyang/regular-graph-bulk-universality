import GeneralizedBulk.Analysis.CountableStrata

/-! Nonnegative moment bounds survive the actual countable marked mixture. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace GeneralizedBulk.Analysis
variable {E I : Type*} [MeasurableSpace E] [MeasurableSpace I]
variable [Countable I] [MeasurableSingletonClass I]
variable (ν : Measure E) [IsProbabilityMeasure ν] (c : E → I) (hc : Measurable c)
variable (T : ActiveStratum ν c → Type*) [∀ i, MeasurableSpace (T i)]
variable (Q : ∀ i, Measure (T i)) [∀ i, IsProbabilityMeasure (Q i)]

theorem lintegral_stratumMarkedLaw (f : StratumSample ν c T → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂stratumMarkedLaw ν c hc T Q) =
      ∑' i : ActiveStratum ν c, ν (stratumSet c i.val) *
        ∫⁻ z, f ⟨i,z⟩ ∂(stratumProbability ν c hc i : Measure (stratumSet c i.val)).prod (Q i) := by
  rw [stratumMarkedLaw,lintegral_sum_measure]
  congr 1
  funext i
  rw [lintegral_smul_measure,lintegral_map hf (measurable_sigma_mk i)]
  rfl

/-- Fiberwise nonnegative moment domination gives genuine integrability of
the countable mixture and the same bound on its integral. -/
theorem integrable_stratumMarkedLaw_of_fiber_bound
    (f u : StratumSample ν c T → ℝ) (hf : Measurable f) (hu : Measurable u)
    (hf0 : ∀ z, 0 ≤ f z) (hu0 : ∀ z, 0 ≤ u z)
    (hiu : Integrable u (stratumMarkedLaw ν c hc T Q))
    (hif : ∀ i, Integrable (fun z => f ⟨i,z⟩)
      ((stratumProbability ν c hc i : Measure (stratumSet c i.val)).prod (Q i)))
    (hiuf : ∀ i, Integrable (fun z => u ⟨i,z⟩)
      ((stratumProbability ν c hc i : Measure (stratumSet c i.val)).prod (Q i)))
    (hbound : ∀ i, (∫ z, f ⟨i,z⟩
      ∂(stratumProbability ν c hc i : Measure (stratumSet c i.val)).prod (Q i)) ≤
      ∫ z, u ⟨i,z⟩
        ∂(stratumProbability ν c hc i : Measure (stratumSet c i.val)).prod (Q i)) :
    Integrable f (stratumMarkedLaw ν c hc T Q) ∧
      (∫ z, f z ∂stratumMarkedLaw ν c hc T Q) ≤ ∫ z, u z ∂stratumMarkedLaw ν c hc T Q := by
  have hle : (∫⁻ z, ENNReal.ofReal (f z) ∂stratumMarkedLaw ν c hc T Q) ≤
      ∫⁻ z, ENNReal.ofReal (u z) ∂stratumMarkedLaw ν c hc T Q := by
    rw [lintegral_stratumMarkedLaw ν c hc T Q _ hf.ennreal_ofReal,
      lintegral_stratumMarkedLaw ν c hc T Q _ hu.ennreal_ofReal]
    apply ENNReal.tsum_le_tsum
    intro i
    apply mul_le_mul_left'
    rw [← ofReal_integral_eq_lintegral_ofReal (hif i) (Eventually.of_forall (fun z => hf0 _)),
      ← ofReal_integral_eq_lintegral_ofReal (hiuf i) (Eventually.of_forall (fun z => hu0 _))]
    exact ENNReal.ofReal_le_ofReal (hbound i)
  have hint : Integrable f (stratumMarkedLaw ν c hc T Q) :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable
      (Eventually.of_forall hf0)).mp
      (ne_top_of_le_ne_top (by
        exact (lintegral_ofReal_ne_top_iff_integrable hiu.aestronglyMeasurable
          (Eventually.of_forall hu0)).mpr hiu) hle)
  refine ⟨hint,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hf0),
    ← ofReal_integral_eq_lintegral_ofReal hiu (Eventually.of_forall hu0)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hu0)).mp hle

end GeneralizedBulk.Analysis
