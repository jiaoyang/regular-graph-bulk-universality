import GeneralizedBulk.Entropy.FiniteLawIntegral

/-! Literal finite sampling of measurable observations under an arbitrary
probability law, with exact law-mass and weighted integral identities. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace GeneralizedBulk.Entropy

variable {Ω Y S B : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] [Fintype S]

def finiteSampleLaw (μ : Measure Ω) (weight : S → ℝ) (F : S → Ω → Y) : Measure Y :=
  ∑ s,ENNReal.ofReal (weight s) • Measure.map (F s) μ

theorem finiteSampleLaw_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : S → ℝ) (hw : ∀ s,0 ≤ weight s) (hsum : ∑ s,weight s = 1)
    (F : S → Ω → Y) (hF : ∀ s,Measurable (F s)) : IsProbabilityMeasure (finiteSampleLaw μ weight F) := by
  constructor
  simp only [finiteSampleLaw,Measure.finset_sum_apply,Measure.smul_apply,
    Measure.map_apply (hF _) MeasurableSet.univ,Set.preimage_univ,measure_univ,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun s hs => hw s),hsum,ENNReal.ofReal_one]

theorem finiteSampleLaw_real (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : S → ℝ) (hw : ∀ s,0 ≤ weight s)
    (F : S → Ω → Y) (hF : ∀ s,Measurable (F s)) (T : Set Y) (hT : MeasurableSet T) :
    (finiteSampleLaw μ weight F).real T = ∑ s,weight s*μ.real ((F s) ⁻¹' T) := by
  unfold Measure.real finiteSampleLaw
  rw [Measure.finset_sum_apply,ENNReal.toReal_sum (fun s hs => by
    simp only [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
      rw [Measure.map_apply (hF s) hT]
      finiteness))]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (hw s),Measure.map_apply (hF s) hT]

theorem lawMass_finiteSampleLaw [MeasurableSpace B] [MeasurableSingletonClass B]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (weight : S → ℝ) (hw : ∀ s,0 ≤ weight s)
    (F : S → Ω → Y) (hF : ∀ s,Measurable (F s)) (J : Y → B) (hJ : Measurable J) (b : B) :
    lawMass (finiteSampleLaw μ weight F) J b = ∑ s,weight s*lawMass μ (J ∘ F s) b := by
  exact finiteSampleLaw_real μ weight hw F hF _ (hJ (measurableSet_singleton b))

theorem integrable_finiteSampleLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : S → ℝ) (F : S → Ω → Y) (f : Y → ℝ)
    (hf : ∀ s,Integrable f (Measure.map (F s) μ)) : Integrable f (finiteSampleLaw μ weight F) :=
  integrable_finset_sum_measure.mpr (fun s hs => (hf s).smul_measure ENNReal.ofReal_ne_top)

theorem integral_finiteSampleLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : S → ℝ) (hw : ∀ s,0 ≤ weight s) (F : S → Ω → Y) (hF : ∀ s,Measurable (F s))
    (f : Y → ℝ) (hf : ∀ s,Integrable f (Measure.map (F s) μ)) :
    (∫ y,f y ∂finiteSampleLaw μ weight F) = ∑ s,weight s*(∫ x,f (F s x) ∂μ) := by
  rw [finiteSampleLaw,integral_finset_sum_measure (fun s hs => (hf s).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro s hs
  rw [integral_smul_measure,ENNReal.toReal_ofReal (hw s),smul_eq_mul,
    integral_map (hF s).aemeasurable (hf s).aestronglyMeasurable]

end GeneralizedBulk.Entropy
