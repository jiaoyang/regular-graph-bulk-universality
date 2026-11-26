import GeneralizedBulk.Entropy.FiniteSampleLaw

/-! Actual maps of finite sampled laws and normalized uniform weights. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy

def uniformSampleWeight (S : Type*) [Fintype S] (_ : S) : ℝ := (Fintype.card S : ℝ)⁻¹

theorem uniformSampleWeight_nonneg (S : Type*) [Fintype S] (s : S) : 0 ≤ uniformSampleWeight S s := by
  unfold uniformSampleWeight
  positivity

theorem uniformSampleWeight_sum (S : Type*) [Fintype S] [Nonempty S] :
    (∑ s,uniformSampleWeight S s) = 1 := by
  simp only [uniformSampleWeight,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

theorem map_finiteSampleLaw {Ω Y Z S : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [MeasurableSpace Z] [Fintype S] (μ : Measure Ω) (weight : S → ℝ)
    (F : S → Ω → Y) (hF : ∀ s,Measurable (F s)) (J : Y → Z) (hJ : Measurable J) :
    Measure.map J (finiteSampleLaw μ weight F) = finiteSampleLaw μ weight (fun s => J ∘ F s) := by
  rw [finiteSampleLaw,← Measure.mapₗ_apply_of_measurable hJ,map_sum]
  unfold finiteSampleLaw
  apply Finset.sum_congr rfl
  intro s hs
  rw [Measure.mapₗ_apply_of_measurable hJ,Measure.map_smul,Measure.map_map hJ (hF s)]

end GeneralizedBulk.Entropy
