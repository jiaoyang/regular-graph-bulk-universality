import GeneralizedBulk.Entropy.CountableLaw

/-! Literal law masses commute with measurable maps. -/
noncomputable section
open MeasureTheory

namespace GeneralizedBulk.Entropy

theorem lawMass_map {Ω Y B : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [MeasurableSpace B] [MeasurableSingletonClass B] (μ : Measure Ω)
    (F : Ω → Y) (hF : Measurable F) (J : Y → B) (hJ : Measurable J) (b : B) :
    lawMass (Measure.map F μ) J b = lawMass μ (J ∘ F) b := by
  unfold lawMass Measure.real
  rw [Measure.map_apply hF (hJ (measurableSet_singleton b))]
  rfl

end GeneralizedBulk.Entropy
