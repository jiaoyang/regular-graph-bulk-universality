import Mathlib

/-! A good event may be pushed to an actual model space without assuming
that its auxiliary spectral choices are functions of that model. -/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.Analysis
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem map_good_image_failure_le (P : Measure X) (f : X → Y) (hf : Measurable f)
    (good : Set X) (himage : MeasurableSet (f '' good)) :
    (P.map f) (f '' good)ᶜ ≤ P goodᶜ := by
  rw [Measure.map_apply hf himage.compl]
  apply measure_mono
  intro x hx hxgood
  exact hx ⟨x,hxgood,rfl⟩

theorem map_good_image_real_failure_le (P : Measure X) [IsFiniteMeasure P] (f : X → Y) (hf : Measurable f)
    (good : Set X) (himage : MeasurableSet (f '' good)) :
    (P.map f).real (f '' good)ᶜ ≤ P.real goodᶜ :=
  ENNReal.toReal_mono (measure_ne_top _ _) (map_good_image_failure_le P f hf good himage)

end GeneralizedBulk.Analysis
