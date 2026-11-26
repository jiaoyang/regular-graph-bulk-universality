import Mathlib

/-! Vanishing exceptional probabilities are preserved by finite common events. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Analysis
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

theorem intersection_failure_tendsto_zero (A B : ℕ → Set Ω)
    (hA : Tendsto (fun n => P.real (A n)ᶜ) atTop (nhds 0))
    (hB : Tendsto (fun n => P.real (B n)ᶜ) atTop (nhds 0)) :
    Tendsto (fun n => P.real (A n ∩ B n)ᶜ) atTop (nhds 0) := by
  apply squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_)
    (by simpa only [zero_add] using hA.add hB)
  rw [Set.compl_inter]
  exact measureReal_union_le _ _

end GeneralizedBulk.Analysis
