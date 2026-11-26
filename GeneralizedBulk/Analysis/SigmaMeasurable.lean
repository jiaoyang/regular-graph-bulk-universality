import Mathlib

/-! Basic measurable maps for the dependent disjoint union used in mass mixtures. -/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.Analysis

theorem measurable_sigma_mk {I : Type*} {S : I → Type*}
    [∀ i, MeasurableSpace (S i)] (i : I) : Measurable (Sigma.mk i : S i → Sigma S) := by
  intro A hA
  exact (MeasurableSpace.measurableSet_iInf.mp hA) i

theorem measurable_sigma_of_sections {I E : Type*} {S : I → Type*}
    [∀ i, MeasurableSpace (S i)] [MeasurableSpace E] (f : Sigma S → E)
    (hf : ∀ i, Measurable (fun x : S i => f ⟨i,x⟩)) : Measurable f := by
  intro A hA
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro i
  exact hf i hA

end GeneralizedBulk.Analysis
