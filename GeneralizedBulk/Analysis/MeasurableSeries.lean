import Mathlib

/-! Measurable versions of the convergent series used for random scalar states. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators NNReal

namespace GeneralizedBulk.Analysis

theorem measurable_tsum_of_summable
    {ι Ω E : Type*} [Countable ι] [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (F : ι → Ω → E) (hF : ∀ i, Measurable (F i))
    (hs : ∀ ω, Summable (fun i => F i ω)) :
    Measurable (fun ω => ∑' i, F i ω) := by
  classical
  obtain ⟨u, hu⟩ := exists_seq_tendsto (atTop : Filter (Finset ι))
  apply measurable_of_tendsto_metrizable
    (fun n => (u n).measurable_sum (fun i _ => hF i))
  apply tendsto_pi_nhds.mpr
  intro ω
  exact (hs ω).hasSum.comp hu

theorem measurable_nonneg_tsum
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (F : ι → Ω → ℝ) (hF : ∀ i, Measurable (F i)) (hpos : ∀ i ω, 0 ≤ F i ω) :
    Measurable (fun ω => ∑' i, F i ω) := by
  have h : Measurable (fun ω => ∑' i, (⟨F i ω, hpos i ω⟩ : ℝ≥0)) :=
    Measurable.nnreal_tsum (fun i => (hF i).subtype_mk)
  convert h.coe_nnreal_real using 1
  funext ω
  exact (NNReal.coe_tsum (f := fun i => (⟨F i ω, hpos i ω⟩ : ℝ≥0))).symm

end GeneralizedBulk.Analysis
