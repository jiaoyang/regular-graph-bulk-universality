import GeneralizedBulk.Analysis.AnchoredCompactness
import GeneralizedBulk.Analysis.SubsequenceIdentification

/-! Once every anchored subsequential limit has its identified counting law,
the actual whole sequence of counting laws converges. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology ENNReal
namespace GeneralizedBulk.Counting
open Analysis

theorem countingLaw_converges_of_anchor_tails_and_limit_identification
    (laws : ℕ → ProbabilityMeasure AnchoredCountingState)
    (target : Measure LocalCountingMeasure)
    (htail : ∀ ε : ℝ≥0∞,0 < ε → ∃ B : ℝ,∀ n,
      (laws n : Measure AnchoredCountingState) {s | B < ‖s.val.2‖} ≤ ε)
    (hidentify : ∀ (r : ℕ → ℕ),StrictMono r →
      ∀ ν : ProbabilityMeasure AnchoredCountingState,
      External.WeakLawConverges (fun n => (laws (r n) : Measure AnchoredCountingState)) ν →
      Measure.map (fun s : AnchoredCountingState => s.val.1) ν=target) :
    External.WeakLawConverges
      (fun n => Measure.map (fun s : AnchoredCountingState => s.val.1) (laws n)) target := by
  apply weakLaw_marginal_of_subsequence_identification
    (fun n => (laws n : Measure AnchoredCountingState)) target
    (fun s : AnchoredCountingState => s.val.1) (continuous_fst.comp continuous_subtype_val)
  intro r hr
  have hrtail : ∀ ε : ℝ≥0∞,0 < ε → ∃ B : ℝ,∀ n,
      (laws (r n) : Measure AnchoredCountingState) {s | B < ‖s.val.2‖} ≤ ε := by
    intro ε hε
    obtain ⟨B,hB⟩ := htail ε hε
    exact ⟨B,fun n => hB (r n)⟩
  obtain ⟨ν,t,ht,hweak⟩ := anchored_laws_subsequence_of_uniform_anchor_tails (laws ∘ r) hrtail
  have hw : External.WeakLawConverges
      (fun n => (laws (r (t n)) : Measure AnchoredCountingState)) ν := by
    intro F
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak F
  exact ⟨t,ν,ht,hw,hidentify (r ∘ t) (hr.comp ht) ν hw⟩

end GeneralizedBulk.Counting
