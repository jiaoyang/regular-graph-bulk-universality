import BourgadeHuang.RationalEdge.CharacterizationReduction
import BourgadeHuang.RationalEdge.EventLawTransfer

/-! The full event and moment-weighted convergence reduction of Theorem 1.12.
The rational uniqueness proof discharges the explicitly isolated uniqueness
premise below; no error rate or uniform moment estimate is an input. -/
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge

theorem EventWeightedHierarchy.converges_of_unique
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {β : ℝ} {X : ℕ → Ω → AnchoredCountingState} {A : ℕ → Set Ω}
    (h : EventWeightedHierarchy μ β X A)
    (ν : ProbabilityMeasure AnchoredCountingState)
    (hunique : ∀ ρ : ProbabilityMeasure AnchoredCountingState,
      ExactHierarchy (ρ : Measure AnchoredCountingState) β →
      (∃ a : ℝ, 0 < a ∧ Integrable
        (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2))
          (ρ : Measure AnchoredCountingState)) → ρ = ν) :
    WeakLawConverges μ X (ν : Measure AnchoredCountingState) ∧
      VagueLawConverges μ (fun N ω => (X N ω).val.1)
        (anchoredCountingLaw ν : Measure LocalCountingMeasure) := by
  have hw : WeakLawConverges μ X (ν : Measure AnchoredCountingState) := by
    apply h.weakLawConverges_of_clip
    exact weakLawConverges_of_vanishingHierarchy_and_uniqueness μ β
      (fun N => clipState (A N) (X N))
      (fun N => measurable_clipState (h.measurable_event N) (h.measurable_state N))
      (fun N q => integrable_clipState_moments μ (h.measurable_event N) (X N)
        (h.moments N) q)
      h.vanishing_clip ν hunique
  exact ⟨hw, anchored_sequence_vagueLawConverges μ X ν hw⟩

end BourgadeHuang.RationalEdge
