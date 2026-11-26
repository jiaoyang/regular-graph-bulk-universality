import BourgadeHuang.RationalEdge.GaussianEdgeLimit
import BourgadeHuang.RationalEdge.PaperAssumptions

/-!
# Bourgade--Huang, Theorem 1.11

The exact edge loop hierarchy identifies the Airy-beta pole law for every
positive rational beta. Ordinary anchor moments suffice: exponential-square
integrability, local laws, and uniqueness are proved internally. The target
is the full limit of the genuine normalized Gaussian beta edge ensembles.
-/
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge

/-- The exact hierarchy identifies the complete anchored state law. -/
theorem bourgade_huang_theorem_1_11_anchored
    (β : ℚ) (hβ : 0<β)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → AnchoredCountingState) (h : EdgeLoopEquations μ (β:ℝ) X) :
    probabilityLaw μ X h.measurable_state = airyBetaAnchoredLaw β hβ :=
  airyBetaAnchoredLaw_unique β hβ
    (probabilityLaw μ X h.measurable_state) h.exact_law h.exponentialSquare_law

/-- Bourgade--Huang Theorem 1.11: the pole counting measure has the Airy-beta
law, with no extra uniqueness or exponential-integrability assumption. -/
theorem bourgade_huang_theorem_1_11
    (β : ℚ) (hβ : 0<β)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → AnchoredCountingState) (h : EdgeLoopEquations μ (β:ℝ) X) :
    Measure.map (fun ω => (X ω).val.1) μ =
      (airyBetaLaw β hβ : Measure LocalCountingMeasure) :=
  (h.law_eq_of_unique (airyBetaAnchoredLaw β hβ) (airyBetaAnchoredLaw_unique β hβ)).2

/-- All hypotheses exposed, using the weaker sufficient natural anchor moments. -/
theorem bourgade_huang_theorem_1_11_unbundled
    (β : ℚ) (hβ : 0<β)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → AnchoredCountingState) (hX : Measurable X)
    (hm : ∀q : ℕ, Integrable (fun ω => ‖(X ω).val.2‖^q) μ)
    (hh : ∀n : ℕ, ∀w : ℂ, w.im≠0 →
      ∀aux : Fin n→ℂ, (∀j,(aux j).im≠0) →
        (∫ω,loopIntegrand (β:ℝ) (X ω) w aux ∂μ)=0) :
    Measure.map (fun ω => (X ω).val.1) μ =
      (airyBetaLaw β hβ : Measure LocalCountingMeasure) :=
  bourgade_huang_theorem_1_11 β hβ μ X ⟨hX,hm,hh⟩

/-- The literal real-order moment formulation of Assumption 1.10 and (1.5). -/
theorem bourgade_huang_theorem_1_11_paper
    (β : ℚ) (hβ : 0<β)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → AnchoredCountingState) (hX : Measurable X)
    (hm : ∀q : ℝ, 0<q → ∀w : ℂ, w.im≠0 →
      Integrable (fun ω => ‖anchoredNevanlinna (X ω) w‖^q) μ)
    (hh : ∀n : ℕ, ∀w : ℂ, w.im≠0 →
      ∀aux : Fin n→ℂ, (∀j,(aux j).im≠0) →
        (∫ω,loopIntegrand (β:ℝ) (X ω) w aux ∂μ)=0) :
    Measure.map (fun ω => (X ω).val.1) μ =
      (airyBetaLaw β hβ : Measure LocalCountingMeasure) :=
  bourgade_huang_theorem_1_11 β hβ μ X
    (EdgeLoopEquations.of_paper μ (β:ℝ) X hX hm hh)

end BourgadeHuang.RationalEdge
