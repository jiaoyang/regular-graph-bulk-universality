import BourgadeHuang.RationalEdge.GaussianEdgeLimit
import BourgadeHuang.RationalEdge.PaperAssumptions

/-!
# Bourgade--Huang, Theorem 1.12

The full event-restricted, moment-weighted approximate edge hierarchy implies
vague convergence to Airy beta for every positive rational beta. The proof
internally supplies tightness, exponential moments, the exact limiting
hierarchy, rational-coupling uniqueness, and the full Gaussian edge target.
No moments outside the good events or error rates are assumed.
-/
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge

/-- The criterion also gives convergence of the anchor and counting state jointly. -/
theorem bourgade_huang_theorem_1_12_anchored
    (β : ℚ) (hβ : 0<β)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ→Ω→AnchoredCountingState) (A : ℕ→Set Ω)
    (h : EventWeightedHierarchy μ (β:ℝ) X A) :
    WeakLawConverges μ X (airyBetaAnchoredLaw β hβ : Measure AnchoredCountingState) ∧
      VagueLawConverges μ (fun N ω => (X N ω).val.1)
        (airyBetaLaw β hβ : Measure LocalCountingMeasure) :=
  h.converges_of_unique (airyBetaAnchoredLaw β hβ) (airyBetaAnchoredLaw_unique β hβ)

/-- Bourgade--Huang Theorem 1.12: the full mixed edge hierarchy (1.6) implies
vague convergence in distribution to the Airy-beta point process. -/
theorem bourgade_huang_theorem_1_12
    (β : ℚ) (hβ : 0<β)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ→Ω→AnchoredCountingState) (A : ℕ→Set Ω)
    (h : EventWeightedHierarchy μ (β:ℝ) X A) :
    VagueLawConverges μ (fun N ω => (X N ω).val.1)
      (airyBetaLaw β hβ : Measure LocalCountingMeasure) :=
  (bourgade_huang_theorem_1_12_anchored β hβ μ X A h).2

/-- Every assumption is exposed, using natural moments at the anchor. -/
theorem bourgade_huang_theorem_1_12_unbundled
    (β : ℚ) (hβ : 0<β)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ→Ω→AnchoredCountingState) (A : ℕ→Set Ω)
    (hX : ∀N,Measurable (X N)) (hA : ∀N,MeasurableSet (A N))
    (hprob : Tendsto (fun N => μ.real (A N)ᶜ) atTop (𝓝 0))
    (hm : ∀N q : ℕ,Integrable (fun ω => ‖(X N ω).val.2‖^q) (μ.restrict (A N)))
    (herr : ∀n : ℕ,∀K : Set ℂ,IsCompact K → (∀z∈K,z.im≠0) →
      ∃ε : ℕ→ℝ,Tendsto ε atTop (𝓝 0) ∧ (∀N,0≤ε N) ∧
        ∀N (w : ℂ),w∈K → ∀aux : Fin n→ℂ,(∀j,aux j∈K) →
          ‖∫ω,loopIntegrand (β:ℝ) (X N ω) w aux ∂(μ.restrict (A N))‖ ≤
            ε N*(1+∫ω,coordinateMaximum (X N ω) w aux^(n+2) ∂(μ.restrict (A N)))) :
    VagueLawConverges μ (fun N ω => (X N ω).val.1)
      (airyBetaLaw β hβ : Measure LocalCountingMeasure) :=
  bourgade_huang_theorem_1_12 β hβ μ X A ⟨hX,hA,hprob,hm,herr⟩

/-- The literal real-order event moments and uniform weighted error of (1.6). -/
theorem bourgade_huang_theorem_1_12_paper
    (β : ℚ) (hβ : 0<β)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ→Ω→AnchoredCountingState) (A : ℕ→Set Ω)
    (hX : ∀N,Measurable (X N)) (hA : ∀N,MeasurableSet (A N))
    (hprob : Tendsto (fun N => μ.real (A N)ᶜ) atTop (𝓝 0))
    (hm : ∀N,∀q : ℝ,0<q → ∀w : ℂ,w.im≠0 →
      Integrable (fun ω => ‖anchoredNevanlinna (X N ω) w‖^q) (μ.restrict (A N)))
    (herr : ∀n : ℕ,∀K : Set ℂ,IsCompact K → (∀z∈K,z.im≠0) →
      ∃ε : ℕ→ℝ,Tendsto ε atTop (𝓝 0) ∧ (∀N,0≤ε N) ∧
        ∀N (w : ℂ),w∈K → ∀aux : Fin n→ℂ,(∀j,aux j∈K) →
          ‖∫ω,loopIntegrand (β:ℝ) (X N ω) w aux ∂(μ.restrict (A N))‖ ≤
            ε N*(1+∫ω,coordinateMaximum (X N ω) w aux^(n+2) ∂(μ.restrict (A N)))) :
    VagueLawConverges μ (fun N ω => (X N ω).val.1)
      (airyBetaLaw β hβ : Measure LocalCountingMeasure) :=
  bourgade_huang_theorem_1_12_unbundled β hβ μ X A hX hA hprob
    (event_anchor_moments_of_paper μ X A hm) herr

end BourgadeHuang.RationalEdge
