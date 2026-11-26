import BourgadeHuang.RationalEdge.GaussianEdgeTarget
import BourgadeHuang.RationalEdge.HierarchyUniqueness

/-! Full Gaussian beta soft-edge convergence for every positive rational
beta. The reference was constructed from actual finite Gaussian particle
laws; proved hierarchy uniqueness identifies the full sequence and makes
the selected reference independent of subsequence and choice. -/
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk

/-- The edge hierarchy uniquely characterizes the actual Gaussian edge law. -/
theorem airyBetaAnchoredLaw_unique (β : ℚ) (hβ : 0<β)
    (ν : ProbabilityMeasure AnchoredCountingState)
    (hν : RationalEdge.ExactHierarchy (ν : Measure AnchoredCountingState) (β:ℝ))
    (hE : ∃a : ℝ,0<a ∧ Integrable
      (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2))
      (ν : Measure AnchoredCountingState)) : ν=airyBetaAnchoredLaw β hβ := by
  obtain ⟨a,ha,he⟩ := hE
  obtain ⟨b,hb,hf⟩ := airyBetaAnchoredLaw_exponentialSquare β hβ
  exact RationalEdge.anchored_law_eq_of_exactHierarchy_rational β hβ ν
    (airyBetaAnchoredLaw β hβ) hν (airyBetaAnchoredLaw_exactHierarchy β hβ) ha hb he hf

/-- The genuine Gaussian beta edge ensembles converge along the full sequence. -/
theorem gaussianBetaEdge_full_convergence (β : ℚ) (hβ : 0<β) :
    WeakLawConverges (gaussianBetaProduct (β:ℝ) (by exact_mod_cast hβ))
      gaussianBetaEdgeState (airyBetaAnchoredLaw β hβ : Measure AnchoredCountingState) :=
  (gaussianBetaEdgeReference (β:ℝ) (by exact_mod_cast hβ)).full_convergence_of_uniqueness
    (airyBetaAnchoredLaw_unique β hβ)

/-- The Airy-beta target is the actual full Gaussian beta edge particle limit. -/
theorem gaussianBetaEdge_vague_full_convergence (β : ℚ) (hβ : 0<β) :
    VagueLawConverges (gaussianBetaProduct (β:ℝ) (by exact_mod_cast hβ))
      (fun N ω => (gaussianBetaEdgeState N ω).val.1)
      (airyBetaLaw β hβ : Measure LocalCountingMeasure) :=
  anchored_sequence_vagueLawConverges
    (gaussianBetaProduct (β:ℝ) (by exact_mod_cast hβ)) gaussianBetaEdgeState
    (airyBetaAnchoredLaw β hβ) (gaussianBetaEdge_full_convergence β hβ)

/-- Every reference selected from the genuine Gaussian beta edge sequence has
this same law. -/
theorem gaussianBetaEdgeReference_law_unique (β : ℚ) (hβ : 0<β)
    (R : GaussianBetaEdgeReference (β:ℝ) (by exact_mod_cast hβ)) :
    R.law=airyBetaAnchoredLaw β hβ :=
  airyBetaAnchoredLaw_unique β hβ R.law R.hierarchy R.exponentialSquare

end BourgadeHuang.RationalEdge
