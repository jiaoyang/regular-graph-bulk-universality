import BourgadeHuang.RationalEdge.GaussianEdgeReference

/-! The actual Gaussian beta soft-edge reference measure. Full-sequence
identification is provided in GaussianEdgeLimit after rational uniqueness. -/
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk

/-- Anchored measure selected from the genuine Gaussian beta soft-edge ensembles.
Its uniqueness and full-sequence interpretation are established in GaussianEdgeLimit. -/
def airyBetaAnchoredLaw (β : ℚ) (hβ : 0<β) : ProbabilityMeasure AnchoredCountingState :=
  (gaussianBetaEdgeReference (β:ℝ) (by exact_mod_cast hβ)).law

/-- Reflected Airy-beta candidate with the standard edge spacing convention.
The actual full-limit theorem, not this definition alone, identifies the target. -/
def airyBetaLaw (β : ℚ) (hβ : 0<β) : ProbabilityMeasure LocalCountingMeasure :=
  anchoredCountingLaw (airyBetaAnchoredLaw β hβ)

theorem airyBetaAnchoredLaw_exactHierarchy (β : ℚ) (hβ : 0<β) :
    RationalEdge.ExactHierarchy (airyBetaAnchoredLaw β hβ : Measure AnchoredCountingState) (β:ℝ) :=
  (gaussianBetaEdgeReference (β:ℝ) (by exact_mod_cast hβ)).hierarchy

theorem airyBetaAnchoredLaw_exponentialSquare (β : ℚ) (hβ : 0<β) :
    ∃a : ℝ, 0<a ∧ Integrable
      (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2))
      (airyBetaAnchoredLaw β hβ : Measure AnchoredCountingState) :=
  (gaussianBetaEdgeReference (β:ℝ) (by exact_mod_cast hβ)).exponentialSquare

theorem airyBetaLaw_gaussian_subsequence (β : ℚ) (hβ : 0<β) :
    ∃r : ℕ→ℕ, StrictMono r ∧
      VagueLawConverges (gaussianBetaProduct (β:ℝ) (by exact_mod_cast hβ))
        (fun N ω=>(gaussianBetaEdgeState (r N) ω).val.1)
        (airyBetaLaw β hβ : Measure LocalCountingMeasure) := by
  let R := gaussianBetaEdgeReference (β:ℝ) (by exact_mod_cast hβ)
  exact ⟨R.subsequence,R.strictMono,R.vague_subsequence⟩

end BourgadeHuang.RationalEdge
