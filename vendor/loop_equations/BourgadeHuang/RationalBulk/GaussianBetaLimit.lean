import BourgadeHuang.RationalBulk.GaussianFiniteLoop
import BourgadeHuang.RationalBulk.GaussianBetaReference
import BourgadeHuang.RationalBulk.HierarchyUniqueness

/-! Construction of actual Gaussian beta bulk reference laws. Sine terminology
is reserved for positive rational beta, where hierarchy uniqueness identifies
the full Gaussian bulk limit. -/
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem gaussianBeta_eventWeightedHierarchy (β : ℝ) (hβ : 0 < β) :
    EventWeightedHierarchy (gaussianBetaProduct β hβ) β gaussianBetaState
      (fun _ => Set.univ) :=
  gaussianBeta_eventWeighted_of_finite_identity β hβ
    (gaussianBeta_finite_loop_identity β hβ)

theorem gaussianBeta_vanishingHierarchy (β : ℝ) (hβ : 0 < β) :
    VanishingHierarchy (gaussianBetaProduct β hβ) β gaussianBetaState := by
  intro n w hw aux ha
  simpa only [Measure.restrict_univ] using
    (gaussianBeta_eventWeightedHierarchy β hβ).restricted_loop_tendsto hw ha

theorem exists_gaussianBetaReference (β : ℝ) (hβ : 0 < β) :
    Nonempty (GaussianBetaReference β hβ) :=
  exists_gaussianBetaReference_of_finite_identity β hβ
    (gaussianBeta_finite_loop_identity β hβ)

/-- An actual subsequential limit of the explicitly normalized Gaussian beta
particle ensembles; existence and its hierarchy are proved above. -/
def gaussianBetaReference (β : ℝ) (hβ : 0 < β) : GaussianBetaReference β hβ :=
  Classical.choice (exists_gaussianBetaReference β hβ)

/-- The anchored law selected from the actual Gaussian beta bulk limit.
The full-sequence and uniqueness theorems establish choice-independence. -/
def sineBetaAnchoredLaw (β : ℚ) (hβ : 0 < β) : ProbabilityMeasure AnchoredCountingState :=
  (gaussianBetaReference (β : ℝ) (by exact_mod_cast hβ)).law

/-- Sine beta with the article's intensity convention, defined from the actual
Gaussian beta bulk particles, and only for positive rational beta here. -/
def sineBetaLaw (β : ℚ) (hβ : 0 < β) : ProbabilityMeasure LocalCountingMeasure :=
  anchoredCountingLaw (sineBetaAnchoredLaw β hβ)

theorem sineBetaAnchoredLaw_exactHierarchy (β : ℚ) (hβ : 0 < β) :
    ExactHierarchy (sineBetaAnchoredLaw β hβ : Measure AnchoredCountingState) (β : ℝ) :=
  (gaussianBetaReference (β : ℝ) (by exact_mod_cast hβ)).hierarchy

theorem sineBetaAnchoredLaw_exponentialSquare (β : ℚ) (hβ : 0 < β) :
    ∃ a : ℝ, 0 < a ∧ Integrable
      (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2))
      (sineBetaAnchoredLaw β hβ : Measure AnchoredCountingState) :=
  (gaussianBetaReference (β : ℝ) (by exact_mod_cast hβ)).exponentialSquare

/-- This is a subsequence of the genuine Gaussian beta particles, with the
microscopic density exp(−beta sum(x_i²)/(4N)) times Vandermonde^beta. -/
theorem sineBetaLaw_gaussian_subsequence (β : ℚ) (hβ : 0 < β) :
    ∃ r : ℕ → ℕ, StrictMono r ∧
      VagueLawConverges (gaussianBetaProduct (β : ℝ) (by exact_mod_cast hβ))
        (fun N ω => (gaussianBetaState (r N) ω).val.1)
        (sineBetaLaw β hβ : Measure LocalCountingMeasure) := by
  let R := gaussianBetaReference (β : ℝ) (by exact_mod_cast hβ)
  exact ⟨R.subsequence, R.strictMono, R.vague_subsequence⟩

/-- The Sine law is characterized by the exact rational-beta hierarchy. -/
theorem sineBetaAnchoredLaw_unique (β : ℚ) (hβ : 0 < β)
    (ν : ProbabilityMeasure AnchoredCountingState)
    (hν : ExactHierarchy (ν : Measure AnchoredCountingState) (β : ℝ))
    (hE : ∃ a : ℝ, 0 < a ∧ Integrable
      (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2))
      (ν : Measure AnchoredCountingState)) : ν = sineBetaAnchoredLaw β hβ := by
  obtain ⟨a,ha,he⟩ := hE
  obtain ⟨b,hb,hf⟩ := sineBetaAnchoredLaw_exponentialSquare β hβ
  exact anchored_law_eq_of_exactHierarchy_rational β hβ ν (sineBetaAnchoredLaw β hβ)
    hν (sineBetaAnchoredLaw_exactHierarchy β hβ) ha hb he hf

/-- Full Gaussian beta convergence, not merely a chosen subsequence. -/
theorem gaussianBeta_full_convergence (β : ℚ) (hβ : 0 < β) :
    WeakLawConverges (gaussianBetaProduct (β : ℝ) (by exact_mod_cast hβ))
      gaussianBetaState (sineBetaAnchoredLaw β hβ : Measure AnchoredCountingState) := by
  exact (gaussianBetaReference (β : ℝ) (by exact_mod_cast hβ)).full_convergence_of_uniqueness
    (gaussianBeta_vanishingHierarchy (β : ℝ) (by exact_mod_cast hβ))
    (sineBetaAnchoredLaw_unique β hβ)

/-- The actual full Gaussian beta particle bulk limit is the declared Sine law. -/
theorem gaussianBeta_vague_full_convergence (β : ℚ) (hβ : 0 < β) :
    VagueLawConverges (gaussianBetaProduct (β : ℝ) (by exact_mod_cast hβ))
      (fun N ω => (gaussianBetaState N ω).val.1)
      (sineBetaLaw β hβ : Measure LocalCountingMeasure) := by
  exact anchored_sequence_vagueLawConverges
    (gaussianBetaProduct (β : ℝ) (by exact_mod_cast hβ)) gaussianBetaState
    (sineBetaAnchoredLaw β hβ) (gaussianBeta_full_convergence β hβ)

/-- Any Gaussian beta reference choice gives the same rational-beta law. -/
theorem gaussianBetaReference_law_unique (β : ℚ) (hβ : 0 < β)
    (R : GaussianBetaReference (β : ℝ) (by exact_mod_cast hβ)) :
    R.law = sineBetaAnchoredLaw β hβ :=
  sineBetaAnchoredLaw_unique β hβ R.law R.hierarchy R.exponentialSquare

end BourgadeHuang.RationalBulk
