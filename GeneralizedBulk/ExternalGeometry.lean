import GeneralizedBulk.Graph.OrientedEdgeSampling
import GeneralizedBulk.Graph.FiniteTreeBall

/-!
# The geometric part of the external HY regular-graph input

This is only the literal fixed-radius local-tree statement. It supplies no
spectral multiplier, marked-series, concentration, or remote-tail conclusion.
Those deterministic and analytical consequences are proved in graph modules.
-/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.External

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The actual finite graph ball, using extended graph distance so different
components are handled correctly. -/
def spectralGraphBall (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)
    (root : Fin (N n)) (R : ℕ) : Set (Fin (N n)) :=
  {v | (D.simpleGraph n ω).edist root v ≤ (R : ℕ∞)}

/-- The fixed-radius neighborhood has no cycle. This is a statement only
about the actual finite graph induced on that ball. -/
def HasTreeNeighborhood (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)
    (root : Fin (N n)) (R : ℕ) : Prop :=
  ((D.simpleGraph n ω).induce (spectralGraphBall D n ω root R)).IsAcyclic

/-- HY's separate local geometry event, supplied for every fixed radius.
Its exceptional-root proportion is at most `N^(-1/2)` on a polynomially
probable graph event, with constants permitted to depend on the radius.
The `edgeIso` field is the equivalent rooted-edge formulation: a radius
`R+1` acyclic neighborhood in a regular graph contains the canonical radius
`R` edge ball, with each endpoint's `d-1` outward branches independently
enumerated. The reference graph is the explicit finite word tree from
`Graph/FiniteTreeBall`, not an unspecified common walk-count conclusion. -/
structure HYGeometryInput (D : RegularSpectralData d N Ω)
    (P : Measure Ω) [IsProbabilityMeasure P] where
  events : ℕ → PolynomialGoodEvents P N
  badRoots : ∀ R n, Ω → Finset (Fin (N n))
  bad_count : ∀ R n, (events R).threshold ≤ n → ∀ ω ∈ (events R).good n,
    ((badRoots R n ω).card : ℝ) ≤ (N n : ℝ) ^ (1 / 2 : ℝ)
  tree : ∀ R n, (events R).threshold ≤ n → ∀ ω ∈ (events R).good n,
    ∀ root : Fin (N n), root ∉ badRoots R n ω → HasTreeNeighborhood D n ω root R
  edgeIso : ∀ R n, (events R).threshold ≤ n → ∀ ω ∈ (events R).good n,
    ∀ root : Fin (N n), root ∉ badRoots R n ω → ∀ j : Fin d,
      Nonempty (Graph.RootedEdgeBallIso (D.simpleGraph n ω) root (D.neighbor n ω root j) d R)

end GeneralizedBulk.External
