import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import BourgadeHuang.Particles

/-!
# Point-process and finite-particle foundations

Locally finite integer counting measures, their vague topology, finite factorial
statistics, and finite-particle loop hierarchy assumptions.
-/

noncomputable section
open scoped BigOperators Topology ENNReal CompactlySupported BoundedContinuousFunction
open MeasureTheory Filter

namespace BourgadeHuang

/-- A locally finite counting measure, with multiplicities allowed. Integer values on every
compact set exclude a diffuse component; local finiteness excludes infinite compact counts. -/
structure LocalCountingMeasure where
  measure : Measure ℝ
  locallyFinite : IsLocallyFiniteMeasure measure
  integer_compacts : ∀ K : Set ℝ, IsCompact K → ∃ n : ℕ, measure K = n

instance (ξ : LocalCountingMeasure) : IsLocallyFiniteMeasure ξ.measure := ξ.locallyFinite

/-- The vague topology is the initial topology of the compactly supported continuous tests. -/
instance : TopologicalSpace LocalCountingMeasure :=
  ⨅ f : ℝ →C_c ℝ,
    TopologicalSpace.induced (fun ξ : LocalCountingMeasure => ∫ x, f x ∂ξ.measure)
      inferInstance

instance : MeasurableSpace LocalCountingMeasure := borel LocalCountingMeasure

instance : BorelSpace LocalCountingMeasure := ⟨rfl⟩

/-- Weak convergence of point-process laws for the vague topology, expressed by bounded
continuous real tests. The target measure is an explicit parameter, not constructed here. -/
def VagueLawConverges {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ξ : ℕ → Ω → LocalCountingMeasure) (target : Measure LocalCountingMeasure) : Prop :=
  ∀ F : LocalCountingMeasure →ᵇ ℝ,
    Tendsto (fun N => ∫ ω, F (ξ N ω) ∂μ) atTop (𝓝 (∫ c, F c ∂target))

/-- Ordered factorial statistics count distinct particle labels, even at repeated locations. -/
def factorialStatistic {N q : ℕ} (x : Fin N → ℝ) (φ : (Fin q → ℝ) → ℝ) : ℝ :=
  ∑ a : Fin q → Fin N, if Function.Injective a then φ (fun j => x (a j)) else 0

/-- A simple reference law with intensity `1/π` and finite compact-count moments. -/
structure TargetProcess where
  law : Measure LocalCountingMeasure
  probability : IsProbabilityMeasure law
  simple : ∀ᵐ ξ ∂law, ∀ x : ℝ, ξ.measure {x} ≤ 1
  count_moments_integrable : ∀ a b : ℝ, ∀ q : ℕ,
    Integrable (fun ξ => (ξ.measure (Set.Icc a b)).toReal ^ q) law
  intensity : ∀ a b : ℝ, a ≤ b →
    (∫ ξ, (ξ.measure (Set.Icc a b)).toReal ∂law) = (b - a) / Real.pi

/-- For a simple target, restriction of its tensor powers to distinct locations is its
factorial measure. Finite-N statistics above instead exclude repeated *labels*. -/
def TargetProcess.factorialExpectation (target : TargetProcess) (q : ℕ)
    (φ : (Fin q → ℝ) → ℝ) : ℝ :=
  ∫ ξ, (∫ x : Fin q → ℝ, if Function.Injective x then φ x else 0
    ∂Measure.pi (fun _ : Fin q => ξ.measure)) ∂target.law

/-- Stochastic domination using probability in ENNReal and an eventually positive scale. -/
def StochasticallyDominated {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Ω → ℝ) (a : ℕ → ℝ) : Prop :=
  (∀ᶠ N in atTop, 0 < a N) ∧ ∀ ε D : ℝ, 0 < ε → 0 < D →
    ∀ᶠ N in atTop,
      μ {ω | |A N ω| > (N : ℝ) ^ ε * a N} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- The finite mixed-half-plane hierarchy with `n` auxiliary parameters, hence
length `n+1`. `loopIntegrand` uses its finite-sum analytic extension on every diagonal. -/
def ApproximateHierarchy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (β : Beta) (x : (N : ℕ) → Ω → Fin N → ℝ) (center : ℝ) : Prop :=
  ∀ n : ℕ, ∀ K : Set ℂ, IsCompact K → (∀ w ∈ K, w.im ≠ 0) →
    ∀ c : ℝ, 0 < c → c < 1 / 6 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N in atTop, ∀ w ∈ K, ∀ aux : Fin n → ℂ,
        (∀ a, aux a ∈ K) →
        ‖∫ ω, loopIntegrand β (x N ω) center w aux ∂μ‖ ≤ C * (N : ℝ) ^ (-c)

/-- Explicit integrability avoids exploiting the totalized Bochner integral's default value
on non-integrable functions. -/
def ResolventMoments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x : (N : ℕ) → Ω → Fin N → ℝ) (center : ℝ) : Prop :=
  ∀ (N : ℕ) (w : ℂ), w.im ≠ 0 → ∀ q : ℕ,
    Integrable (fun ω => ‖microscopicResolvent (x N ω) center w‖ ^ q) μ

def HierarchyIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (β : Beta) (x : (N : ℕ) → Ω → Fin N → ℝ) (center : ℝ) : Prop :=
  ∀ (N n : ℕ) (w : ℂ), w.im ≠ 0 → ∀ aux : Fin n → ℂ, (∀ a, (aux a).im ≠ 0) →
    Integrable (fun ω => loopIntegrand β (x N ω) center w aux) μ

/-- Uniform compact-count moments, including integrability. -/
def UniformCountMoments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ξ : ℕ → Ω → LocalCountingMeasure) : Prop :=
  ∀ a b : ℝ, ∀ q : ℕ,
    (∀ N, Integrable (fun ω => ((ξ N ω).measure (Set.Icc a b)).toReal ^ q) μ) ∧
    ∃ C : ℝ, ∀ N,
      (∫ ω, ((ξ N ω).measure (Set.Icc a b)).toReal ^ q ∂μ) ≤ C

end BourgadeHuang
