import Mathlib

/-!
# Concrete probability-law definitions

The BS input used later is an ordinary argument of the theorems, not a new
axiom. Centered Gaussianity leaves the covariance unspecified; normalization
and independence must be proved from finite empirical moments.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace GaussianWave

/-- Weak convergence against all real bounded continuous functions. -/
def WeakLawConverges {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : ℕ → Measure E) (ν : Measure E) : Prop :=
  ∀ f : BoundedContinuousFunction E ℝ,
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν))

def finiteLinearForm {ι : Type*} [Fintype ι] (t x : ι → ℝ) : ℝ :=
  ∑ i, t i * x i

def finiteCovarianceQuadratic {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (t : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, t i * C i j * t j

/-- The characteristic function of a centered Gaussian with stated covariance.
This definition includes degenerate Gaussian laws. -/
def HasGaussianCovariance {ι : Type*} [Fintype ι]
    (ν : Measure (ι → ℝ)) (C : Matrix ι ι ℝ) : Prop :=
  ∀ t : ι → ℝ,
    (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂ν) =
      Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic C t) : ℂ)

/-- Qualitative Gaussianity, with no claimed variance-one normalization. -/
def CenteredGaussianLaw {ι : Type*} [Fintype ι] (ν : Measure (ι → ℝ)) : Prop :=
  IsProbabilityMeasure ν ∧ ∃ C : Matrix ι ι ℝ,
    (∀ i j, C i j = C j i) ∧
    (∀ t, 0 ≤ finiteCovarianceQuadratic C t) ∧ HasGaussianCovariance ν C

theorem weakLawConverges_iff_probability_tendsto
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (μ : ℕ → ProbabilityMeasure E)
    (ν : ProbabilityMeasure E) :
    WeakLawConverges (fun n => (μ n : Measure E)) (ν : Measure E) ↔
      Tendsto μ atTop (𝓝 ν) := by
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.symm

end GaussianWave
