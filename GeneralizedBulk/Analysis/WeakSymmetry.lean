import GeneralizedBulk.ExternalInputs

/-!
# Symmetry passes from approximate finite laws to their weak limits

Bounded continuous tests identify finite Borel measures. Product laws are then
identified by finite cylinders, so an uncountable spectral index requires no
metrizability assumption on the entire product field space.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Analysis

/-- Vanishing bounded-test discrepancy passes a continuous symmetry to a
weak limit. This is a theorem of weak convergence, not a stationary law input. -/
theorem map_eq_of_weakLimit_approximate_symmetry
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [HasOuterApproxClosed E]
    (mu : ℕ → Measure E) (nu : Measure E) [IsFiniteMeasure nu]
    (q : E → E) (hq : Continuous q) (epsilon : ℕ → ℝ)
    (hepsilon : Tendsto epsilon atTop (𝓝 0))
    (hweak : External.WeakLawConverges mu nu)
    (happrox : ∀ n : ℕ, ∀ f : BoundedContinuousFunction E ℝ,
      ‖(∫ x, f (q x) ∂mu n) - (∫ x, f x ∂mu n)‖ ≤ ‖f‖ * epsilon n) :
    Measure.map q nu = nu := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hq.measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  have hleft := hweak (f.compContinuous ⟨q, hq⟩)
  have hright := hweak f
  have hlimit := hleft.sub hright
  have herror : Tendsto (fun n => ‖f‖ * epsilon n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hepsilon
  have hzero := squeeze_zero_norm (fun n => happrox n f) herror
  exact sub_eq_zero.mp (tendsto_nhds_unique hlimit hzero)

/-- Equality of every finite-dimensional marginal identifies an arbitrary
product law. The spectral index need not be countable. -/
theorem measure_eq_of_finite_marginals
    {I E : Type*} [MeasurableSpace E]
    (mu nu : Measure (I → E)) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (h : ∀ s : Finset I, Measure.map s.restrict mu = Measure.map s.restrict nu) : mu = nu := by
  let P := fun s : Finset I => Measure.map s.restrict mu
  have hmu : IsProjectiveLimit mu P := fun _ => rfl
  have hnu : IsProjectiveLimit nu P := fun s => (h s).symm
  exact hmu.unique hnu

/-- A pointwise continuous symmetry passes to an uncountably indexed product
field from finite-dimensional weak convergence and finite test discrepancies. -/
theorem pi_map_eq_of_finite_weak_limits
    {I E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [TopologicalSpace.PseudoMetrizableSpace E] [SecondCountableTopology E]
    (mu : ℕ → Measure (I → E)) (nu : Measure (I → E)) [IsFiniteMeasure nu]
    (q : E → E) (hq : Continuous q) (epsilon : ℕ → ℝ)
    (hepsilon : Tendsto epsilon atTop (𝓝 0))
    (hweak : ∀ s : Finset I, External.WeakLawConverges
      (fun n => Measure.map s.restrict (mu n)) (Measure.map s.restrict nu))
    (happrox : ∀ s : Finset I, ∀ n : ℕ, ∀ f : BoundedContinuousFunction (s → E) ℝ,
      ‖(∫ x, f (fun i => q (x i)) ∂Measure.map s.restrict (mu n)) -
        (∫ x, f x ∂Measure.map s.restrict (mu n))‖ ≤ ‖f‖ * epsilon n) :
    Measure.map (fun x : I → E => fun i => q (x i)) nu = nu := by
  have hQ : Measurable (fun x : I → E => fun i => q (x i)) :=
    measurable_pi_lambda _ (fun i => hq.measurable.comp (measurable_pi_apply i))
  apply measure_eq_of_finite_marginals
  intro s
  have hs : Measurable (s.restrict : (I → E) → (s → E)) := measurable_pi_lambda _ (fun i => measurable_pi_apply (i : I))
  have hqS : Continuous (fun x : s → E => fun i => q (x i)) :=
    continuous_pi (fun i => hq.comp (continuous_apply i))
  have hsym := map_eq_of_weakLimit_approximate_symmetry
    (fun n => Measure.map s.restrict (mu n)) (Measure.map s.restrict nu)
    (fun x : s → E => fun i => q (x i)) hqS epsilon hepsilon (hweak s) (happrox s)
  rw [Measure.map_map hs hQ]
  rw [Measure.map_map hqS.measurable hs] at hsym
  exact hsym

end GeneralizedBulk.Analysis
