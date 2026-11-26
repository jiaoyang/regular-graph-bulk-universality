import GeneralizedBulk.Graph.ExteriorSwitching
import GeneralizedBulk.Analysis.WeakSymmetry

/-!
# Recovering full joint exterior symmetry from finite-dimensional weak limits

Finite cylinders determine the product law even though the spectral index is
uncountable. Only the finite-dimensional target of each weak convergence needs
to be metrizable, and all such targets are concrete complex vector spaces.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Graph
open Exterior

abbrev ExteriorState (I : Type*) := (I → ℂ) × (I → Mat)

/-- Bundle scalar and matrix values at each spectral parameter, preserving
their joint law rather than treating them as independent coordinates. -/
def exteriorBundle (I : Type*) : ExteriorState I ≃ᵐ (I → (ℂ × Mat)) where
  toFun x := fun w => (x.1 w, x.2 w)
  invFun x := (fun w => (x w).1, fun w => (x w).2)
  left_inv x := rfl
  right_inv x := by funext w; exact Prod.eta (x w)
  measurable_toFun := measurable_pi_lambda _ (fun w =>
    ((measurable_pi_apply w).comp measurable_fst).prodMk
      ((measurable_pi_apply w).comp measurable_snd))
  measurable_invFun := (measurable_pi_lambda _ (fun w =>
    measurable_fst.comp (measurable_pi_apply w))).prodMk
      (measurable_pi_lambda _ (fun w => measurable_snd.comp (measurable_pi_apply w)))

def exteriorProjection {I : Type*} (s : Finset I) : ExteriorState I → (s → (ℂ × Mat)) :=
  fun x => s.restrict (exteriorBundle I x)

theorem measurable_exteriorProjection {I : Type*} (s : Finset I) :
    Measurable (exteriorProjection s) :=
  measurable_pi_lambda _ (fun w =>
    ((measurable_pi_apply (w : I)).comp measurable_fst).prodMk
      ((measurable_pi_apply (w : I)).comp measurable_snd))

def finiteExteriorAction {I : Type*} (Q : Mat) (s : Finset I) (x : s → (ℂ × Mat)) :
    s → (ℂ × Mat) := fun w => ((x w).1, Q * (x w).2 * Q.transpose)

theorem continuous_finiteExteriorAction {I : Type*} (Q : Mat) (s : Finset I) :
    Continuous (finiteExteriorAction Q s) :=
  continuous_pi (fun w => ((continuous_fst.comp (continuous_apply w))).prodMk
    ((continuous_const.mul (continuous_snd.comp (continuous_apply w))).mul continuous_const))

@[simp] theorem exteriorProjection_action {I : Type*} (Q : Mat) (s : Finset I)
    (x : ExteriorState I) :
    exteriorProjection s (action Q x) = finiteExteriorAction Q s (exteriorProjection s x) := rfl

/-- Finite joint scalar/matrix marginals determine the whole exterior law.
This does not assume that an uncountable product is a Polish space. -/
theorem exterior_measure_eq_of_finite_marginals
    {I : Type*} (mu nu : Measure (ExteriorState I)) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (h : ∀ s : Finset I,
      Measure.map (exteriorProjection s) mu = Measure.map (exteriorProjection s) nu) : mu = nu := by
  let b := exteriorBundle I
  have hb : Measure.map b mu = Measure.map b nu := by
    apply Analysis.measure_eq_of_finite_marginals
    intro s
    have hs : Measurable (s.restrict : (I → (ℂ × Mat)) → (s → (ℂ × Mat))) :=
      measurable_pi_lambda _ (fun w => measurable_pi_apply (w : I))
    rw [Measure.map_map hs b.measurable, Measure.map_map hs b.measurable]
    exact h s
  exact b.map_measurableEquiv_injective hb

/-- Vanishing finite test discrepancy and finite-dimensional weak convergence
supply the literal full exterior law symmetry used by the constructed criterion. -/
theorem exterior_law_symmetry_of_finite_weak_limits
    {I : Type*} (mu : ℕ → Measure (ExteriorState I)) (nu : Measure (ExteriorState I))
    [IsFiniteMeasure nu] (Q : Mat) (epsilon : ℕ → ℝ)
    (hepsilon : Tendsto epsilon atTop (𝓝 0))
    (hweak : ∀ s : Finset I, External.WeakLawConverges
      (fun n => Measure.map (exteriorProjection s) (mu n))
        (Measure.map (exteriorProjection s) nu))
    (happrox : ∀ s : Finset I, ∀ n : ℕ,
      ∀ f : BoundedContinuousFunction (s → (ℂ × Mat)) ℝ,
      ‖(∫ x, f (exteriorProjection s (action Q x)) ∂mu n) -
        (∫ x, f (exteriorProjection s x) ∂mu n)‖ ≤ ‖f‖ * epsilon n) :
    Measure.map (action Q) nu = nu := by
  apply exterior_measure_eq_of_finite_marginals
  intro s
  let q := finiteExteriorAction Q s
  have hq := continuous_finiteExteriorAction Q s
  have hbound (n : ℕ) (f : BoundedContinuousFunction (s → (ℂ × Mat)) ℝ) :
      ‖(∫ x, f (q x) ∂Measure.map (exteriorProjection s) (mu n)) -
        (∫ x, f x ∂Measure.map (exteriorProjection s) (mu n))‖ ≤ ‖f‖ * epsilon n := by
    have hq' : Continuous q := hq
    have hfq : AEStronglyMeasurable (fun x => f (q x))
        (Measure.map (exteriorProjection s) (mu n)) :=
      (f.continuous.comp hq').measurable.aestronglyMeasurable
    rw [integral_map (measurable_exteriorProjection s).aemeasurable hfq,
      integral_map (measurable_exteriorProjection s).aemeasurable f.continuous.measurable.aestronglyMeasurable]
    exact happrox s n f
  have hsym := Analysis.map_eq_of_weakLimit_approximate_symmetry
    (fun n => Measure.map (exteriorProjection s) (mu n)) (Measure.map (exteriorProjection s) nu)
    q hq epsilon hepsilon (hweak s) hbound
  rw [Measure.map_map (measurable_exteriorProjection s) (measurable_action Q)]
  rw [Measure.map_map hq.measurable (measurable_exteriorProjection s)] at hsym
  exact hsym

end GeneralizedBulk.Graph
