import GaussianWave.BS.WhiteSecondMoments
import GaussianWave.BS.EntropyRecovery

/-!
# The analytic comparison step for the actual entropy functional

A finite-entropy density witness records the source theorem's ordinary
absolute continuity and finite entropy hypotheses. It contains no upper
bound, Gaussianity, score identity, or entropy-convergence premise.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace GaussianWave.BS

structure FiniteEntropyDensity {I : Type*} [Fintype I] (μ : Measure (I → ℝ)) where
  density : (I → ℝ) → ℝ
  measurable : Measurable density
  nonneg : ∀ x, 0 ≤ density x
  integrable : Integrable density
  integral_eq_one : (∫ x, density x) = 1
  integrable_log : Integrable (fun x => density x * Real.log (density x))
  measure_eq : μ = volume.withDensity (fun x => ENNReal.ofReal (density x))

def FiniteEntropyDensity.entropy {I : Type*} [Fintype I] {μ : Measure (I → ℝ)}
    (f : FiniteEntropyDensity μ) : ℝ := densityEntropy volume f.density

/-- Entropy depends on the actual law, not on the chosen density version. -/
theorem FiniteEntropyDensity.entropy_eq_of_measure_eq
    {I : Type*} [Fintype I] {μ ν : Measure (I → ℝ)}
    (f : FiniteEntropyDensity μ) (g : FiniteEntropyDensity ν) (hμν : μ = ν) :
    f.entropy = g.entropy := by
  have heq : volume.withDensity (fun x => ENNReal.ofReal (f.density x)) =
      volume.withDensity (fun x => ENNReal.ofReal (g.density x)) :=
    f.measure_eq.symm.trans (hμν.trans g.measure_eq)
  have hae := (withDensity_eq_iff_of_sigmaFinite f.measurable.ennreal_ofReal.aemeasurable
    g.measurable.ennreal_ofReal.aemeasurable).mp heq
  have hre : f.density =ᵐ[volume] g.density := by
    filter_upwards [hae] with x hx
    have h := congrArg ENNReal.toReal hx
    simpa only [ENNReal.toReal_ofReal (f.nonneg _), ENNReal.toReal_ofReal (g.nonneg _)] using h
  unfold FiniteEntropyDensity.entropy densityEntropy
  congr 1
  apply integral_congr_ae
  exact hre.mono (fun _ hx => congrArg (fun a : ℝ => a * Real.log a) hx)

def initialFrameEntropy {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    {μ : Measure (I → ℝ)} {O : K → Matrix J I ℝ}
    (f : FiniteEntropyDensity μ)
    (g : ∀ i, FiniteEntropyDensity (Measure.map (fun x => (O i).mulVec x) μ)) : ℝ :=
  f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy

theorem tendsto_heatFrameEntropy_zero
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (O : K → Matrix J I ℝ)
    (f : FiniteEntropyDensity μ)
    (g : ∀ i, FiniteEntropyDensity (Measure.map (fun x => (O i).mulVec x) μ)) :
    Tendsto (heatFrameEntropy μ O) (𝓝[>] 0) (𝓝 (initialFrameEntropy f g)) := by
  classical
  letI : ∀ i, IsProbabilityMeasure (Measure.map (fun x => (O i).mulVec x) μ) :=
    fun i => isProbabilityMeasure_map (measurable_finiteMatrixAction (O i)).aemeasurable
  have ha := tendsto_heatDensity_entropy_zero μ f.density f.measurable f.nonneg f.integrable
    f.integral_eq_one f.integrable_log f.measure_eq hμ
  have hg := tendsto_finset_sum Finset.univ (fun i _ =>
    tendsto_heatDensity_entropy_zero (Measure.map (fun x => (O i).mulVec x) μ)
      (g i).density (g i).measurable (g i).nonneg (g i).integrable
      (g i).integral_eq_one (g i).integrable_log (g i).measure_eq
      (integrable_squareRadius_matrixImage μ hμ (O i)))
  exact ha.sub (hg.const_mul (1 / 2 : ℝ))

/-- A calculus lemma for the actual heat functional. Its Fisher premise is
isolated here for use after the geometric projection argument proves it. -/
theorem monotoneOn_heatFrameEntropy_of_fisher_nonneg
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (O : K → Matrix J I ℝ)
    (hF : ∀ t, 0 < t → 0 ≤ heatFrameFisherDefect μ O t) :
    MonotoneOn (heatFrameEntropy μ O) (Set.Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro t ht
    exact (hasDerivAt_heatFrameEntropy μ hμ O ht).continuousAt.continuousWithinAt
  · intro t ht
    have hp : 0 < t := interior_subset ht
    exact (hasDerivAt_heatFrameEntropy μ hμ O hp).differentiableAt.differentiableWithinAt
  · intro t ht
    have hp : 0 < t := interior_subset ht
    rw [(hasDerivAt_heatFrameEntropy μ hμ O hp).deriv]
    exact hF t hp

/-- Elementary real analysis: a nondecreasing positive-time function lies
between its one-sided endpoint limits. -/
theorem endpoint_comparison_of_monotoneOn
    (F : ℝ → ℝ) (A B : ℝ) (hmono : MonotoneOn F (Set.Ioi 0))
    (hzero : Tendsto F (𝓝[>] 0) (𝓝 A)) (hinfty : Tendsto F atTop (𝓝 B)) :
    A ≤ B ∧ ∀ t, 0 < t → F t ≤ B := by
  have hb (t : ℝ) (ht : 0 < t) : F t ≤ B := by
    apply ge_of_tendsto hinfty
    filter_upwards [eventually_ge_atTop t] with u hu
    exact hmono ht (lt_of_lt_of_le ht hu) hu
  constructor
  · apply le_of_tendsto hzero
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hb t ht
  · exact hb

theorem eq_of_monotoneOn_and_equal_endpoint_limits
    (F : ℝ → ℝ) (A : ℝ) (hmono : MonotoneOn F (Set.Ioi 0))
    (hzero : Tendsto F (𝓝[>] 0) (𝓝 A)) (hinfty : Tendsto F atTop (𝓝 A)) :
    ∀ t, 0 < t → F t = A := by
  have hupper := (endpoint_comparison_of_monotoneOn F A A hmono hzero hinfty).2
  intro t ht
  apply le_antisymm (hupper t ht)
  apply le_of_tendsto hzero
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds] with u hu hut
  exact hmono hu ht hut.le

end GaussianWave.BS
