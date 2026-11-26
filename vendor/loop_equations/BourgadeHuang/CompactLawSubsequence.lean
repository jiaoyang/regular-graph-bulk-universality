import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sequences

/-!
# Sequential compactness of laws on a compact metric space

Positive unital linear functionals form a closed subset of the compact product
of intervals `[-‖f‖, ‖f‖]`, indexed by real continuous functions. Riesz–Markov
maps this compact set continuously onto probability measures. Weak probability
convergence is metrizable on a separable metric space, so compactness gives the
required convergent subsequences. This is an actual existence proof, with no
compactness or subsequence hypothesis on the probability laws.
-/
noncomputable section
open scoped Topology CompactlySupported BoundedContinuousFunction
open MeasureTheory Filter Set

namespace BourgadeHuang

private theorem isClosed_forall_condition {A I : Type*} [TopologicalSpace A]
    (p : I → A → Prop) (h : ∀ i, IsClosed {a | p i a}) :
    IsClosed {a | ∀ i, p i a} := by
  simpa only [Set.setOf_forall] using isClosed_iInter h

section CompactFunctionals
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Bounded positive unital linear functionals, with the topology of pointwise
convergence on continuous test functions. -/
def compactLawFunctionals : Set (C(X, ℝ) → ℝ) := {L |
    (∀ f, L f ∈ Set.Icc (-‖f‖) ‖f‖) ∧
    (∀ f g, L (f + g) = L f + L g) ∧
    (∀ (r : ℝ) f, L (r • f) = r * L f) ∧
    (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ L f) ∧
    L 1 = 1}

/-- Tychonoff compactness applies to the exact positivity and linearity equations. -/
theorem isCompact_compactLawFunctionals : IsCompact (compactLawFunctionals (X := X)) := by
  have hc : IsClosed (compactLawFunctionals (X := X)) := by
    apply IsClosed.inter
    · exact isClosed_forall_condition _ (fun f => isClosed_Icc.preimage (continuous_apply f))
    · apply IsClosed.inter
      · exact isClosed_forall_condition _ (fun f => isClosed_forall_condition _
          (fun g => isClosed_eq (continuous_apply (f + g))
            ((continuous_apply f).add (continuous_apply g))))
      · apply IsClosed.inter
        · exact isClosed_forall_condition _ (fun r => isClosed_forall_condition _
            (fun f => isClosed_eq (continuous_apply (r • f))
              (continuous_const.mul (continuous_apply f))))
        · apply IsClosed.inter
          · apply isClosed_forall_condition
            intro f
            by_cases hf : ∀ x, 0 ≤ f x
            · simpa [hf] using
                (isClosed_le continuous_const (continuous_apply f) :
                  IsClosed {L : C(X, ℝ) → ℝ | 0 ≤ L f})
            · simp [hf]
          · exact isClosed_eq (continuous_apply 1) continuous_const
  exact (isCompact_pi_infinite (fun f : C(X, ℝ) =>
    (isCompact_Icc : IsCompact (Set.Icc (-‖f‖) ‖f‖)))).of_isClosed_subset hc
    (fun _ h => h.1)

instance compactLawFunctionals_compactSpace :
    CompactSpace (compactLawFunctionals (X := X)) :=
  isCompact_iff_compactSpace.mp isCompact_compactLawFunctionals

/-- The compact-support version of a positive functional, suitable for Riesz–Markov. -/
def compactLawLinear (L : compactLawFunctionals (X := X)) : C_c(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := L.val f.toContinuousMap
  map_add' f g := L.property.2.1 f.toContinuousMap g.toContinuousMap
  map_smul' r f := L.property.2.2.1 r f.toContinuousMap

theorem compactLawLinear_nonneg (L : compactLawFunctionals (X := X))
    (f : C_c(X, ℝ)) (hf : 0 ≤ f) : 0 ≤ compactLawLinear L f :=
  L.property.2.2.2.1 _ hf

variable [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- The representing measure has mass one, as proved from the functional's
normalization and the two Riesz–Markov inequalities. -/
theorem compactLawLinear_riesz_probability (L : compactLawFunctionals (X := X)) :
    IsProbabilityMeasure (RealRMK.rieszMeasure (compactLawLinear_nonneg L)) := by
  let f : C_c(X, ℝ) := CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported (1 : C(X, ℝ))
  have hf : compactLawLinear L f = 1 := L.property.2.2.2.2
  refine ⟨le_antisymm ?_ ?_⟩
  · have hh := RealRMK.rieszMeasure_le_of_eq_one (compactLawLinear_nonneg L)
      (f := f) (fun _ => zero_le_one) isCompact_univ (fun _ _ => rfl)
    simpa only [hf, ENNReal.ofReal_one] using hh
  · have hh := RealRMK.le_rieszMeasure_tsupport_subset (compactLawLinear_nonneg L)
      (f := f) (fun _ => ⟨zero_le_one, le_rfl⟩) (Set.subset_univ _)
    simpa only [hf, ENNReal.ofReal_one] using hh

/-- The probability measure represented by a compact positive functional. -/
def compactLawMeasure (L : compactLawFunctionals (X := X)) : ProbabilityMeasure X :=
  ⟨RealRMK.rieszMeasure (compactLawLinear_nonneg L), compactLawLinear_riesz_probability L⟩

/-- The representing law integrates every continuous test to the original functional. -/
theorem integral_compactLawMeasure (L : compactLawFunctionals (X := X)) (f : C(X, ℝ)) :
    (∫ x, f x ∂(compactLawMeasure L : Measure X)) = L.val f := by
  exact RealRMK.integral_rieszMeasure (compactLawLinear_nonneg L)
    (CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported f)

/-- Pointwise convergence of functionals is weak convergence of the represented laws. -/
theorem continuous_compactLawMeasure : Continuous (compactLawMeasure (X := X)) := by
  rw [continuous_iff_continuousAt]
  intro L
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  simp only [show ∀ K : compactLawFunctionals (X := X),
      (∫ x, f x ∂(compactLawMeasure K : Measure X)) = K.val f.toContinuousMap from
    fun K => integral_compactLawMeasure K f.toContinuousMap]
  exact ((continuous_apply f.toContinuousMap).comp continuous_subtype_val).continuousAt

end CompactFunctionals

section CompactMetricLaws
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Integration against a probability law is a bounded positive unital functional. -/
def probabilityLawFunctional (μ : ProbabilityMeasure X) : compactLawFunctionals (X := X) := by
  refine ⟨(fun f => ∫ x, f x ∂(μ : Measure X)), ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    have hh := norm_integral_le_of_norm_le_const (μ := (μ : Measure X))
      (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x))
    have hh' : |∫ x, f x ∂(μ : Measure X)| ≤ ‖f‖ := by simpa using hh
    exact abs_le.mp hh'
  · intro f g
    exact integral_add
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g))
  · intro r f
    exact integral_const_mul r (fun x => f x)
  · intro f hf
    exact integral_nonneg hf
  · simp

/-- Riesz representation recovers the original law, so every law is represented. -/
theorem compactLawMeasure_probabilityLawFunctional (μ : ProbabilityMeasure X) :
    compactLawMeasure (probabilityLawFunctional μ) = μ := by
  have hh : (compactLawMeasure (probabilityLawFunctional μ)).toFiniteMeasure = μ.toFiniteMeasure := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    exact integral_compactLawMeasure (probabilityLawFunctional μ) f.toContinuousMap
  apply Subtype.ext
  exact congrArg (fun ν : FiniteMeasure X => (ν : Measure X)) hh

/-- Probability laws on a compact metric space form a compact space in the weak
topology. The compactness follows from the representing positive functionals. -/
theorem compactSpace_probabilityMeasure : CompactSpace (ProbabilityMeasure X) := by
  constructor
  have hh := isCompact_univ.image (continuous_compactLawMeasure (X := X))
  have hsurj : Function.Surjective (compactLawMeasure (X := X)) :=
    fun μ => ⟨probabilityLawFunctional μ, compactLawMeasure_probabilityLawFunctional μ⟩
  simpa only [Set.image_univ, Set.range_eq_univ.mpr hsurj] using hh

/-- Every sequence of probability laws on a compact metric space has an actual
weakly convergent subsequence. -/
theorem compact_probability_laws_subsequence [SecondCountableTopology X]
    (μ : ℕ → ProbabilityMeasure X) :
    ∃ (ν : ProbabilityMeasure X) (r : ℕ → ℕ), StrictMono r ∧
      Tendsto (μ ∘ r) atTop (𝓝 ν) := by
  letI : CompactSpace (ProbabilityMeasure X) := compactSpace_probabilityMeasure
  exact SeqCompactSpace.tendsto_subseq μ

/-- The subsequence can be tested against every real bounded continuous function. -/
theorem compact_probability_laws_subsequence_integrals [SecondCountableTopology X]
    (μ : ℕ → ProbabilityMeasure X) :
    ∃ (ν : ProbabilityMeasure X) (r : ℕ → ℕ), StrictMono r ∧
      ∀ f : X →ᵇ ℝ, Tendsto
        (fun n => ∫ x, f x ∂(μ (r n) : Measure X)) atTop
        (𝓝 (∫ x, f x ∂(ν : Measure X))) := by
  obtain ⟨ν, r, hr, hh⟩ := compact_probability_laws_subsequence μ
  exact ⟨ν, r, hr, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hh⟩

end CompactMetricLaws


end BourgadeHuang
