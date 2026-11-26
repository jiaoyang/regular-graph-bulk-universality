import GeneralizedBulk.Analysis.FiniteDimensionalSubsequence
import GeneralizedBulk.Gaussian.CharacteristicUniqueness

/-! Finite-dimensional characteristic convergence upgraded to genuine weak convergence. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace GeneralizedBulk.Gaussian

def linearCharacteristic {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    BoundedContinuousFunction (ι → ℝ) ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I))
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_finiteLinearForm t)).mul continuous_const))
    1 (fun x => by simp [Complex.norm_exp])

theorem weakLaw_complex_integral {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : ℕ → Measure E) (ν : Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges μ ν) (f : BoundedContinuousFunction E ℂ) :
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (𝓝 (∫ x, f x ∂ν)) := by
  let laws : ℕ → ProbabilityMeasure E := fun n => ⟨μ n, inferInstance⟩
  let limit : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have h : Tendsto laws atTop (𝓝 limit) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hweak
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp h f

theorem weakLaw_characteristic {ι : Type*} [Fintype ι]
    (μ : ℕ → Measure (ι → ℝ)) (ν : Measure (ι → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges μ ν) (t : ι → ℝ) :
    Tendsto (fun n => ∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂μ n)
      atTop (𝓝 (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂ν)) :=
  weakLaw_complex_integral μ ν hweak (linearCharacteristic t)

/-- Tightness from a uniform fourth moment, characteristic-function uniqueness,
and pointwise characteristic convergence prove actual bounded-continuous weak
convergence. This includes product and finite-cutoff mark applications. -/
theorem weakLaw_of_characteristic_of_norm_fourth
    {ι : Type*} [Fintype ι] (μ : ℕ → Measure (ι → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)] (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν]
    (hi : ∀ n, Integrable (fun x => ‖x‖ ^ 4) (μ n)) (M : ℝ)
    (hM : ∀ n, (∫ x, ‖x‖ ^ 4 ∂μ n) ≤ M)
    (hcf : ∀ t : ι → ℝ,
      Tendsto (fun n => ∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂μ n)
        atTop (𝓝 (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂ν))) :
    External.WeakLawConverges μ ν := by
  intro F
  apply tendsto_of_subseq_tendsto
  intro r hr
  obtain ⟨t, ht, hrt⟩ := strictMono_subseq_of_tendsto_atTop hr
  let laws : ℕ → ProbabilityMeasure (ι → ℝ) := fun n => ⟨μ (r (t n)), inferInstance⟩
  obtain ⟨ρ, s, hs, hconv⟩ := Analysis.finite_laws_subsequence_of_uniform_norm_fourth laws
    (fun n => hi (r (t n))) M (fun n => hM (r (t n)))
  let φ := r ∘ t ∘ s
  have hφ : StrictMono φ := hrt.comp hs
  have hweak : External.WeakLawConverges (fun n => μ (φ n)) (ρ : Measure (ι → ℝ)) := by
    intro G
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv G
  have heq : (ρ : Measure (ι → ℝ)) = ν := by
    apply measure_eq_of_linear_characteristic
    intro a
    exact tendsto_nhds_unique (weakLaw_characteristic _ _ hweak a)
      ((hcf a).comp hφ.tendsto_atTop)
  refine ⟨t ∘ s, ?_⟩
  have h := hweak F
  rw [heq] at h
  exact h

end GeneralizedBulk.Gaussian
