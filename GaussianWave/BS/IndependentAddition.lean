import GaussianWave.Foundation

/-! Independent addition is weakly continuous in either argument separately.
The measures are actual product-and-pushforward laws. No moment hypothesis is
needed: averaging a bounded continuous test against the fixed law remains a
bounded continuous test. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GaussianWave.BS

variable {I : Type*} [Fintype I]

/-- The literal law of `X + η Y` for independent `X` and `Y`. -/
def independentAddLaw (μ ν : Measure (I → ℝ)) (η : ℝ) : Measure (I → ℝ) :=
  Measure.map (fun p : (I → ℝ) × (I → ℝ) => p.1 + η • p.2) (μ.prod ν)

private theorem continuous_addSample (η : ℝ) :
    Continuous (fun p : (I → ℝ) × (I → ℝ) => p.1 + η • p.2) :=
  continuous_fst.add (continuous_const.smul continuous_snd)

instance independentAddLaw_probability (μ ν : Measure (I → ℝ)) (η : ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (independentAddLaw μ ν η) :=
  isProbabilityMeasure_map (continuous_addSample η).measurable.aemeasurable

/-- Fubini for bounded continuous observations of an actual independent sum. -/
theorem integral_independentAddLaw (μ ν : Measure (I → ℝ)) (η : ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : BoundedContinuousFunction (I → ℝ) ℝ) :
    (∫ z, F z ∂independentAddLaw μ ν η) =
      ∫ x, ∫ y, F (x + η • y) ∂ν ∂μ := by
  have hc := F.continuous.comp (continuous_addSample η)
  have hi : Integrable (fun p : (I → ℝ) × (I → ℝ) => F (p.1 + η • p.2))
      (μ.prod ν) :=
    (integrable_const ‖F‖).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => F.norm_coe_le_norm _))
  rw [independentAddLaw, integral_map (continuous_addSample η).measurable.aemeasurable
    F.continuous.aestronglyMeasurable, integral_prod _ hi]

/-- Averaging a bounded continuous observation over the fixed independent noise. -/
def averagedAddTest (ν : Measure (I → ℝ)) [IsProbabilityMeasure ν]
    (η : ℝ) (F : BoundedContinuousFunction (I → ℝ) ℝ) :
    BoundedContinuousFunction (I → ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => ∫ y, F (x + η • y) ∂ν)
    (continuous_of_dominated
      (fun x => (F.continuous.comp (continuous_const.add
        (continuous_const.smul continuous_id))).aestronglyMeasurable)
      (fun x => Filter.Eventually.of_forall (fun y => F.norm_coe_le_norm _))
      (integrable_const ‖F‖)
      (Filter.Eventually.of_forall (fun y =>
        F.continuous.comp (continuous_id.add continuous_const))))
    ‖F‖ (fun x => by
      calc
        ‖∫ y, F (x + η • y) ∂ν‖ ≤ ∫ y, ‖F (x + η • y)‖ ∂ν := norm_integral_le_integral_norm _
        _ ≤ ∫ _ : I → ℝ, ‖F‖ ∂ν := integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) (integrable_const _)
          (Filter.Eventually.of_forall (fun _ => F.norm_coe_le_norm _))
        _ = ‖F‖ := by simp)

/-- Weak convergence of the signal is preserved by adding a fixed independent law. -/
theorem independentAddLaw_weakConverges_left
    (μ : ℕ → Measure (I → ℝ)) (ρ ν : Measure (I → ℝ)) (η : ℝ)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    (hμ : WeakLawConverges μ ρ) :
    WeakLawConverges (fun n => independentAddLaw (μ n) ν η)
      (independentAddLaw ρ ν η) := by
  intro F
  simpa only [integral_independentAddLaw, averagedAddTest,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup] using hμ (averagedAddTest ν η F)

/-- Averaging in the signal variable is also a bounded continuous test. -/
def averagedSignalTest (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (η : ℝ) (F : BoundedContinuousFunction (I → ℝ) ℝ) :
    BoundedContinuousFunction (I → ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y => ∫ x, F (x + η • y) ∂μ)
    (continuous_of_dominated
      (fun y => (F.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
      (fun y => Filter.Eventually.of_forall (fun x => F.norm_coe_le_norm _))
      (integrable_const ‖F‖)
      (Filter.Eventually.of_forall (fun x => F.continuous.comp
        (continuous_const.add (continuous_const.smul continuous_id)))))
    ‖F‖ (fun y => by
      calc
        ‖∫ x, F (x + η • y) ∂μ‖ ≤ ∫ x, ‖F (x + η • y)‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ _ : I → ℝ, ‖F‖ ∂μ := integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) (integrable_const _)
          (Filter.Eventually.of_forall (fun _ => F.norm_coe_le_norm _))
        _ = ‖F‖ := by simp)

/-- Weak convergence of the independent noise is preserved with the signal fixed. -/
theorem independentAddLaw_weakConverges_right
    (μ : Measure (I → ℝ)) (ν : ℕ → Measure (I → ℝ)) (ρ : Measure (I → ℝ)) (η : ℝ)
    [IsProbabilityMeasure μ] [∀ n, IsProbabilityMeasure (ν n)] [IsProbabilityMeasure ρ]
    (hν : WeakLawConverges ν ρ) :
    WeakLawConverges (fun n => independentAddLaw μ (ν n) η)
      (independentAddLaw μ ρ η) := by
  intro F
  have hswap (θ : Measure (I → ℝ)) [IsProbabilityMeasure θ] :
      (∫ z, F z ∂independentAddLaw μ θ η) =
        ∫ y, ∫ x, F (x + η • y) ∂μ ∂θ := by
    have hc := F.continuous.comp (continuous_addSample η)
    have hi : Integrable (fun p : (I → ℝ) × (I → ℝ) => F (p.1 + η • p.2))
        (μ.prod θ) := (integrable_const ‖F‖).mono' hc.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun p => F.norm_coe_le_norm _))
    rw [integral_independentAddLaw, integral_integral_swap hi]
  simpa only [hswap, averagedSignalTest,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup] using hν (averagedSignalTest μ η F)

end GaussianWave.BS
