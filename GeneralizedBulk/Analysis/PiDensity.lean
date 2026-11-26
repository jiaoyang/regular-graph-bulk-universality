import Mathlib

/-! Product densities for actual finite products of real probability spaces. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace GeneralizedBulk.Analysis
variable {I : Type*} [Fintype I]

theorem integral_pi_product (μ : I → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : I → ℝ → ℝ) :
    (∫ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫ t, f i t ∂μ i := by
  let instMS : (i : I) → MeasureSpace ℝ := fun i => ⟨μ i⟩
  have instSF : ∀ i : I, @SigmaFinite ℝ _ (@volume ℝ (instMS i)) := fun i => inferInstance
  simpa only [volume_pi] using
    @integral_fintype_prod_eq_prod ℝ _ I _ (fun _ => ℝ) f instMS instSF

theorem integrable_pi_product (μ : I → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : I → ℝ → ℝ) (hf : ∀ i, Integrable (f i) (μ i)) :
    Integrable (fun x => ∏ i, f i (x i)) (Measure.pi μ) := by
  let instMS : (i : I) → MeasureSpace ℝ := fun i => ⟨μ i⟩
  have instSF : ∀ i : I, @SigmaFinite ℝ _ (@volume ℝ (instMS i)) := fun i => inferInstance
  simpa only [volume_pi] using
    @Integrable.fintype_prod_dep ℝ _ I _ (fun _ => ℝ) f instMS instSF hf

/-- A finite product of actual real densities is their product density.
This supplies the multivariate Gaussian-mixture density without a separate
Radon--Nikodym or independence hypothesis. -/
theorem pi_withDensity_ofReal (μ : I → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : I → ℝ → ℝ) (hf : ∀ i, Integrable (f i) (μ i))
    (hpos : ∀ i t, 0 ≤ f i t) :
    Measure.pi (fun i => (μ i).withDensity (fun t => ENNReal.ofReal (f i t))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  letI : ∀ i, IsFiniteMeasure ((μ i).withDensity (fun t => ENNReal.ofReal (f i t))) :=
    fun i => isFiniteMeasure_withDensity_ofReal (hf i).hasFiniteIntegral
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hprod := integrable_pi_product μ f hf
  rw [← ofReal_integral_eq_lintegral_ofReal hprod.restrict
    (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => hpos i (x i))))]
  rw [Measure.restrict_pi_pi, integral_pi_product]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hpos i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hf i).restrict (ae_of_all _ (hpos i))

end GeneralizedBulk.Analysis
