import BourgadeHuang.RationalBulk.GaussianBetaDensity

/-! Polynomially bounded observables multiplied by the actual density. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem gaussianBetaDensity_smul_integrable_of_envelope {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (hN : 0 < N) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin N → ℝ) → E} (hF : StronglyMeasurable F) (q : ℕ) {C : ℝ}
    (hbound : ∀ x, ‖F x‖ ≤ C * coordinateEnvelope x ^ q) :
    Integrable (fun x => gaussianBetaDensity β N x • F x) := by
  refine ((gaussianBetaDensity_envelope_integrable hβ hN q).const_mul C).mono'
    ((gaussianBetaDensity_continuous hβ N).stronglyMeasurable.smul hF).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (gaussianBetaDensity_nonneg β N x)]
  calc
    _ ≤ gaussianBetaDensity β N x * (C * coordinateEnvelope x ^ q) :=
      mul_le_mul_of_nonneg_left (hbound x) (gaussianBetaDensity_nonneg β N x)
    _ = _ := by unfold coordinateEnvelope; ring

theorem gaussianBetaDensity_mul_integrable_of_envelope {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (hN : 0 < N) {F : (Fin N → ℝ) → ℂ} (hF : StronglyMeasurable F)
    (q : ℕ) {C : ℝ} (hbound : ∀ x, ‖F x‖ ≤ C * coordinateEnvelope x ^ q) :
    Integrable (fun x => (gaussianBetaDensity β N x : ℂ) * F x) := by
  simpa only [Complex.real_smul] using
    gaussianBetaDensity_smul_integrable_of_envelope hβ hN hF q hbound

end BourgadeHuang.RationalBulk
