import BourgadeHuang.RationalBulk.CoordinateSingularIBP
import BourgadeHuang.RationalBulk.GaussianDensityDerivative
import BourgadeHuang.RationalBulk.GaussianDensityObservable
import BourgadeHuang.RationalBulk.GaussianScoreObservable

/-! Genuine integration by parts for the Gaussian beta density. The collision
hyperplanes require only beta > 0; derivatives at the hyperplanes are not used. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem gaussianBetaDensity_integrationByParts {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (i : Fin (N+1)) (F D : (Fin (N+1) → ℝ) → ℂ)
    (hF : Continuous F)
    (hderiv : ∀ x, HasDerivAt (fun t => F (Function.update x i t)) (D x) (x i))
    (hFI : Integrable (fun x => (gaussianBetaDensity β (N+1) x : ℂ) * F x))
    (hDI : Integrable (fun x => (gaussianBetaDensity β (N+1) x : ℂ) * D x))
    (hSI : Integrable (fun x => (gaussianBetaDensity β (N+1) x : ℂ) *
      (gaussianBetaScore β (N+1) x i : ℂ) * F x)) :
    (∫ x, (gaussianBetaDensity β (N+1) x : ℂ) *
      (D x + (gaussianBetaScore β (N+1) x i : ℂ) * F x)) = 0 := by
  have hg : Integrable (fun x => (gaussianBetaDensity β (N+1) x : ℂ) *
      (D x + (gaussianBetaScore β (N+1) x i : ℂ) * F x)) := by
    convert hDI.add hSI using 1
    ext x
    simp only [Pi.add_apply]
    ring
  apply integral_coordinate_derivative_eq_zero i
    (fun x => (gaussianBetaDensity β (N+1) x : ℂ) * F x) _
    ((Complex.continuous_ofReal.comp (gaussianBetaDensity_continuous hβ (N+1))).mul hF) _ hFI hg
  intro x hsep
  have hd := (hasDerivAt_gaussianBetaDensity (β := β) x i hsep).ofReal_comp.mul (hderiv x)
  convert hd using 1
  simp only [Complex.ofReal_mul, Function.update_eq_self]
  ring

theorem gaussianBetaMeasure_integrationByParts_of_integrable {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (i : Fin (N+1)) (F D : (Fin (N+1) → ℝ) → ℂ)
    (hF : Continuous F)
    (hderiv : ∀ x, HasDerivAt (fun t => F (Function.update x i t)) (D x) (x i))
    (hFI : Integrable (fun x => (gaussianBetaDensity β (N+1) x : ℂ) * F x))
    (hDI : Integrable (fun x => (gaussianBetaDensity β (N+1) x : ℂ) * D x))
    (hSI : Integrable (fun x => (gaussianBetaDensity β (N+1) x : ℂ) *
      (gaussianBetaScore β (N+1) x i : ℂ) * F x)) :
    (∫ x, D x + (gaussianBetaScore β (N+1) x i : ℂ) * F x
      ∂gaussianBetaMeasure β (N+1)) = 0 := by
  rw [gaussianBetaMeasure_integral hβ (by omega)]
  simp only [Complex.real_smul]
  rw [gaussianBetaDensity_integrationByParts hβ i F D hF hderiv hFI hDI hSI, mul_zero]

/-- Full density IBP from actual differentiability and polynomial bounds alone. -/
theorem gaussianBetaDensity_integrationByParts_of_envelope {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (i : Fin (N+1)) (F D : (Fin (N+1) → ℝ) → ℂ)
    (hF : Continuous F) (hD : StronglyMeasurable D)
    (hderiv : ∀ x, HasDerivAt (fun t => F (Function.update x i t)) (D x) (x i))
    (qF qD : ℕ) {CF CD : ℝ}
    (hFb : ∀ x, ‖F x‖ ≤ CF * coordinateEnvelope x ^ qF)
    (hDb : ∀ x, ‖D x‖ ≤ CD * coordinateEnvelope x ^ qD) :
    (∫ x, (gaussianBetaDensity β (N+1) x : ℂ) *
      (D x + (gaussianBetaScore β (N+1) x i : ℂ) * F x)) = 0 := by
  apply gaussianBetaDensity_integrationByParts hβ i F D hF hderiv
  · exact gaussianBetaDensity_mul_integrable_of_envelope hβ (by omega)
      hF.stronglyMeasurable qF hFb
  · exact gaussianBetaDensity_mul_integrable_of_envelope hβ (by omega) hD qD hDb
  · simpa only [Complex.real_smul, Complex.ofReal_mul] using
      gaussianBetaDensity_fullScore_smul_integrable hβ (by omega) i
        hF.stronglyMeasurable qF hFb

/-- Probability-law version, with no assumed integrability of collision scores. -/
theorem gaussianBetaMeasure_integrationByParts {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (i : Fin (N+1)) (F D : (Fin (N+1) → ℝ) → ℂ)
    (hF : Continuous F) (hD : StronglyMeasurable D)
    (hderiv : ∀ x, HasDerivAt (fun t => F (Function.update x i t)) (D x) (x i))
    (qF qD : ℕ) {CF CD : ℝ}
    (hFb : ∀ x, ‖F x‖ ≤ CF * coordinateEnvelope x ^ qF)
    (hDb : ∀ x, ‖D x‖ ≤ CD * coordinateEnvelope x ^ qD) :
    (∫ x, D x + (gaussianBetaScore β (N+1) x i : ℂ) * F x
      ∂gaussianBetaMeasure β (N+1)) = 0 := by
  rw [gaussianBetaMeasure_integral hβ (by omega)]
  simp only [Complex.real_smul]
  rw [gaussianBetaDensity_integrationByParts_of_envelope hβ i F D hF hD hderiv
    qF qD hFb hDb, mul_zero]

end BourgadeHuang.RationalBulk
