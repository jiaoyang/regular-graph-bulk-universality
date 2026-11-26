import BourgadeHuang.RationalBulk.FiniteLoopAlgebra
import BourgadeHuang.RationalBulk.GaussianDensityDerivative

/-! Exact finite beta-ensemble divergence identity, including collision points
after multiplication by the genuine density. -/
noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem complexGaussianScore_eq {N : ℕ} (β : ℝ) (x : Fin N → ℝ) (i : Fin N) :
    complexGaussianScore β x i = (gaussianBetaScore β N x i : ℂ) := by
  unfold complexGaussianScore gaussianBetaScore
  push_cast
  ring

theorem gaussianBetaMeasure_ae_injective {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    ∀ᵐ x ∂gaussianBetaMeasure β N, Function.Injective x := by
  unfold gaussianBetaMeasure
  apply Measure.ae_smul_measure
  rw [ae_withDensity_iff (gaussianBetaDensity_continuous hβ N).measurable.ennreal_ofReal]
  apply Eventually.of_forall
  intro x hx
  by_contra hn
  exact hx (by rw [gaussianBetaDensity_eq_zero_of_not_injective hβ x hn]; simp)

theorem gaussian_density_divergence_identity {N n : ℕ} {β : ℝ} (hβ : 0 < β)
    (hN : 0 < N) (x : Fin N → ℝ)
    {w : ℂ} {aux : Fin n → ℂ} (hw : w.im ≠ 0) (ha : ∀ a, (aux a).im ≠ 0) :
    (∑ i : Fin N, (gaussianBetaDensity β N x : ℂ) *
      (resolventTestDerivative x w aux i + (gaussianBetaScore β N x i : ℂ) * resolventTest x w aux i)) =
      (gaussianBetaDensity β N x : ℂ) * (-(β : ℂ)/2 *
        (loopIntegrand β (finiteAnchoredState x 0) w aux +
          (w/(N:ℂ)) * (microscopicResolvent x 0 w * ∏ a, microscopicResolvent x 0 (aux a)))) := by
  by_cases hx : Function.Injective x
  · rw [← Finset.mul_sum]
    simp_rw [← complexGaussianScore_eq]
    rw [gaussian_divergence_identity hβ.ne' hN.ne' x hx hw ha]
  · simp [gaussianBetaDensity_eq_zero_of_not_injective hβ x hx]

theorem gaussian_divergence_identity_ae {N n : ℕ} {β : ℝ} (hβ : 0 < β)
    (hN : 0 < N) {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im ≠ 0) (ha : ∀ a, (aux a).im ≠ 0) :
    ∀ᵐ x ∂gaussianBetaMeasure β N,
      (Finset.sum (Finset.univ : Finset (Fin N)) (fun i =>
        resolventTestDerivative x w aux i + (gaussianBetaScore β N x i : ℂ) * resolventTest x w aux i)) =
      -(β : ℂ)/2 * (loopIntegrand β (finiteAnchoredState x 0) w aux +
        (w/(N:ℂ)) * (microscopicResolvent x 0 w * ∏ a, microscopicResolvent x 0 (aux a))) := by
  filter_upwards [gaussianBetaMeasure_ae_injective hβ N] with x hx
  simpa only [complexGaussianScore_eq] using gaussian_divergence_identity hβ.ne' hN.ne' x hx hw ha

end BourgadeHuang.RationalBulk
