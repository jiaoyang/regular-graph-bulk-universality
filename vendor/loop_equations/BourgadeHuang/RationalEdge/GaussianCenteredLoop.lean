import BourgadeHuang.RationalEdge.GaussianCenteredBounds
import BourgadeHuang.RationalBulk.GaussianBetaIntegrationByParts

/-! Centered Gaussian beta loop identity from actual density integration by parts.
Collision scores are integrable for every positive beta, including beta below one. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk

theorem gaussianBeta_centered_finite_loop (β : ℝ) (hβ : 0<β)
    (N n : ℕ) (center : ℝ) (w : ℂ) (hw : w.im≠0)
    (aux : Fin n → ℂ) (ha : ∀a,(aux a).im≠0) :
    (∫ x, centeredGaussianLoop β x center w aux ∂gaussianBetaMeasure β (N+1)) = 0 := by
  let den := fun x : Fin (N+1) → ℝ => (gaussianBetaDensity β (N+1) x : ℂ)
  let Q := fun (i : Fin (N+1)) (x : Fin (N+1) → ℝ) =>
    den x * (centeredResolventTestDerivative x center w aux i +
      (gaussianBetaScore β (N+1) x i : ℂ)*centeredResolventTest x center w aux i)
  have hQi (i : Fin (N+1)) : Integrable (Q i) := by
    obtain ⟨CF,_,hF⟩ := bounded_centeredResolventTest center i hw ha
    obtain ⟨CD,_,hD⟩ := bounded_centeredResolventTestDerivative center i hw ha
    have hDI := gaussianBetaDensity_mul_integrable_of_envelope hβ (by omega)
      (continuous_centeredResolventTestDerivative center i hw ha).stronglyMeasurable 0
      (C:=CD) (by simpa only [pow_zero,mul_one] using hD)
    have hSI := gaussianBetaDensity_fullScore_smul_integrable hβ (by omega) i
      (continuous_centeredResolventTest center i hw ha).stronglyMeasurable 0
      (C:=CF) (by simpa only [pow_zero,mul_one] using hF)
    convert hDI.add hSI using 1
    ext x
    simp only [Q,den,Pi.add_apply,Complex.real_smul,Complex.ofReal_mul]
    ring
  have hQ0 (i : Fin (N+1)) : (∫ x,Q i x)=0 := by
    obtain ⟨CF,_,hF⟩ := bounded_centeredResolventTest center i hw ha
    obtain ⟨CD,_,hD⟩ := bounded_centeredResolventTestDerivative center i hw ha
    exact gaussianBetaDensity_integrationByParts_of_envelope hβ i
      (fun x => centeredResolventTest x center w aux i)
      (fun x => centeredResolventTestDerivative x center w aux i)
      (continuous_centeredResolventTest center i hw ha)
      (continuous_centeredResolventTestDerivative center i hw ha).stronglyMeasurable
      (fun x => hasDerivAt_centeredResolventTest x center i hw ha) 0 0
      (CF:=CF) (CD:=CD) (by simpa only [pow_zero,mul_one] using hF)
      (by simpa only [pow_zero,mul_one] using hD)
  have hsum : (∫ x,∑ i,Q i x)=0 := by
    rw [integral_finset_sum _ (fun i _ => hQi i)]
    simp only [hQ0,Finset.sum_const_zero]
  have hpoint (x : Fin (N+1) → ℝ) :
      (∑ i,Q i x) = -(β:ℂ)/2 * (den x * centeredGaussianLoop β x center w aux) := by
    by_cases hx : Function.Injective x
    · simp only [Q, ←complexGaussianScore_eq, ←Finset.mul_sum]
      rw [centered_gaussian_divergence_identity hβ.ne' (by omega) x center hx hw]
      ring
    · simp [Q, den, gaussianBetaDensity_eq_zero_of_not_injective hβ x hx]
  simp_rw [hpoint] at hsum
  rw [integral_const_mul] at hsum
  have hk : -(β:ℂ)/2 ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hβ.ne')) (by norm_num)
  have hz : (∫ x, den x * centeredGaussianLoop β x center w aux) = 0 :=
    (mul_eq_zero.mp hsum).resolve_left hk
  rw [gaussianBetaMeasure_integral hβ (by omega)]
  simp only [Complex.real_smul]
  change _ * (∫ x, den x * centeredGaussianLoop β x center w aux) = 0
  rw [hz,mul_zero]

end BourgadeHuang.RationalEdge
