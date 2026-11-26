import GaussianWave.StarCovariancePSD
import GaussianWave.GaussianProduct

/-! The canonical star Gaussian satisfies the eigenvalue equation almost
surely. This checks the physical support of the possibly singular target law. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace GaussianWave

theorem starGaussian_eigenrelation (d : ℕ) (energy : ℝ) (hd : 2 ≤ d)
    (hC : (RegularEigenData.starWaveCovariance d energy).PosSemidef) :
    ∀ᵐ x ∂gaussianCovarianceLaw (RegularEigenData.starWaveCovariance d energy) hC,
      (∑ i : Fin d, x i.succ) = energy * x 0 := by
  let C := RegularEigenData.starWaveCovariance d energy
  let μ := gaussianCovarianceLaw C hC
  let t : Fin (d + 1) → ℝ := Fin.cases (-energy) (fun _ => 1)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hq : finiteCovarianceQuadratic C t = 0 := by
    rw [RegularEigenData.starWaveCovariance_quadratic_factor d energy hd t]
    simp only [t, Fin.cases_zero, Fin.cases_succ, one_pow, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hm : energy / (d : ℝ) * (d : ℝ) = energy := div_mul_cancel₀ _ hd0
    have hv : (d : ℝ) ^ 2 / (d : ℝ) = (d : ℝ) := by
      rw [pow_two, mul_div_cancel_right₀ _ hd0]
    simp only [hm, hv, neg_add_cancel, zero_pow (by decide : 2 ≠ 0),
      sub_self, mul_zero, add_zero]
  have hi := centeredGaussian_projection_integrable_pow μ C
    (finiteCovarianceQuadratic_nonneg_of_posSemidef C hC)
    (gaussianCovarianceLaw_characteristic C hC) t 2
  have hm := centeredGaussian_projection_second_moment μ C
    (finiteCovarianceQuadratic_nonneg_of_posSemidef C hC)
    (gaussianCovarianceLaw_characteristic C hC) t
  rw [hq] at hm
  have ha : (fun x => finiteLinearForm t x ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hi).mp hm
  filter_upwards [ha] with x hx
  have hz : finiteLinearForm t x = 0 := by
    change finiteLinearForm t x ^ 2 = 0 at hx
    exact (sq_eq_zero_iff).mp hx
  have hl : finiteLinearForm t x = -energy * x 0 + ∑ i : Fin d, x i.succ := by
    simp [finiteLinearForm, Fin.sum_univ_succ, t]
  rw [hl] at hz
  linarith

end GaussianWave
