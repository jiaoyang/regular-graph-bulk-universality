import GeneralizedBulk.Graph.ResolventCovariance
import GeneralizedBulk.Entropy.GaussianAffineEntropy

/-! The exact entropy per vertex of actual finite resolvent noise, before
rigidity and quantile approximation. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy GeneralizedBulk.Gaussian
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

/-- The actual resolvent noise law is a concrete linear image of independent
standard Gaussians with the displayed spectral square-root factor. -/
def resolventNoise (E eta sigma : ℝ) : Measure (Fin (N n) → ℝ) :=
  linearImageGaussian (D.resolventCovarianceFactor n ω E eta sigma)

theorem resolventNoise_entropy (E eta sigma : ℝ) (heta : 0 < eta) (hsigma : 0 < sigma) :
    -(∫ x, Real.log (linearGaussianPDF (D.resolventCovarianceFactor n ω E eta sigma) x)
      ∂D.resolventNoise n ω E eta sigma) =
      (N n : ℝ) / 2 * (1 + Real.log (2 * Real.pi) + Real.log (eta / sigma)) -
        (1 / 2 : ℝ) * ∑ a, Real.log (D.resolventDenominator n ω E eta a) := by
  rw [resolventNoise, linearGaussian_differentialEntropy_covariance _
    (D.resolventCovarianceFactor_det_ne_zero n ω E eta sigma heta hsigma),
    D.resolventCovariance_factor n ω E eta sigma heta hsigma,
    D.resolventCovariance_logdet n ω E eta sigma heta hsigma]
  simp only [Fintype.card_fin]
  ring

theorem resolventNoise_entropy_per_vertex (E eta sigma : ℝ) (heta : 0 < eta) (hsigma : 0 < sigma) :
    -(∫ x, Real.log (linearGaussianPDF (D.resolventCovarianceFactor n ω E eta sigma) x)
      ∂D.resolventNoise n ω E eta sigma) / (N n : ℝ) =
      (1 / 2 : ℝ) * (1 + Real.log (2 * Real.pi) + Real.log (eta / sigma)) -
        (1 / (2 * (N n : ℝ))) * ∑ a, Real.log (D.resolventDenominator n ω E eta a) := by
  rw [D.resolventNoise_entropy n ω E eta sigma heta hsigma]
  have hn : (N n : ℝ) ≠ 0 := (Nat.cast_pos.mpr (D.size_pos n)).ne'
  field_simp
  <;> ring

end GeneralizedBulk.External.RegularSpectralData
