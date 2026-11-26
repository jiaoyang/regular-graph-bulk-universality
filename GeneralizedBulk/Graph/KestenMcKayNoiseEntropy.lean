import GeneralizedBulk.Graph.KestenMcKayLogPotential

/-! The actual Gaussian resolvent-noise entropy is approximated by the
actual Kesten–McKay regularized potential on the HY event. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy GeneralizedBulk.Gaussian GeneralizedBulk.Spectral GeneralizedBulk.KestenMcKay
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem HY_resolventNoise_entropy_regularizedPotential {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ (d : ℝ)) (H : HYCoarseInput D P (D.kestenMcKayQuantile hd))
    (n : ℕ) (hn : H.events.threshold ≤ n) (ω : Ω) (hω : ω ∈ H.events.good n)
    (E eta sigma : ℝ) (heta : 0 < eta) (hsigma : 0 < sigma) :
    |(-(∫ x, Real.log (linearGaussianPDF (D.resolventCovarianceFactor n ω E eta sigma) x)
        ∂D.resolventNoise n ω E eta sigma) / (N n : ℝ)) -
      ((1 / 2 : ℝ) * (1 + Real.log (2 * Real.pi) + Real.log (eta / sigma)) -
        regularizedPotential d E eta)| ≤
      (N n : ℝ) ^ (-H.rigidity_exponent) / eta +
        (|(d : ℝ) - radius d| + 4 * radius d) / ((N n : ℝ) * eta) := by
  have he : -(∫ x, Real.log (linearGaussianPDF (D.resolventCovarianceFactor n ω E eta sigma) x)
        ∂D.resolventNoise n ω E eta sigma) / (N n : ℝ) =
      (1 / 2 : ℝ) * (1 + Real.log (2 * Real.pi) + Real.log (eta / sigma)) -
        (∑ i : Fin (N n), regularizedLog E eta (D.eigenvalue n ω i)) / (N n : ℝ) := by
    rw [D.resolventNoise_entropy_per_vertex n ω E eta sigma heta hsigma]
    simp only [regularizedLog, resolventDenominator, ← Finset.mul_sum]
    ring
  rw [he]
  have hid : (1 / 2 : ℝ) * (1 + Real.log (2 * Real.pi) + Real.log (eta / sigma)) -
      (∑ i : Fin (N n), regularizedLog E eta (D.eigenvalue n ω i)) / (N n : ℝ) -
      ((1 / 2 : ℝ) * (1 + Real.log (2 * Real.pi) + Real.log (eta / sigma)) - regularizedPotential d E eta) =
      -((∑ i : Fin (N n), regularizedLog E eta (D.eigenvalue n ω i)) / (N n : ℝ) - regularizedPotential d E eta) := by ring
  rw [hid, abs_neg]
  exact D.HY_kestenMcKay_logPotential hd H n hn ω hω E eta heta

end GeneralizedBulk.External.RegularSpectralData
