import GeneralizedBulk.Graph.KestenMcKayNoiseEntropy
import GeneralizedBulk.Spectral.KestenMcKayUniformPotential

/-! The actual HY event implies the required compact-bulk entropy asymptotic
for genuine finite resolvent noise, with every deterministic input proved. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy GeneralizedBulk.Gaussian GeneralizedBulk.KestenMcKay
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem HY_resolventNoise_entropy_bulk_uniform {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ (d : ℝ)) (H : HYCoarseInput D P (D.kestenMcKayQuantile hd))
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E ∈ K, E ^ 2 < 4 * ((d : ℝ) - 1)) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      H.events.threshold ≤ n → ∀ ω ∈ H.events.good n, ∀ E ∈ K, ∀ eta sigma : ℝ,
      0 < eta → eta ≤ eta0 → 0 < sigma →
      |(-(∫ x, Real.log (linearGaussianPDF (D.resolventCovarianceFactor n ω E eta sigma) x)
          ∂D.resolventNoise n ω E eta sigma) / (N n : ℝ)) -
        ((1 / 2 : ℝ) * (1 + Real.log (2 * Real.pi) + Real.log (eta / sigma)) - bulkPotential d E)| ≤
        (N n : ℝ) ^ (-H.rigidity_exponent) / eta +
          (|(d : ℝ) - radius d| + 4 * radius d) / ((N n : ℝ) * eta) + C * eta := by
  obtain ⟨eta0, he0, C, hC, hu⟩ := regularizedPotential_bulk_uniform d hd K hK hbulk
  refine ⟨eta0, he0, C, hC, ?_⟩
  intro n hn ω hω E hE eta sigma heta heta' hsigma
  have ha := D.HY_resolventNoise_entropy_regularizedPotential hd H n hn ω hω E eta sigma heta hsigma
  have hb := hu E hE eta heta heta'
  let A := -(∫ x, Real.log (linearGaussianPDF (D.resolventCovarianceFactor n ω E eta sigma) x)
    ∂D.resolventNoise n ω E eta sigma) / (N n : ℝ)
  let T := (1 / 2 : ℝ) * (1 + Real.log (2 * Real.pi) + Real.log (eta / sigma))
  have heq : |(T - regularizedPotential d E eta) - (T - bulkPotential d E)| =
      |regularizedPotential d E eta - bulkPotential d E| := by
    rw [show T - regularizedPotential d E eta - (T - bulkPotential d E) =
      -(regularizedPotential d E eta - bulkPotential d E) by ring, abs_neg]
  have ht := abs_sub_le A (T - regularizedPotential d E eta) (T - bulkPotential d E)
  rw [heq] at ht
  exact ht.trans (add_le_add ha hb)

end GeneralizedBulk.External.RegularSpectralData
