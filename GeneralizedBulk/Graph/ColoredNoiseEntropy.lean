import GeneralizedBulk.Graph.ColoredResolventNoise
import GeneralizedBulk.Graph.KestenMcKayBulkNoiseEntropy
import GeneralizedBulk.Matrix.ColorBlockDeterminant
import GeneralizedBulk.Graph.GaussianChannelEntropy
import GeneralizedBulk.Entropy.AffineEntropyFormula

/-! Actual colored global Gaussian entropy, its graph-channel coordinate
bridge, and its uniform HY bulk asymptotic. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace GeneralizedBulk.Graph.Configuration
open GeneralizedBulk.Entropy

theorem wholeGaussianDensity_entropy_square_factor {k N : ℕ}
    (A : Matrix (Fin k × Fin N) (Fin k × Fin N) ℝ) (hA : A.det ≠ 0) (lo : ℝ) (hlo : 0 < lo)
    (hbound : ∀ x : Fin k × Fin N → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x)) :
    differentialEntropy (wholeGaussianDensity A lo hlo hbound 0)=
      differentialEntropy (affineGaussianPDF 0 A) := by
  rw [wholeGaussianDensity,differentialEntropy_affineGaussianPDF _ _ (wholeNoiseFactor_det_ne_zero A lo hlo hbound),
    differentialEntropy_affineGaussianPDF _ _ hA]
  have he : flatSelection (k := k) (id : Fin N → Fin N)=((finProdFinEquiv : (Fin k × Fin N) ≃ Fin (k*N)).symm : Fin (k*N) → Fin k × Fin N) := rfl
  have hg := selectedGaussianFactor_covariance A (flatSelection (id : Fin N → Fin N))
    (flatSelection_injective id Function.injective_id) lo hlo hbound
  change wholeNoiseFactor A lo hlo hbound*(wholeNoiseFactor A lo hlo hbound).transpose=(A*A.transpose).submatrix _ _ at hg
  rw [hg,he,Matrix.det_submatrix_equiv_self]
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]

end GeneralizedBulk.Graph.Configuration

namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy GeneralizedBulk.Gaussian GeneralizedBulk.Covariance GeneralizedBulk.KestenMcKay
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem coloredResolventCovarianceFactor_det_ne_zero {k : ℕ} (energy sigma : Fin k → ℝ) (eta : ℝ)
    (heta : 0 < eta) (hsigma : ∀ a,0 < sigma a) :
    (D.coloredResolventCovarianceFactor n ω energy eta sigma).det ≠ 0 := by
  rw [coloredResolventCovarianceFactor,colorBlock_det]
  exact Finset.prod_ne_zero_iff.mpr (fun a ha => D.resolventCovarianceFactor_det_ne_zero n ω _ _ _ heta (hsigma a))

theorem coloredResolventNoise_entropy_sum {k : ℕ} (energy sigma : Fin k → ℝ) (eta : ℝ)
    (heta : 0 < eta) (hsigma : ∀ a,0 < sigma a) :
    differentialEntropy (affineGaussianPDF 0 (D.coloredResolventCovarianceFactor n ω energy eta sigma))=
      ∑ a,-(∫ x,Real.log (linearGaussianPDF (D.resolventCovarianceFactor n ω (energy a) eta (sigma a)) x)
        ∂D.resolventNoise n ω (energy a) eta (sigma a)) := by
  rw [differentialEntropy_affineGaussianPDF _ _ (D.coloredResolventCovarianceFactor_det_ne_zero n ω energy sigma eta heta hsigma),
    D.coloredResolventCovariance_factor n ω energy eta sigma heta hsigma,coloredResolventCovariance,colorBlock_det,
    Real.log_prod _ _ (fun a ha => (D.resolventCovariance_posDef n ω _ _ _ heta (hsigma a)).det_pos.ne')]
  have hh (a : Fin k) : -(∫ x,Real.log (linearGaussianPDF (D.resolventCovarianceFactor n ω (energy a) eta (sigma a)) x)
      ∂D.resolventNoise n ω (energy a) eta (sigma a))=
      Real.log (D.resolventCovariance n ω (energy a) eta (sigma a)).det/2+
        (N n : ℝ)/2*(1+Real.log (2*Real.pi)) := by
    rw [resolventNoise,linearGaussian_differentialEntropy_covariance _
      (D.resolventCovarianceFactor_det_ne_zero n ω _ _ _ heta (hsigma a)),
      D.resolventCovariance_factor n ω _ _ _ heta (hsigma a)]
    simp only [Fintype.card_fin]
  simp_rw [hh]
  simp only [Finset.sum_add_distrib,Finset.sum_div,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul]
  ring

theorem HY_coloredResolventNoise_entropy_bulk_uniform {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ (d : ℝ)) (H : HYCoarseInput D P (D.kestenMcKayQuantile hd))
    (k : ℕ) (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) :
    ∃ eta0 : ℝ,0 < eta0 ∧ ∃ C : ℝ,0 < C ∧ ∀ n,H.events.threshold ≤ n → ∀ ω ∈ H.events.good n,
      ∀ energy sigma : Fin k → ℝ,(∀ a,energy a ∈ K) → (∀ a,0 < sigma a) →
      ∀ eta : ℝ,0 < eta → eta ≤ eta0 →
      |differentialEntropy (affineGaussianPDF 0 (D.coloredResolventCovarianceFactor n ω energy eta sigma))/(N n : ℝ)-
        ∑ a,((1/2 : ℝ)*(1+Real.log (2*Real.pi)+Real.log (eta/sigma a))-bulkPotential d (energy a))| ≤
        (k : ℝ)*((N n : ℝ)^(-H.rigidity_exponent)/eta+
          (|(d : ℝ)-radius d|+4*radius d)/((N n : ℝ)*eta)+C*eta) := by
  obtain ⟨eta0,he0,C,hC,hu⟩ := D.HY_resolventNoise_entropy_bulk_uniform hd H K hK hbulk
  refine ⟨eta0,he0,C,hC,?_⟩
  intro n hn ω hω energy sigma hE hsigma eta heta heta0
  rw [D.coloredResolventNoise_entropy_sum n ω energy sigma eta heta hsigma,Finset.sum_div,← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum
    (fun a (_ : a ∈ Finset.univ) => hu n hn ω hω (energy a) (hE a) eta (sigma a) heta heta0 (hsigma a))).trans_eq
      (by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]))

end GeneralizedBulk.External.RegularSpectralData
