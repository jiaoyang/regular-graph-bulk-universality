import GeneralizedBulk.Entropy.UniformCovarianceRate
import GeneralizedBulk.Gaussian.CovarianceLaw
import GeneralizedBulk.Entropy.GaussianMixtureLaw

/-! Entropy depends on the actual covariance laws, rather than a chosen
square-root factor. This removes auxiliary factors from covariance stability. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Mehler
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

theorem differentialEntropy_eq_of_density_law (f g : (I → ℝ) → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hfp : ∀ x,0 ≤ f x) (hgp : ∀ x,0 ≤ g x)
    (hlaw : volume.withDensity (fun x => ENNReal.ofReal (f x)) =
      volume.withDensity (fun x => ENNReal.ofReal (g x))) : differentialEntropy f=differentialEntropy g := by
  have hh := (withDensity_eq_iff_of_sigmaFinite hf.ennreal_ofReal.aemeasurable
    hg.ennreal_ofReal.aemeasurable).mp hlaw
  unfold differentialEntropy
  congr 1
  apply integral_congr_ae
  filter_upwards [hh] with x hx
  rw [(ENNReal.ofReal_eq_ofReal_iff (hfp x) (hgp x)).mp hx]

theorem gaussianMixture_entropy_eq_of_covariance
    (weight : S → ℝ) (mean : S → I → ℝ) (M A : S → Matrix I I ℝ)
    (hw : ∀ s,0 ≤ weight s) (hnorm : ∑ s,weight s=1)
    (hM : ∀ s,(M s).det ≠ 0) (hA : ∀ s,(A s).det ≠ 0)
    (hcov : ∀ s,M s*(M s).transpose=A s*(A s).transpose) :
    differentialEntropy (gaussianMixturePDF weight mean M)=differentialEntropy (gaussianMixturePDF weight mean A) := by
  apply differentialEntropy_eq_of_density_law _ _ (measurable_gaussianMixturePDF _ _ _)
    (measurable_gaussianMixturePDF _ _ _)
    (fun x => (gaussianMixturePDF_pos _ _ _ hw hnorm hM x).le)
    (fun x => (gaussianMixturePDF_pos _ _ _ hw hnorm hA x).le)
  rw [← gaussianMixtureLaw_eq_withDensity weight mean M hw hM,
    ← gaussianMixtureLaw_eq_withDensity weight mean A hw hA]
  unfold gaussianMixtureLaw
  apply Finset.sum_congr rfl
  intro s hs
  rw [affineGaussian,affineGaussian,linearImageGaussian_eq_of_covariance (M s) (A s) (hcov s)]

theorem gaussianMixture_entropy_stability_of_covariance
    (weight : S → ℝ) (mean : S → I → ℝ) (A : S → Matrix I I ℝ)
    (hw : ∀ s,0 ≤ weight s) (hnorm : ∑ s,weight s=1) (hA : ∀ s,(A s).det ≠ 0)
    (hQ : ∀ s,(A s*(A s).transpose).PosDef)
    (M : Matrix I I ℝ) (hM : M.det ≠ 0) (kappa U : ℝ) (hkappa : 0 < kappa) (hU : 0 ≤ U)
    (hfloor : ∀ x : I → ℝ,kappa*(∑ i,x i^2) ≤ dotProduct x ((M*M.transpose).mulVec x))
    (htrace : Matrix.trace (M*M.transpose) ≤ U)
    (B e : ℝ) (hB : 0 ≤ B) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hsignal : ∀ s,coordinateL1 (mean s) ≤ B)
    (hclose : ∀ s i j,|(A s*(A s).transpose-M*M.transpose) i j| ≤ e)
    (hsmall : ((Fintype.card I : ℝ)^2/kappa)*e ≤ 1/2) :
    |differentialEntropy (gaussianMixturePDF weight mean A)-
      differentialEntropy (gaussianMixturePDF weight mean (fun _ => M))| ≤
      uniformCovarianceEntropyRateConstant I kappa U*(1+B^2)*e := by
  obtain ⟨F,hF,hEnt⟩ := exists_uniform_gaussianMixture_entropy_linear_rate weight mean
    (fun s => A s*(A s).transpose) hw hnorm hQ M hM kappa U hkappa hU hfloor htrace B e hB he he1 hsignal hclose hsmall
  rw [gaussianMixture_entropy_eq_of_covariance weight mean A F hw hnorm hA
    (fun s => (hF s).2) (fun s => (hF s).1.symm)]
  exact hEnt

end GeneralizedBulk.Entropy
