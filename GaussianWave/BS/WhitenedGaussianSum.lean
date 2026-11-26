import GaussianWave.BS.IndependentTreeSum
import GaussianWave.BS.JointGaussianProcessProperties
import GaussianWave.BS.PositiveRootWhitening

/-! Adding one actual independent Gaussian wave and whitening its strictly
positive root covariance preserves all ordinary process hypotheses. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

theorem gaussianSum_root_secondMoments {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av,Integrable (fun x => x av^2) μ) (energy : ℝ) (he : |energy|<(m+2 : ℝ)) :
    HasSecondMoments (rootChannelLaw (independentTreeSumLaw μ (jointGaussianTreeProcessLaw r m energy)))
      (positiveRootCovariance (treeRootCovariance μ)) := by
  rw [rootChannelLaw_independentTreeSum]
  apply independentAddLaw_secondMoments _ _ (rootChannelLaw_integrable_squareRadius μ hi)
    (rootChannelLaw_integrable_squareRadius _ (jointGaussianTreeProcessLaw_coordinate_integrable_square r m energy he))
    (jointGaussianTreeProcessLaw_root_mean_zero r m energy he) (treeRootCovariance μ) 1
  · intro a b
    exact rootChannelLaw_integral_product μ a b
  · intro a b
    simpa only [Matrix.one_apply] using jointGaussianTreeProcessLaw_root_identitySecondMoments r m energy he a b

def whitenedGaussianSumLaw {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hi : ∀ av,Integrable (fun x => x av^2) μ) (energy : ℝ) :=
  Measure.map (channelProcessMap (positiveRootWhitening (treeRootCovariance μ) (treeRootCovariance_posSemidef μ hi)))
    (independentTreeSumLaw μ (jointGaussianTreeProcessLaw r m energy))

instance whitenedGaussianSumLaw_probability {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av,Integrable (fun x => x av^2) μ) (energy : ℝ) :
    IsProbabilityMeasure (whitenedGaussianSumLaw μ hi energy) :=
  isProbabilityMeasure_map (continuous_channelProcessMap _).measurable.aemeasurable

theorem whitenedGaussianSumLaw_invariant {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av,Integrable (fun x => x av^2) μ) (energy : ℝ) (he : |energy|<(m+2 : ℝ))
    (hμ : ChannelTreeInvariant μ) : ChannelTreeInvariant (whitenedGaussianSumLaw μ hi energy) :=
  channelProcessMap_invariant _
    (independentTreeSumLaw_invariant _ _ hμ (jointGaussianTreeProcessLaw_invariant r m energy he)) _

theorem whitenedGaussianSumLaw_integrable_square {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av,Integrable (fun x => x av^2) μ) (energy : ℝ) (he : |energy|<(m+2 : ℝ))
    (av : Fin r × RegularTreeVertex (m+2)) :
    Integrable (fun x => x av^2) (whitenedGaussianSumLaw μ hi energy) :=
  channelProcessMap_integrable_sq _
    (independentTreeSumLaw_integrable_square _ _ hi
      (jointGaussianTreeProcessLaw_coordinate_integrable_square r m energy he)) _ av

theorem whitenedGaussianSumLaw_eigenrelations {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av,Integrable (fun x => x av^2) μ) (energy : ℝ) (he : |energy|<(m+2 : ℝ))
    (hE : ∀ a v,∀ᵐ x ∂μ,treeEigenResidual (m+2) r (fun _ => energy) a v x=0)
    (a : Fin r) (v : RegularTreeVertex (m+2)) :
    ∀ᵐ x ∂whitenedGaussianSumLaw μ hi energy,treeEigenResidual (m+2) r (fun _ => energy) a v x=0 := by
  apply channelProcessMap_eigenrelations
  apply ae_all_iff.mpr
  intro b
  apply ae_all_iff.mpr
  intro u
  exact independentTreeSumLaw_eigenrelations _ _ energy hE
    (jointGaussianTreeProcessLaw_eigenrelation r m energy he) b u

theorem whitenedGaussianSumLaw_root_identitySecondMoments {r m : ℕ}
    (μ : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure μ]
    (hi : ∀ av,Integrable (fun x => x av^2) μ) (energy : ℝ) (he : |energy|<(m+2 : ℝ)) :
    HasIdentitySecondMoments (rootChannelLaw (whitenedGaussianSumLaw μ hi energy)) := by
  rw [whitenedGaussianSumLaw,rootChannelLaw_channelProcessMap]
  have h2 := rootChannelLaw_integrable_squareRadius _
    (independentTreeSumLaw_integrable_square _ _ hi
      (jointGaussianTreeProcessLaw_coordinate_integrable_square r m energy he))
  exact positiveRootWhitening_identity_secondMoments _ h2 (treeRootCovariance μ)
    (treeRootCovariance_posSemidef μ hi) (gaussianSum_root_secondMoments μ hi energy he)

end GaussianWave.BS
