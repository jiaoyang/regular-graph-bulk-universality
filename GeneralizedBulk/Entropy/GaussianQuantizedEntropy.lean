import GeneralizedBulk.Entropy.GaussianMixtureClipping
import GeneralizedBulk.Entropy.GaussianGridCovarianceBound

/-! Actual clipped quantizer entropy compared with differential entropy of
finite Gaussian mixtures, uniformly in the number of mixture components. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical NNReal

namespace GeneralizedBulk.Entropy
open Mehler

def gaussianClippingError (m : ℕ) (a H : ℝ) (c : ℝ≥0) (K : ℕ) : ℝ :=
  gridClippingLossConstant m a (H^2+(c : ℝ))*
    Real.sqrt (2*(m : ℝ)*Real.exp (-((K : ℝ)*a-H)^2/(2*(c : ℝ))))

def gaussianLocalGridError (m : ℕ) (a lo : ℝ) : ℝ := ((2 : ℝ)^m/2)*(m/lo)*m*a^2

theorem gaussianClippingError_nonneg (m : ℕ) (a H : ℝ) (c : ℝ≥0) (K : ℕ) :
    0 ≤ gaussianClippingError m a H c K :=
  mul_nonneg (gridClippingLossConstant_nonneg m a _) (Real.sqrt_nonneg _)

variable {S : Type*} [Fintype S]

set_option maxHeartbeats 1000000 in
theorem gaussianMixture_clipped_entropy_le_grid {m : ℕ}
    (weight : S → ℝ) (mean : S → Fin m → ℝ) (M : S → Matrix (Fin m) (Fin m) ℝ)
    (hw : ∀ s,0 ≤ weight s) (hsum : ∑ s,weight s = 1) (hdet : ∀ s,(M s).det ≠ 0)
    (a : ℝ) (ha : 0 < a) (K : ℕ) (hK : 0 < K) :
    Finite.entropy (lawMass (gaussianMixtureLaw weight mean M) (codedClipIntegerVector K hK ∘ gridLabel a)) ≤
      countableEntropy (gridMass a (gaussianMixturePDF weight mean M)) := by
  let μ := gaussianMixtureLaw weight mean M
  letI : IsProbabilityMeasure μ := gaussianMixtureLaw_probability weight mean M hw hsum hdet
  let p := gridMass a (gaussianMixturePDF weight mean M)
  have hp : ∀ j,0 ≤ p j := fun j => integral_nonneg (fun x => (gaussianMixturePDF_pos weight mean M hw hsum hdet x).le)
  have hs : HasSum p 1 := gridMass_hasSum a ha _ (integrable_gaussianMixturePDF weight mean M hdet)
    (integral_gaussianMixturePDF weight mean M hsum hdet)
  have hH := summable_grid_entropy a ha _ (measurable_gaussianMixturePDF weight mean M)
    (fun x => (gaussianMixturePDF_pos weight mean M hw hsum hdet x).le)
    (integrable_gaussianMixturePDF weight mean M hdet) (integral_gaussianMixturePDF weight mean M hsum hdet)
    (integrable_gaussianMixturePDF_mul_coordinateL1 weight mean M hdet)
  have hpush : countablePush p (codedClipIntegerVector K hK) =
      lawMass μ (codedClipIntegerVector K hK ∘ gridLabel a) := by
    change countablePush (gridMass a (gaussianMixturePDF weight mean M)) _ = _
    rw [← lawMass_gaussianMixture_gridLabel weight mean M hw hsum hdet a ha]
    funext j
    exact countablePush_lawMass μ (gridLabel a) (measurable_gridLabel a) _ j
  have h := countableEntropy_push_le p hp hs hH (codedClipIntegerVector K hK)
  rw [hpush] at h
  have he : countableEntropy (lawMass μ (codedClipIntegerVector K hK ∘ gridLabel a)) =
      Finite.entropy (lawMass μ (codedClipIntegerVector K hK ∘ gridLabel a)) := by
    rw [countableEntropy,tsum_fintype]
    rfl
  rwa [he] at h

theorem gaussianMixture_clipped_entropy_upper {m : ℕ}
    (weight : S → ℝ) (mean : S → Fin m → ℝ) (M : S → Matrix (Fin m) (Fin m) ℝ)
    (hw : ∀ s,0 ≤ weight s) (hsum : ∑ s,weight s = 1) (hdet : ∀ s,(M s).det ≠ 0)
    (lo : ℝ) (hlo : 0 < lo) (hcov : ∀ s (x : Fin m → ℝ),lo*(∑ i,x i^2) ≤ dotProduct x ((M s*(M s).transpose).mulVec x))
    (a : ℝ) (ha : 0 < a) (K : ℕ) (hK : 0 < K) :
    Finite.entropy (lawMass (gaussianMixtureLaw weight mean M) (codedClipIntegerVector K hK ∘ gridLabel a))+
      (m : ℝ)*Real.log a-differentialEntropy (gaussianMixturePDF weight mean M) ≤ gaussianLocalGridError m a lo := by
  have h := gaussianMixture_clipped_entropy_le_grid weight mean M hw hsum hdet a ha K hK
  have hg := (gaussianMixture_grid_error_of_covariance_lower weight mean M hw hsum hdet lo hlo hcov a ha).2
  unfold gaussianLocalGridError
  linarith

theorem gaussianMixture_clipped_entropy_lower {m : ℕ}
    (weight : S → ℝ) (mean : S → Fin m → ℝ) (M : S → Matrix (Fin m) (Fin m) ℝ)
    (hw : ∀ s,0 ≤ weight s) (hsum : ∑ s,weight s = 1) (hdet : ∀ s,(M s).det ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hmean : ∀ s i,|mean s i| ≤ H)
    (c : ℝ≥0) (hc : 0 < c) (hvar : ∀ s i,GeneralizedBulk.Gaussian.coordinateVariance (M s) i ≤ c)
    (a : ℝ) (ha : 0 < a) (K : ℕ) (hK : 0 < K) (hR : H ≤ (K : ℝ)*a) :
    -gaussianClippingError m a H c K ≤
      Finite.entropy (lawMass (gaussianMixtureLaw weight mean M) (codedClipIntegerVector K hK ∘ gridLabel a))+
        (m : ℝ)*Real.log a-differentialEntropy (gaussianMixturePDF weight mean M) := by
  have h := gaussianMixture_grid_clipping_loss weight mean M hw hsum hdet H hH hmean c hc hvar a ha K hK hR
  have hg := (gaussianMixture_unclipped_grid_entropy weight mean M hw hsum hdet a ha).1
  unfold gaussianClippingError
  linarith

end GeneralizedBulk.Entropy
